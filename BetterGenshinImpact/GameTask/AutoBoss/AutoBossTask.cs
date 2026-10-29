using BetterGenshinImpact.Core.BgiVision;
using BetterGenshinImpact.Core.Config;
using BetterGenshinImpact.Core.Recognition;
using BetterGenshinImpact.Core.Recognition.OCR;
using BetterGenshinImpact.Core.Recorder;
using BetterGenshinImpact.Core.Simulator;
using BetterGenshinImpact.Core.Simulator.Extensions;
using BetterGenshinImpact.GameTask.AutoFight;
using BetterGenshinImpact.GameTask.AutoFight.Model;
using BetterGenshinImpact.GameTask.AutoFight.Script;
using BetterGenshinImpact.GameTask.AutoGeniusInvokation.Exception;
using BetterGenshinImpact.GameTask.AutoPathing;
using BetterGenshinImpact.GameTask.AutoPathing.Model;
using BetterGenshinImpact.GameTask.AutoTrackPath;
using BetterGenshinImpact.GameTask.Common;
using BetterGenshinImpact.GameTask.Common.BgiVision;
using BetterGenshinImpact.GameTask.Common.Job;
using BetterGenshinImpact.GameTask.Common.Reward;
using BetterGenshinImpact.GameTask.Model.Area;
using BetterGenshinImpact.Helpers;
using BetterGenshinImpact.Service.Notification;
using Microsoft.Extensions.Logging;
using OpenCvSharp;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using Vanara.PInvoke;
using static BetterGenshinImpact.GameTask.Common.TaskControl;

namespace BetterGenshinImpact.GameTask.AutoBoss;

/// <summary>
/// 自动首领讨伐独立任务，负责按配置前往 Boss、执行战斗策略、领取征讨之花奖励并处理重定位。
/// </summary>
public class AutoBossTask : ISoloTask<Dictionary<string, int>>
{
    public string Name => "自动首领讨伐";

    private readonly ILogger<AutoBossTask> _logger = App.GetLogger<AutoBossTask>();
    private readonly AutoBossParam _taskParam;
    private readonly CombatScriptBag? _combatScriptBag;
    private readonly string? _jsonCombatStrategyPath;
    private readonly ReturnMainUiTask _returnMainUiTask = new();
    private readonly Dictionary<string, int> _rewardSummary = new();
    private SwitchPartyTask? _switchPartyTask;
    private CancellationToken _ct;
    private int _successfulRewardCount;

    private static readonly TimeSpan OriginalResinRecoveryInterval = TimeSpan.FromMinutes(8);
    private const int MaxQuickUseQuantity = 20;

    // ==================== 私服补充树脂（自定义修改）开始 ====================
    // 私服的树脂详情弹窗永远显示“原粹树脂已完全恢复”，战前预检会误判为树脂充足，从而永远不会补充。
    // 因此改为在征讨之花领奖界面兜底：按钮显示“补充原粹树脂”时，点击它 → 脆弱树脂 → 使用 →
    // 快捷使用界面把数量调到最大（20）→ 使用 → 点击“点击空白区域继续”，回到游戏主界面后再交互一次征讨之花领取奖励。
    // 下面几个开关改完需要重新编译。

    /// <summary>领奖界面出现“补充原粹树脂”时，是否自动用脆弱树脂补充并重新领取。</summary>
    private static readonly bool PrivateServerReplenishOnRewardPanel = true;

    /// <summary>每次补充使用的脆弱树脂数量（快捷使用界面单次最多 20 个）。</summary>
    private static readonly int PrivateServerFragileResinPerReplenish = 20;

    /// <summary>同一朵征讨之花最多补充几次，防止识别异常时无限消耗脆弱树脂。</summary>
    private static readonly int PrivateServerMaxReplenishPerReward = 2;

    /// <summary>是否跳过每轮开战前的大地图树脂预检（私服预检结果不可信，跳过可省去每轮开关地图的时间）。</summary>
    private static readonly bool PrivateServerSkipResinPreCheck = true;
    // ==================== 私服补充树脂（自定义修改）结束 ====================

    private string PathingAssetFolder => Global.Absolute(@"GameTask\AutoBoss\Assets\Pathing");

    private double AssetScale => TaskContext.Instance().SystemInfo.AssetScale;

    private static RecognitionObject LoadRecognitionObject(string objectName)
    {
        var captureRect = TaskContext.Instance().SystemInfo.ScaleMax1080PCaptureRect;
        return RecognitionAssets.Get("AutoBoss", objectName, captureRect.Width, captureRect.Height);
    }

    private sealed record OriginalResinInfo(int Count, int Limit);

    private sealed record SupplementalResinOption(string Name, RecognitionObject Template);

    /// <summary>
    /// 创建自动首领讨伐任务，并根据任务参数预解析战斗策略。
    /// </summary>
    /// <param name="taskParam">自动首领讨伐参数，包含 Boss、队伍、战斗策略、讨伐次数和补充树脂开关。</param>
    public AutoBossTask(AutoBossParam taskParam)
    {
        _taskParam = taskParam;
        if (string.IsNullOrWhiteSpace(_taskParam.CombatStrategyPath))
        {
            _taskParam.SetCombatStrategyPath(_taskParam.StrategyName);
        }

        if (_taskParam.CombatStrategyPath.EndsWith(".json", StringComparison.OrdinalIgnoreCase))
        {
            _jsonCombatStrategyPath = _taskParam.CombatStrategyPath;
            _logger.LogInformation("自动首领讨伐：检测到JSON策略文件，将使用JSON战斗引擎");
        }
        else
        {
            _combatScriptBag = CombatScriptParser.ReadAndParse(_taskParam.CombatStrategyPath);
        }
    }

    /// <summary>
    /// 启动自动首领讨伐任务，包含参数校验、分辨率校验、死亡重试和最终输入状态释放。
    /// </summary>
    /// <param name="ct">任务取消令牌。</param>
    Task ISoloTask.Start(CancellationToken ct) => Start(ct);

    public async Task<Dictionary<string, int>> Start(CancellationToken ct)
    {
        _ct = ct;
        _rewardSummary.Clear();
        _successfulRewardCount = 0;
        Validate();
        LogScreenResolution();

        Notify.Event("AutoBoss").Success($"{Name}启动");
        try
        {
            var retryCount = 0;
            while (true)
            {
                try
                {
                    await RunBossLoop();
                    break;
                }
                catch (RetryException e) when (retryCount < _taskParam.ReviveRetryCount)
                {
                    retryCount++;
                    _logger.LogWarning("{Name}：第 {Retry}/{MaxRetry} 次重试当前首领讨伐，原因：{Reason}", Name, retryCount, _taskParam.ReviveRetryCount, e.Message);
                    await Delay(2000, _ct);
                }
                catch (RetryException e)
                {
                    _logger.LogWarning("{Name}：角色死亡后重试次数已达上限 {MaxRetry}，结束任务，原因：{Reason}", Name, _taskParam.ReviveRetryCount, e.Message);
                    throw;
                }
            }
        }
        finally
        {
            Simulation.ReleaseAllKey();
            Simulation.SendInput.Mouse.LeftButtonUp();
            Notify.Event("AutoBoss").Success($"{Name}结束");
        }

        return new Dictionary<string, int>(_rewardSummary);
    }

    /// <summary>
    /// 执行完整讨伐循环：准备环境、前往首领、战斗、寻找奖励、领奖并决定是否继续下一轮。
    /// </summary>
    private async Task RunBossLoop()
    {
        // 1.切换队伍
        await Prepare();
        
        var shouldNavigateToBoss = true;
        //2.根据剩余次数判断是否继续
        while (ShouldContinueBeforeRound())
        {
            _ct.ThrowIfCancellationRequested();
            _logger.LogInformation("{Name}：开始第 {Round} 次讨伐 {Boss}", Name, _successfulRewardCount + 1, _taskParam.BossName);
            
            //3.树脂不足则退出
            if (!await EnsureResinBeforeRound())
            {
                _logger.LogInformation("{Name}：原粹树脂不足或补充失败，结束任务", Name);
                break;
            }
            
            //4.首次讨伐 or 回过七天神像 则需要重新寻路到首领
            if (shouldNavigateToBoss)
            {
                await NavigateToBoss();
            }
            
            //5.开始战斗
            await RunAutoFight();
            
            //6.寻路到征讨之花
            await NavigateToReward();
            
            //7.交互征讨之花
            var rewardSuccess = await TakeReward();
            if (!rewardSuccess)
            {
                _logger.LogInformation("{Name}：原粹树脂不足或无法领取奖励，结束任务", Name);
                break;
            }

            _successfulRewardCount++;
            _taskParam.RewardClaimedCallback?.Invoke();
            if (!ShouldContinueBeforeRound())
            {
                break;
            }
            
            if (_taskParam.ReturnToStatueAfterEachRound)
            {
                _logger.LogInformation("{Name}：返回七天神像", Name);
                await new TpTask(_ct).TpToStatueOfTheSeven();
                await Delay(3000, _ct);
                shouldNavigateToBoss = true;
            }
            else
            {
                // 就近回到首领附近继续讨伐
                await RepositionAfterFight();
                shouldNavigateToBoss = false;
            }
        }
    }

    /// <summary>
    /// 判断本轮开始前是否还有继续讨伐的次数。
    /// </summary>
    /// <returns>树脂耗尽模式始终返回 true；指定次数模式下未达到目标次数时返回 true。</returns>
    private bool ShouldContinueBeforeRound()
    {
        return !_taskParam.SpecifyRunCount || _successfulRewardCount < _taskParam.RunCount;
    }

    /// <summary>
    /// 战前预检原粹树脂是否足够领取一次世界 Boss 奖励；必要时尝试使用已开启的补充树脂入口。
    /// </summary>
    /// <returns>树脂足够或预检失败需要交由领奖弹窗兜底时返回 true；确认不足且无法补充时返回 false。</returns>
    private async Task<bool> EnsureResinBeforeRound()
    {
        if (PrivateServerSkipResinPreCheck)
        {
            // 私服：跳过战前预检，树脂不足时交给领奖界面的“补充原粹树脂”流程处理
            await _returnMainUiTask.Start(_ct);
            return true;
        }

        try
        {
            await _returnMainUiTask.Start(_ct);

            OriginalResinInfo originalResin;
            try
            {
                originalResin = await RecognizeOriginalResinInfoFromBigMap();
            }
            catch (Exception e) when (e is not OperationCanceledException)
            {
                _logger.LogWarning("{Name}：战前原粹树脂预检失败，将继续通过领奖界面兜底，原因：{Reason}", Name, e.Message);
                return true;
            }

            if (originalResin.Count >= 40)
            {
                return true;
            }

            _logger.LogInformation("{Name}：当前原粹树脂 {Count}/{Limit}，不足以领取首领奖励", Name, originalResin.Count, originalResin.Limit);
            if (!_taskParam.SpecifyRunCount)
            {
                return false;
            }

            if (!_taskParam.UseTransientResin && !_taskParam.UseFragileResin)
            {
                _logger.LogInformation("{Name}：指定讨伐次数模式未开启补充树脂，停止讨伐", Name);
                return false;
            }

            if (await TryUseSupplementalResinBeforeRound(originalResin))
            {
                return true;
            }

            _logger.LogInformation("{Name}：补充树脂未成功，停止讨伐", Name);
            return false;
        }
        finally
        {
            await _returnMainUiTask.Start(_ct);
        }
    }

    /// <summary>
    /// 打开大地图并通过树脂详情中的全部恢复时间反推当前原粹树脂。
    /// </summary>
    private async Task<OriginalResinInfo> RecognizeOriginalResinInfoFromBigMap()
    {
        var page = new BvPage(_ct);
        //树脂图标
        var resinIconLocator = page
            .Locator(LoadRecognitionObject("OriginalResinTopIcon"))
            .WithRoi(ScaleRect(1200, 25, 580, 50));
        
        await page.Flow()
            //按B打开地图直到识别到树脂图标
            .Do((Action)(() =>
            {
                if (!resinIconLocator.IsExist())
                {
                    Simulation.SendInput.SimulateAction(GIActions.OpenMap);
                }
            })).Until(resinIconLocator)
            //点击树脂图标直到识别到目标文本
            .Click().UntilAnyText(new[] { "全部恢复", "原粹树脂已完全恢复" }, ScaleRect(1180, 75, 620, 200))
            .Run();

        //根据树脂图标位置偏移，计算出体力恢复时间的弹窗位置
        var resinIconRegion = (await resinIconLocator.WaitFor()).First();
        var detailRect = new Rect(resinIconRegion.Left - 13, resinIconRegion.Bottom + 29, 220, 150);
        
        //根据弹窗位置 OCR 出当前树脂上限和全部恢复时间，反推当前原粹树脂
        using var clickedCapture = CaptureToRectArea();
        var resinLimit = RecognizeOriginalResinLimit(clickedCapture, resinIconRegion.Right);
        var fullRecoveryTime = RecognizeFullRecoveryTime(clickedCapture, detailRect);
        var missingResin = (int)Math.Ceiling(fullRecoveryTime.TotalSeconds / OriginalResinRecoveryInterval.TotalSeconds);
        if (missingResin > resinLimit)
        {
            throw new InvalidOperationException($"计算缺失树脂 {missingResin} 超过树脂上限 {resinLimit}");
        }

        var originalResin = new OriginalResinInfo(resinLimit - missingResin, resinLimit);
        _logger.LogInformation("{Name}：剩余树脂 {Count}", Name, originalResin.Count);
        return originalResin;
    }

    /// <summary>
    /// 按原右上角 OCR 区域读取当前/上限文本，并取数字串最后三位作为树脂上限。
    /// </summary>
    private int RecognizeOriginalResinLimit(ImageRegion capture, int resinIconRight)
    {
        var countRect = new Rect(resinIconRight + ScaleX(25), ScaleY(37), ScaleX(120), ScaleY(24));
        using var countRegion = capture.DeriveCrop(countRect);
        var countText = OcrFactory.Paddle.OcrWithoutDetector(countRegion.SrcMat);
        var digits = Regex.Replace(StringUtils.ConvertFullWidthNumToHalfWidth(countText), @"\D", "");
        if (digits.Length < 3)
        {
            throw new FormatException($"原粹树脂上限 OCR 失败：{countText}");
        }

        var limitText = digits[^3..];
        if (!int.TryParse(limitText, NumberStyles.None, CultureInfo.InvariantCulture, out var resinLimit) || resinLimit <= 0)
        {
            throw new FormatException($"原粹树脂上限解析失败：{countText}");
        }

        _logger.LogDebug("{Name}：原粹树脂上限 OCR：{Text} -> {Limit}", Name, countText, resinLimit);
        return resinLimit;
    }

    /// <summary>
    /// 读取树脂详情弹窗中的全部恢复时间；已完全恢复时返回零时长。
    /// </summary>
    private TimeSpan RecognizeFullRecoveryTime(ImageRegion capture, Rect detailRect)
    {
        using var detailRegion = capture.DeriveCrop(detailRect);
        var result = OcrFactory.Paddle.OcrResult(detailRegion.SrcMat);
        var text = string.Concat(result.Regions
            .OrderBy(region => region.Rect.Center.Y)
            .ThenBy(region => region.Rect.Center.X)
            .Select(region => region.Text));
        var normalizedText = NormalizeRecoveryText(text);
        _logger.LogDebug("{Name}：原粹树脂恢复详情 OCR：{Text}", Name, normalizedText);

        return ExtractFullRecoveryTime(normalizedText);
    }

    private static string NormalizeRecoveryText(string text)
    {
        if (string.IsNullOrWhiteSpace(text))
        {
            return string.Empty;
        }

        var normalized = StringUtils.ConvertFullWidthNumToHalfWidth(text).Replace('：', ':');
        return Regex.Replace(normalized, @"\s+", "");
    }

    private static TimeSpan ExtractFullRecoveryTime(string text)
    {
        if (text.Contains("原粹树脂已完全恢复", StringComparison.Ordinal))
        {
            return TimeSpan.Zero;
        }

        var fullRecoveryMatch = Regex.Match(text, @"全部恢复(?<time>\d{1,3}:\d{2}:\d{2})");
        if (fullRecoveryMatch.Success)
        {
            return ParseRecoveryTime(fullRecoveryMatch.Groups["time"].Value);
        }

        var timeMatches = Regex.Matches(text, @"\d{1,3}:\d{2}:\d{2}");
        if (timeMatches.Count == 0)
        {
            throw new FormatException($"未识别到全部恢复时间：{text}");
        }

        return ParseRecoveryTime(timeMatches[timeMatches.Count - 1].Value);
    }

    private static TimeSpan ParseRecoveryTime(string timeText)
    {
        var parts = timeText.Split(':');
        if (parts.Length != 3
            || !int.TryParse(parts[0], NumberStyles.None, CultureInfo.InvariantCulture, out var hours)
            || !int.TryParse(parts[1], NumberStyles.None, CultureInfo.InvariantCulture, out var minutes)
            || !int.TryParse(parts[2], NumberStyles.None, CultureInfo.InvariantCulture, out var seconds)
            || minutes < 0
            || minutes > 59
            || seconds < 0
            || seconds > 59)
        {
            throw new FormatException($"树脂恢复时间格式无效：{timeText}");
        }

        return new TimeSpan(hours, minutes, seconds);
    }

    private static string FormatRecoveryTime(TimeSpan time)
    {
        return $"{(int)time.TotalHours:D2}:{time.Minutes:D2}:{time.Seconds:D2}";
    }

    /// <summary>
    /// 当前处于大地图树脂详情弹窗时，尝试使用须臾或脆弱树脂补充原粹树脂。
    /// </summary>
    private async Task<bool> TryUseSupplementalResinBeforeRound(OriginalResinInfo originalResin)
    {
        var page = new BvPage(_ct);
        var currentResin = originalResin;
        var unavailableResins = new HashSet<string>(StringComparer.Ordinal);

        while (currentResin.Count < 40)
        {
            var targetQuantity = CalculateSupplementalResinTargetQuantity(currentResin);
            if (targetQuantity <= 0)
            {
                _logger.LogInformation("{Name}：当前原粹树脂 {Count}/{Limit}，使用任意补充树脂都会超过上限，停止补充", Name, currentResin.Count, currentResin.Limit);
                return false;
            }

            if (!await TryOpenResinSupplementPane(page))
            {
                return false;
            }

            var usedAnyResin = false;
            foreach (var resin in BuildSupplementalResinOptions())
            {
                if (unavailableResins.Contains(resin.Name))
                {
                    continue;
                }

                if (!await TrySelectSupplementalResin(page, resin))
                {
                    unavailableResins.Add(resin.Name);
                    continue;
                }

                var usedQuantity = await TryUseSelectedSupplementalResin(page, resin, targetQuantity);
                if (usedQuantity <= 0)
                {
                    return false;
                }

                usedAnyResin = true;
                _logger.LogInformation("{Name}：已使用 {Quantity} 个{ResinName}补充原粹树脂", Name, usedQuantity, resin.Name);
                await Delay(800, _ct);

                try
                {
                    currentResin = await RecognizeOriginalResinInfoFromBigMap();
                }
                catch (Exception e) when (e is not OperationCanceledException)
                {
                    _logger.LogWarning("{Name}：补充后重新识别原粹树脂失败，停止讨伐，原因：{Reason}", Name, e.Message);
                    return false;
                }

                _logger.LogInformation("{Name}：补充后原粹树脂 {Count}/{Limit}", Name, currentResin.Count, currentResin.Limit);
                if (currentResin.Count >= 40)
                {
                    return true;
                }

                break;
            }

            if (!usedAnyResin)
            {
                _logger.LogInformation("{Name}：未找到可用的须臾树脂或脆弱树脂", Name);
                return false;
            }
        }

        return true;
    }

    private List<SupplementalResinOption> BuildSupplementalResinOptions()
    {
        var options = new List<SupplementalResinOption>();
        if (_taskParam.UseTransientResin)
        {
            options.Add(new SupplementalResinOption("须臾树脂", LoadRecognitionObject("TransientResinInSupplementPane")));
        }

        if (_taskParam.UseFragileResin)
        {
            options.Add(new SupplementalResinOption("脆弱树脂", LoadRecognitionObject("FragileResinInSupplementPane")));
        }

        return options;
    }

    private static int CalculateSupplementalResinTargetQuantity(OriginalResinInfo originalResin)
    {
        return Math.Max(0, (originalResin.Limit - originalResin.Count) / 60);
    }

    private async Task<bool> TryOpenResinSupplementPane(BvPage page)
    {
        var titleRect = ScaleRect(834, 247, 256, 60);
        var titleLocator = page.Locator("补充原粹树脂", titleRect).WithRetryInterval(300);
        if ((await titleLocator.TryWaitFor(500)).Count > 0)
        {
            return true;
        }

        var openButtonLocator = page.Locator(LoadRecognitionObject("OpenResinSupplementPaneButton"))
            .WithRoi(ScaleRect(1200, 25, 580, 50))
            .WithRetryInterval(300);

        try
        {
            await titleLocator
                .WithRetryAction(_ =>
                {
                    var buttons = openButtonLocator.FindAll();
                    if (buttons.Count > 0)
                    {
                        buttons[0].Click();
                    }
                })
                .WaitFor(5000);
            return true;
        }
        catch (TimeoutException e)
        {
            _logger.LogWarning("{Name}：未能打开补充原粹树脂面板，原因：{Reason}", Name, e.Message);
            return false;
        }
    }

    private async Task<bool> TrySelectSupplementalResin(BvPage page, SupplementalResinOption resin)
    {
        var iconLocator = page.Locator(resin.Template)
            .WithRoi(ScaleRect(644, 378, 620, 192))
            .WithRetryInterval(300);

        var icons = await iconLocator.TryWaitFor(1500);
        if (icons.Count == 0)
        {
            _logger.LogInformation("{Name}：补充面板未找到{ResinName}图标，视为不可用", Name, resin.Name);
            return false;
        }

        icons[0].Click();
        try
        {
            await page.Locator(resin.Name, ScaleRect(906, 587, 110, 31))
                .WithRetryInterval(300)
                .WithRetryAction(_ =>
                {
                    var currentIcons = iconLocator.FindAll();
                    if (currentIcons.Count > 0)
                    {
                        currentIcons[0].Click();
                    }
                })
                .WaitFor(3000);
            return true;
        }
        catch (TimeoutException e)
        {
            _logger.LogWarning("{Name}：未能确认已选中{ResinName}，原因：{Reason}", Name, resin.Name, e.Message);
            return false;
        }
    }

    private async Task<int> TryUseSelectedSupplementalResin(BvPage page, SupplementalResinOption resin, int targetQuantity)
    {
        if (targetQuantity <= 0)
        {
            return 0;
        }

        if (!await TryClickTextButton(page, "使用", ScaleRect(1163, 761, 61, 38), 3000))
        {
            return 0;
        }

        await Delay(500, _ct);
        var quickUseRegions = await page.Locator("快捷使用", ScaleRect(875, 269, 184, 63)).TryWaitFor(1500);
        if (quickUseRegions.Count > 0)
        {
            return await TryUseQuickSupplementalResin(page, resin, targetQuantity);
        }

        if (await TryCloseSupplementObtainDialog(page))
        {
            return 1;
        }

        _logger.LogWarning("{Name}：点击{ResinName}使用后未识别到快捷使用或获得界面", Name, resin.Name);
        return 0;
    }

    /// <summary>
    /// 在快捷使用面板中按目标数量使用补充树脂，最多一次使用 <see cref="MaxQuickUseQuantity"/> 个。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <param name="resin">待使用的补充树脂选项。</param>
    /// <param name="targetQuantity">本轮希望使用的树脂数量。</param>
    /// <returns>成功使用的数量；失败或无法识别时返回 0。</returns>
    private async Task<int> TryUseQuickSupplementalResin(BvPage page, SupplementalResinOption resin, int targetQuantity)
    {
        var availableQuantity = RecognizeQuickUseAvailableCount();
        var targetQuickQuantity = Math.Min(Math.Min(targetQuantity, availableQuantity), MaxQuickUseQuantity);
        if (targetQuickQuantity <= 0)
        {
            _logger.LogWarning("{Name}：快捷使用面板未识别到{ResinName}可用数量", Name, resin.Name);
            return 0;
        }

        var actualQuantity = await AdjustQuickUseQuantity(page, targetQuickQuantity);
        if (actualQuantity <= 0 || actualQuantity > targetQuickQuantity)
        {
            _logger.LogWarning("{Name}：快捷使用{ResinName}数量无效，目标 {TargetQuantity}，识别 {ActualQuantity}", Name, resin.Name, targetQuickQuantity, actualQuantity);
            return 0;
        }

        if (!await TryClickTextButton(page, "使用", ScaleRect(1152, 740, 64, 35), 3000))
        {
            return 0;
        }

        if (!await TryCloseSupplementObtainDialog(page))
        {
            return 0;
        }

        return actualQuantity;
    }

    /// <summary>
    /// 识别快捷使用面板中的可用数量，并限制到单次快捷使用上限。
    /// </summary>
    /// <returns>可用于本次快捷使用的数量，上限为 <see cref="MaxQuickUseQuantity"/>。</returns>
    private int RecognizeQuickUseAvailableCount()
    {
        var text = NormalizeSupplementText(RecognizeTextWithoutDetector(ScaleRect(1191, 633, 72, 29)));
        var matches = Regex.Matches(text, @"\d+");
        var maxValue = 0;
        foreach (Match match in matches)
        {
            if (int.TryParse(match.Value, NumberStyles.None, CultureInfo.InvariantCulture, out var value))
            {
                maxValue = Math.Max(maxValue, value);
            }
        }

        var availableQuantity = Math.Min(maxValue, MaxQuickUseQuantity);
        _logger.LogDebug("{Name}：快捷使用可用数量 OCR：{Text} -> {Quantity}", Name, text, availableQuantity);
        return availableQuantity;
    }

    /// <summary>
    /// 通过点击加号把快捷使用数量调整到目标值，无法继续增加时返回当前识别数量。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <param name="targetQuantity">目标快捷使用数量。</param>
    /// <returns>最终识别到的快捷使用数量。</returns>
    private async Task<int> AdjustQuickUseQuantity(BvPage page, int targetQuantity)
    {
        var increaseLocator = page.Locator(LoadRecognitionObject("IncreaseResinUsageQuantityButton"))
            .WithRoi(ScaleRect(1265, 620, 59, 55))
            .WithRetryInterval(500);

        var actualQuantity = 0;
        var lastQuantity = -1;
        var unchangedTimes = 0;
        var retryTimes = Math.Max(6, targetQuantity * 3);
        var completed = await NewRetry.WaitForAction(() =>
        {
            var quantity = TryRecognizeQuickUseQuantity();
            if (quantity == null)
            {
                return false;
            }

            actualQuantity = quantity.Value;
            if (actualQuantity >= targetQuantity)
            {
                return true;
            }

            if (actualQuantity == lastQuantity)
            {
                unchangedTimes++;
            }
            else
            {
                unchangedTimes = 0;
            }

            lastQuantity = actualQuantity;
            if (unchangedTimes >= 3)
            {
                return true;
            }

            var increaseButtons = increaseLocator.FindAll();
            if (increaseButtons.Count == 0)
            {
                return true;
            }

            increaseButtons[0].Click();
            return false;
        }, _ct, retryTimes, 500);

        if (!completed)
        {
            _logger.LogDebug("{Name}：快捷使用数量调整超时，目标 {TargetQuantity}，当前 {ActualQuantity}", Name, targetQuantity, actualQuantity);
        }

        return actualQuantity;
    }

    /// <summary>
    /// 从快捷使用面板 OCR 文本中解析当前使用数量。
    /// </summary>
    /// <returns>成功解析时返回当前数量；文本不完整或解析失败时返回 null。</returns>
    private int? TryRecognizeQuickUseQuantity()
    {
        var text = NormalizeSupplementText(RecognizeSortedOcrText(ScaleRect(915, 540, 93, 81)));
        if (!text.Contains("使用数量", StringComparison.Ordinal))
        {
            _logger.LogDebug("{Name}：快捷使用数量 OCR 未包含使用数量：{Text}", Name, text);
            return null;
        }

        var match = Regex.Match(text, @"使用数量\D*(\d+)");
        if (!match.Success)
        {
            match = Regex.Match(text, @"\d+");
        }

        var quantityText = match.Groups.Count > 1 && match.Groups[1].Success ? match.Groups[1].Value : match.Value;
        if (!match.Success || !int.TryParse(quantityText, NumberStyles.None, CultureInfo.InvariantCulture, out var quantity))
        {
            _logger.LogDebug("{Name}：快捷使用数量 OCR 解析失败：{Text}", Name, text);
            return null;
        }

        _logger.LogDebug("{Name}：快捷使用数量 OCR：{Text} -> {Quantity}", Name, text, quantity);
        return quantity;
    }

    private async Task<bool> TryCloseSupplementObtainDialog(BvPage page)
    {
        try
        {
            var obtainRegion = (await page.Locator("获得", ScaleRect(924, 279, 74, 38)).WaitFor(5000)).First();
            obtainRegion.Click();
            await Delay(800, _ct);
            return true;
        }
        catch (TimeoutException e)
        {
            _logger.LogWarning("{Name}：未识别到补充树脂获得界面，原因：{Reason}", Name, e.Message);
            return false;
        }
    }

    private async Task<bool> TryClickTextButton(BvPage page, string text, Rect rect, int timeout)
    {
        try
        {
            await page.Locator(text, rect).Click(timeout);
            return true;
        }
        catch (TimeoutException e)
        {
            _logger.LogWarning("{Name}：未能点击文本按钮 {Text}，原因：{Reason}", Name, text, e.Message);
            return false;
        }
    }

    private string RecognizeTextWithoutDetector(Rect rect)
    {
        using var capture = CaptureToRectArea();
        using var region = capture.DeriveCrop(rect);
        return OcrFactory.Paddle.OcrWithoutDetector(region.SrcMat);
    }

    private string RecognizeSortedOcrText(Rect rect)
    {
        using var capture = CaptureToRectArea();
        using var region = capture.DeriveCrop(rect);
        var result = OcrFactory.Paddle.OcrResult(region.SrcMat);
        return string.Concat(result.Regions
            .OrderBy(r => r.Rect.Center.Y)
            .ThenBy(r => r.Rect.Center.X)
            .Select(r => r.Text));
    }

    private static string NormalizeSupplementText(string text)
    {
        if (string.IsNullOrWhiteSpace(text))
        {
            return string.Empty;
        }

        var normalized = StringUtils.ConvertFullWidthNumToHalfWidth(text)
            .Replace('：', ':')
            .Replace('﹕', ':');
        return Regex.Replace(normalized, @"\s+", "");
    }

    /// <summary>
    /// 根据当前队伍匹配战斗脚本，并切换到脚本中的首个角色。
    /// </summary>
    /// <param name="combatScenes">已初始化的战斗场景。</param>
    /// <returns>匹配到的战斗指令列表。</returns>
    /// <exception cref="Exception">没有可用战斗脚本时抛出。</exception>
    private List<CombatCommand> FindCombatScriptAndSwitchAvatar(CombatScenes combatScenes)
    {
        var combatCommands = _combatScriptBag.FindCombatScript(combatScenes.GetAvatars());
        if (combatCommands.Count == 0)
        {
            throw new Exception("没有可用战斗脚本");
        }

        var avatar = combatScenes.SelectAvatar(combatCommands[0].Name);
        avatar?.SwitchWithoutCts();
        Sleep(200, _ct);
        return combatCommands;
    }

    /// <summary>
    /// 使用所选自动战斗策略执行首领战斗，并复用自动战斗的结束检测。
    /// </summary>
    private async Task RunAutoFight()
    {
        _logger.LogInformation("{Name}：执行战斗策略", Name);

        if (_jsonCombatStrategyPath != null)
        {
            await StartJsonFight();
        }
        else
        {
            var combatScenes = CombatScenes.GetCombatScenesWithRetry();
            FindCombatScriptAndSwitchAvatar(combatScenes);

            var taskParam = BuildAutoFightParamForBoss();
            try
            {
                await new AutoFightTask(taskParam).Start(_ct);
            }
            catch (NormalEndException e)
            {
                _logger.LogInformation("战斗操作中断：{Msg}", e.Message);
            }
            finally
            {
                combatScenes.AfterTask();
            }
        }
    }

    /// <summary>
    /// JSON策略战斗入口：委托给AutoFightJsonTask，由其自身处理战斗结束检测，
    /// 抑制战后拾取逻辑。
    /// </summary>
    private async Task StartJsonFight()
    {
        CancellationTokenSource cts = new();
        _ct.Register(cts.Cancel);

        var jsonParam = new AutoFightParam
        {
            CombatStrategyPath = _jsonCombatStrategyPath!,
            FightFinishDetectEnabled = true,
            ExpBasedPickupEnabled = false,
            KazuhaPickupEnabled = false,
            PickDropsAfterFightEnabled = false,
            Timeout = _taskParam.Timeout,
        };

        var jsonTask = new AutoFightJsonTask(jsonParam);

        try
        {
            await jsonTask.Start(cts.Token);
        }
        catch (NormalEndException e)
        {
            _logger.LogInformation("战斗操作中断：{Msg}", e.Message);
        }
        catch (Exception e)
        {
            _logger.LogWarning("JSON战斗任务异常：{Msg}", e.Message);
        }
    }

    /// <summary>
    /// 构造 AutoBoss 专用自动战斗参数：复用战斗检测配置，但不执行任何战后拾取。
    /// </summary>
    private AutoFightParam BuildAutoFightParamForBoss()
    {
        var taskParam = new AutoFightParam(_taskParam.CombatStrategyPath, TaskContext.Instance().Config.AutoFightConfig)
        {
            FightFinishDetectEnabled = true,
            PickDropsAfterFightEnabled = false,
            KazuhaPickupEnabled = false,
            QinDoublePickUp = false,
            ExpBasedPickupEnabled = false,
            KazuhaPartyName = string.Empty,
            BattleThresholdForLoot = -1,
            OnlyPickEliteDropsMode = "DisableAutoPickupForNonElite",
            Timeout = _taskParam.Timeout
        };
        return taskParam;
    }

    /// <summary>
    /// 校验自动首领讨伐启动所需的 Boss、战斗策略、讨伐次数、补充树脂开关、重试次数和路线文件。
    /// </summary>
    /// <exception cref="Exception">配置缺失、Boss 不支持、策略不存在或重试次数非法时抛出。</exception>
    /// <exception cref="FileNotFoundException">必需路线文件不存在时抛出。</exception>
    private void Validate()
    {
        if (string.IsNullOrWhiteSpace(_taskParam.BossName))
        {
            throw new Exception("请选择需要讨伐的首领");
        }

        if (!AutoBossData.IsSupportedBoss(_taskParam.BossName))
        {
            throw new Exception($"暂不支持首领：{_taskParam.BossName}");
        }

        if (_taskParam.ReviveRetryCount < 0)
        {
            throw new Exception("角色死亡后重试次数不能小于 0");
        }

        if (_taskParam.SpecifyRunCount && _taskParam.RunCount < 1)
        {
            throw new Exception("指定讨伐次数必须大于 0");
        }

        if (!_taskParam.SpecifyRunCount && (_taskParam.UseTransientResin || _taskParam.UseFragileResin))
        {
            throw new Exception("只有指定讨伐次数模式才能开启须臾树脂或脆弱树脂补充");
        }

        if (string.IsNullOrWhiteSpace(_taskParam.CombatStrategyPath))
        {
            _taskParam.SetCombatStrategyPath(_taskParam.StrategyName);
        }

        if (!File.Exists(_taskParam.CombatStrategyPath) && !Directory.Exists(_taskParam.CombatStrategyPath))
        {
            throw new Exception("当前选择的自动战斗策略文件不存在");
        }

        foreach (var route in GetRequiredRouteFiles(_taskParam.BossName))
        {
            if (!File.Exists(BuildPathingAssetPath(route)))
            {
                throw new FileNotFoundException($"未找到首领路线文件：{route}", BuildPathingAssetPath(route));
            }
        }
    }

    /// <summary>
    /// 获取指定 Boss 启动任务前必须存在的路线文件名。
    /// </summary>
    /// <param name="bossName">Boss 名称。</param>
    /// <returns>需要校验的路线文件名序列。</returns>
    private static IEnumerable<string> GetRequiredRouteFiles(string bossName)
    {
        if (AutoBossData.IsNoPathingSupportBoss(bossName))
        {
            yield return $"{bossName}强制传送.json";
            yield return $"{bossName}键鼠前往.json";
            yield break;
        }

        yield return $"{bossName}前往.json";

        if (AutoBossData.IsTalkToStartBoss(bossName))
        {
            yield return $"{bossName}战斗后快速前往.json";
        }
    }

    /// <summary>
    /// 校验当前游戏窗口是否满足自动首领讨伐所需的 16:9 分辨率。
    /// </summary>
    /// <exception cref="Exception">游戏窗口不是 16:9 时抛出。</exception>
    private void LogScreenResolution()
    {
        var gameScreenSize = SystemControl.GetGameScreenRect(TaskContext.Instance().GameHandle);
        if (gameScreenSize.Width * 9 != gameScreenSize.Height * 16)
        {
            _logger.LogError("游戏窗口分辨率不是 16:9 ！当前分辨率为 {Width}x{Height}", gameScreenSize.Width, gameScreenSize.Height);
            throw new Exception("游戏窗口分辨率不是 16:9");
        }

        if (gameScreenSize.Width < 1920 || gameScreenSize.Height < 1080)
        {
            Logger.LogWarning("游戏窗口分辨率小于 1920x1080 ！当前分辨率为 {Width}x{Height} , 小于 1920x1080 的分辨率的游戏可能无法正常使用自动首领功能 !",
                gameScreenSize.Width, gameScreenSize.Height);
        }
    }

    /// <summary>
    /// 回到主界面并按配置尝试切换到指定队伍。
    /// </summary>
    private async Task Prepare()
    {
        await _returnMainUiTask.Start(_ct);

        if (string.IsNullOrWhiteSpace(_taskParam.TeamName))
        {
            return;
        }

        _logger.LogInformation("{Name}：切换队伍 {TeamName}", Name, _taskParam.TeamName);
        _switchPartyTask ??= new SwitchPartyTask();
        var success = await _switchPartyTask.Start(_taskParam.TeamName, _ct);
        if (!success)
        {
            throw new InvalidOperationException($"切换队伍失败：{_taskParam.TeamName}");
        }
    }

    /// <summary>
    /// 按 Boss 类型执行前往路线，特殊 Boss 使用强制传送加键鼠宏路线。
    /// </summary>
    private async Task NavigateToBoss()
    {
        _logger.LogInformation("{Name}：前往 {Boss}", Name, _taskParam.BossName);
        if (AutoBossData.IsNoPathingSupportBoss(_taskParam.BossName))
        {
            await RunPathingFile($"{_taskParam.BossName}强制传送.json");
            await RunKeyMouseFile($"{_taskParam.BossName}键鼠前往.json");
            return;
        }

        await RunPathingFile($"{_taskParam.BossName}前往.json");
    }

    /// <summary>
    /// 加载并执行 AutoBoss 资产目录中的寻路 JSON 文件。
    /// </summary>
    /// <param name="fileName">路线文件名。</param>
    private async Task RunPathingFile(string fileName)
    {
        await _returnMainUiTask.Start(_ct);
        var task = PathingTask.BuildFromFilePath(BuildPathingAssetPath(fileName)) ?? throw new Exception($"路径文件解析失败：{fileName}");
        await RunPathingTask(task);
    }

    /// <summary>
    /// 使用自动首领讨伐的队伍配置执行寻路任务。
    /// </summary>
    /// <param name="task">已经解析好的寻路任务。</param>
    private async Task RunPathingTask(PathingTask task)
    {
        var executor = new PathExecutor(_ct)
        {
            PartyConfig = BuildPathingPartyConfig()
        };
        await executor.Pathing(task);
    }

    /// <summary>
    /// 构建首领路线执行时使用的队伍配置，禁止寻路过程自动切队和自动战斗。
    /// </summary>
    /// <returns>寻路任务队伍配置。</returns>
    private static PathingPartyConfig BuildPathingPartyConfig()
    {
        var partyConfig = PathingPartyConfig.BuildDefault();
        partyConfig.SkipPartySwitch = true;
        partyConfig.AutoFightEnabled = false;
        return partyConfig;
    }

    /// <summary>
    /// 执行 AutoBoss 资产目录中的键鼠宏路线文件。
    /// </summary>
    /// <param name="fileName">键鼠宏文件名。</param>
    private async Task RunKeyMouseFile(string fileName)
    {
        await _returnMainUiTask.Start(_ct);
        var json = await File.ReadAllTextAsync(BuildPathingAssetPath(fileName), _ct);
        await KeyMouseMacroPlayer.PlayMacro(json, _ct, false);
    }

    /// <summary>
    /// 拼接 AutoBoss 路线资产的绝对路径。
    /// </summary>
    /// <param name="fileName">路线或键鼠宏文件名。</param>
    /// <returns>资源文件绝对路径。</returns>
    private string BuildPathingAssetPath(string fileName)
    {
        return Path.Combine(PathingAssetFolder, fileName);
    }

    /// <summary>
    /// 战斗结束后通过模板和 OCR 寻找“接触征讨之花”，并控制角色移动到可交互范围。
    /// </summary>
    /// <exception cref="TimeoutException">长时间无法找到或靠近征讨之花时抛出。</exception>
    private async Task NavigateToReward()
    {
        using var navigationCts = CancellationTokenSource.CreateLinkedTokenSource(_ct);
        var page = new BvPage(navigationCts.Token);

        _logger.LogInformation("{Name}：开始寻找征讨之花", Name);

        var navigationStopwatch = Stopwatch.StartNew();
        var navigationTimeout = TimeSpan.FromSeconds(20);
        var adjustCameraTask = AdjustRewardCameraTask(page, navigationCts);
        var moveToRewardTask = MoveToRewardTask(page, navigationCts);
        var monitorRewardPromptTask = MonitorRewardPromptTask(page, navigationCts);

        try
        {
            while (true)
            {
                _ct.ThrowIfCancellationRequested();
                if (navigationStopwatch.Elapsed >= navigationTimeout)
                {
                    throw new TimeoutException("超时未找到征讨之花领奖界面");
                }

                var completedTask = await Task.WhenAny(Task.Delay(500, _ct),adjustCameraTask,moveToRewardTask,monitorRewardPromptTask);

                if (completedTask == monitorRewardPromptTask)
                {
                    await monitorRewardPromptTask;
                    _logger.LogInformation("{Name}：已进入征讨之花领奖界面", Name);
                    return;
                }

                if (completedTask == adjustCameraTask || completedTask == moveToRewardTask)
                {
                    navigationCts.Cancel();
                    await completedTask;
                    throw new TimeoutException("前往征讨之花任务异常结束");
                }
            }
        }
        finally
        {
            navigationCts.Cancel();
            try
            {
                await Task.WhenAll(adjustCameraTask, moveToRewardTask, monitorRewardPromptTask);
            }
            catch
            {
                // The main loop observes task failures; shutdown also cancels background tasks.
            }

            Simulation.SendInput.SimulateAction(GIActions.MoveForward, KeyType.KeyUp);
            Simulation.SendInput.SimulateAction(GIActions.MoveLeft, KeyType.KeyUp);
            Simulation.SendInput.SimulateAction(GIActions.MoveRight, KeyType.KeyUp);
        }
    }

    private bool HasRewardInteractionPrompt(BvPage page)
    {
        var rewardRect = ScaleRect(1210, 300, 200, 400);
        return page.Ocr(rewardRect).Any(region => region.Text.Contains("接触征讨之花", StringComparison.Ordinal));
    }

    private bool HasRewardPanelPrompt(BvPage page)
    {
        var rewardPanelRect = ScaleRect(850, 740, 250, 35);
        return page.Ocr(rewardPanelRect).Any(region =>
            region.Text.Contains("使用原粹树脂", StringComparison.Ordinal)
            || region.Text.Contains("补充原粹树脂", StringComparison.Ordinal));
    }

    private async Task MonitorRewardPromptTask(BvPage page, CancellationTokenSource navigationCts)
    {
        var ct = navigationCts.Token;
        var lastInteractAt = DateTime.MinValue;

        while (!ct.IsCancellationRequested)
        {
            ct.ThrowIfCancellationRequested();

            if (HasRewardPanelPrompt(page))
            {
                return;
            }

            if (HasRewardInteractionPrompt(page))
            {
                if (DateTime.UtcNow - lastInteractAt >= TimeSpan.FromMilliseconds(300))
                {
                    Simulation.SendInput.SimulateAction(GIActions.PickUpOrInteract);
                    lastInteractAt = DateTime.UtcNow;
                }
            }

            await Delay(300, ct);
        }
    }

    private async Task AdjustRewardCameraTask(BvPage page, CancellationTokenSource navigationCts)
    {
        var ct = navigationCts.Token;
        var captureRect = TaskContext.Instance().SystemInfo.ScaleMax1080PCaptureRect;
        //将图标控制在屏幕中间，大约截图宽度的45%-55%之间
        var minTargetX = captureRect.Width * 0.45;
        var maxTargetX = captureRect.Width * 0.55;
        var centerX = captureRect.Width / 2.0;
        var halfHeight = captureRect.Height / 2.0;

        while (!ct.IsCancellationRequested)
        {
            ct.ThrowIfCancellationRequested();
            var boxRegions = page.Locator(LoadRecognitionObject("RewardBox")).FindAll();
            if (boxRegions.Count < 1)
            {
                _logger.LogWarning("{Name}：未找到征讨之花图标，调整视角重试", Name);
                Simulation.SendInput.Mouse.MoveMouseBy(ScaleX(200), 0);
                await Delay(250, ct);
                continue;
            }

            var icon = boxRegions[0];

            if (icon.Y > halfHeight)
            {
                Simulation.SendInput.Mouse.MoveMouseBy(0, (int)Math.Round(halfHeight));
                await Delay(125, ct);
                Simulation.SendInput.Mouse.MoveMouseBy((int)Math.Round(centerX), 0);
                await Delay(125, ct);
                continue;
            }

            if (icon.X < minTargetX || icon.X > maxTargetX)
            {
                Simulation.SendInput.Mouse.MoveMouseBy((int)Math.Round(icon.X - centerX), 0);
            }

            await Delay(250, ct);
        }
    }

    private async Task MoveToRewardTask(BvPage page, CancellationTokenSource navigationCts)
    {
        var ct = navigationCts.Token;
        var climbRect = ScaleRect(1686, 1030, 60, 23);
        var jumpCount = 0;
        var isMovingForward = false;

        try
        {
            while (!ct.IsCancellationRequested)
            {
                ct.ThrowIfCancellationRequested();
                if (page.Locator("Space", climbRect).IsExist())
                {
                    if (isMovingForward)
                    {
                        Simulation.SendInput.SimulateAction(GIActions.MoveForward, KeyType.KeyUp);
                        isMovingForward = false;
                    }

                    _logger.LogInformation("{Name}：检测到攀爬状态，尝试脱离", Name);
                    Simulation.SendInput.SimulateAction(GIActions.Drop);
                    await Delay(1000, ct);
                    Simulation.SendInput.SimulateAction(GIActions.MoveLeft, KeyType.KeyDown);
                    await Delay(800, ct);
                    Simulation.SendInput.SimulateAction(GIActions.MoveLeft, KeyType.KeyUp);
                    continue;
                }

                if (!isMovingForward)
                {
                    Simulation.SendInput.SimulateAction(GIActions.MoveForward, KeyType.KeyDown);
                    isMovingForward = true;
                }

                await Delay(1000, ct);
                jumpCount++;
                if (jumpCount % 2 == 0)
                {
                    Simulation.SendInput.SimulateAction(GIActions.Jump);
                    await Delay(100, ct);
                }

                Simulation.SendInput.SimulateAction(GIActions.MoveForward, KeyType.KeyUp);
                isMovingForward = false;
                await Delay(200, ct);
            }
        }
        finally
        {
            Simulation.SendInput.SimulateAction(GIActions.MoveForward, KeyType.KeyUp);
            Simulation.SendInput.SimulateAction(GIActions.MoveLeft, KeyType.KeyUp);
        }
    }

    /// <summary>
    /// 与征讨之花交互，并在世界 Boss 专用领奖界面点击“使用原粹树脂”领取奖励。
    /// </summary>
    /// <returns>成功领取奖励并回到主界面时返回 true；原粹树脂不足或无法领取时返回 false。</returns>
    private async Task<bool> TakeReward()
    {
        var page = new BvPage(_ct);
        var replenishCount = 0;

        while (!await TryUseOriginalResinOnRewardPrompt(page))
        {
            // 私服：原有识别区域较窄，2K 等分辨率下可能认不全“使用原粹树脂”，用较宽的区域再试一次
            if (PrivateServerReplenishOnRewardPanel && await TryClickUseOriginalResinWide(page))
            {
                break;
            }

            // 私服补充：领奖按钮显示“补充原粹树脂”时，点击补充 → 脆弱树脂 → 使用 20 个 → 回到游戏主界面 → 重新交互征讨之花
            if (PrivateServerReplenishOnRewardPanel
                && replenishCount < PrivateServerMaxReplenishPerReward
                && HasReplenishButtonOnRewardPanel(page))
            {
                replenishCount++;
                if (await TryReplenishOnRewardPanelAndReinteract(page, replenishCount))
                {
                    // 已重新打开领奖界面，回到循环开头再次点击“使用原粹树脂”
                    continue;
                }
            }

            await CloseResinSupplementPrompt(page);
            await _returnMainUiTask.Start(_ct);
            return false;
        }

        await TryRecognizeRewardResult(page);
        await CloseRewardResult();
        Notify.Event("AutoBoss").Success($"{Name}奖励领取");
        return true;
    }

    private async Task TryRecognizeRewardResult(BvPage page)
    {
        if (!_taskParam.RewardRecognitionEnabled)
        {
            return;
        }

        try
        {
            if (!await WaitForRewardResultReady(page))
            {
                _logger.LogWarning("{Name}：奖励结果页未检测到“点击空白区域继续”，已跳过本轮奖励识别", Name);
                return;
            }

            // 使用多页识别（自动检测是否需要翻页）
            _logger.LogInformation("{Name}：开始奖励识别", Name);
            var rewards = RewardResultRecognizer.Instance.RecognizeMultiPage();

            RewardResultRecognizer.MergeIntoSummary(_rewardSummary, rewards);

            if (rewards.Count > 0)
            {
                _logger.LogInformation("{Name}：本轮奖励识别结果 {Rewards}", Name,
                    string.Join(", ", rewards.Select(r => $"{r.Key} x{r.Value}")));
            }
            else
            {
                _logger.LogWarning("{Name}：本轮奖励识别结果为空", Name);
            }
        }
        catch (Exception e) when (e is not OperationCanceledException)
        {
            _logger.LogWarning(e, "{Name}：奖励识别失败，已跳过本轮奖励汇总", Name);
        }
    }

    private async Task<bool> WaitForRewardResultReady(BvPage page)
    {
        var closeRect = ScaleRect(850, 960, 220, 35);

        for (var i = 0; i < 20; i++)
        {
            var closeRegion = page.Ocr(closeRect)
                .FirstOrDefault(r => r.Text.Contains("点击空白区域继续", StringComparison.Ordinal));
            if (closeRegion != null)
            {
                return true;
            }

            await Delay(300, _ct);
        }

        return false;
    }

    /// <summary>
    /// 在世界 Boss 领奖界面的固定区域点击“使用原粹树脂”。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <returns>成功点击并等待使用按钮消失时返回 true；识别到补充原粹树脂或超时时返回 false。</returns>
    private async Task<bool> TryUseOriginalResinOnRewardPrompt(BvPage page)
    {
        var useRect = ScaleRect(850, 740, 250, 35);

        try
        {
            await page.Locator("使用原粹树脂", useRect).ClickUntilDisappears(3000);
            await Delay(1000, _ct);
            return true;
        }
        catch (TimeoutException e)
        {
            var supplementRegions = await page.Locator("补充原粹树脂", useRect).TryWaitFor(1000);
            if (supplementRegions.Count > 0)
            {
                _logger.LogInformation("{Name}：领奖界面提示补充原粹树脂，当前原粹树脂不足", Name);
            }
            else
            {
                _logger.LogWarning("{Name}：未能在世界 Boss 领奖界面点击“使用原粹树脂”，原因：{Reason}", Name, e.Message);
            }

            return false;
        }
    }

    /// <summary>
    /// 关闭补充原粹树脂提示
    /// </summary>
    private async Task CloseResinSupplementPrompt(BvPage page)
    {
        var supplementRect = ScaleRect(850, 730, 250, 60);

        for (var i = 0; i < 50; i++)
        {
            _ct.ThrowIfCancellationRequested();
            var promptExists = page.Ocr(supplementRect).Any(region =>
                region.Text.Contains("补充", StringComparison.Ordinal)
                || region.Text.Contains("原粹", StringComparison.Ordinal)
                || region.Text.Contains("树脂", StringComparison.Ordinal));
            if (!promptExists)
            {
                return;
            }

            page.Keyboard.KeyPress(User32.VK.VK_ESCAPE);
            await page.Wait(300);
        }

        throw new TimeoutException("关闭补充原粹树脂提示超时");
    }

    // ==================== 私服补充树脂（自定义修改）开始 ====================

    /// <summary>
    /// 一次补充的结果。
    /// </summary>
    private enum PrivateServerReplenishOutcome
    {
        /// <summary>已确认使用了脆弱树脂（识别到了“获得”界面）。</summary>
        Used,

        /// <summary>已点击最后的“使用”，但没有识别到“获得”界面；是否成功交给领奖界面判断。</summary>
        MaybeUsed,

        /// <summary>补充界面里没有脆弱树脂（可能已经用完）。</summary>
        NoFragileResin,

        /// <summary>流程中途失败，没有使用脆弱树脂。</summary>
        Failed
    }

    // 下面的区域和坐标都是 1080P 坐标（其他 16:9 分辨率会自动换算），按 2560x1440 实机截图校准。

    /// <summary>领奖界面按钮（使用原粹树脂 / 补充原粹树脂）区域。</summary>
    private Rect PrivateServerRewardButtonRect => ScaleRect(850, 730, 250, 60);

    /// <summary>“补充原粹树脂”界面的标题区域。</summary>
    private Rect PrivateServerSupplementTitleRect => ScaleRect(834, 247, 256, 60);

    /// <summary>“补充原粹树脂”界面中，选中道具后显示道具名称的区域。</summary>
    private Rect PrivateServerSupplementNameRect => ScaleRect(860, 578, 200, 46);

    /// <summary>“补充原粹树脂”界面右下角“使用”按钮文字区域。</summary>
    private Rect PrivateServerSupplementUseRect => ScaleRect(1100, 740, 190, 80);

    /// <summary>“快捷使用”界面的标题区域。</summary>
    private Rect PrivateServerQuickUseTitleRect => ScaleRect(875, 269, 184, 63);

    /// <summary>“快捷使用”界面左上方道具名称区域。</summary>
    private Rect PrivateServerQuickUseNameRect => ScaleRect(700, 345, 200, 60);

    /// <summary>“快捷使用”界面右下角“使用”按钮文字区域。</summary>
    private Rect PrivateServerQuickUseUseRect => ScaleRect(1090, 720, 190, 80);

    /// <summary>“获得”界面顶部标题区域。</summary>
    private Rect PrivateServerObtainTitleRect => ScaleRect(924, 279, 74, 38);

    /// <summary>“获得”界面“点击空白区域继续”文字区域（在原粹树脂图标下方）。</summary>
    private Rect PrivateServerObtainHintRect => ScaleRect(780, 712, 360, 76);

    /// <summary>
    /// 判断征讨之花领奖界面的按钮是否显示为“补充原粹树脂”（即原粹树脂不足）。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    private bool HasReplenishButtonOnRewardPanel(BvPage page)
    {
        return page.Ocr(PrivateServerRewardButtonRect).Any(region => region.Text.Contains("补充", StringComparison.Ordinal));
    }

    /// <summary>
    /// 判断征讨之花领奖界面是否打开（按钮显示“使用原粹树脂”或“补充原粹树脂”）。
    /// 比原有识别区域更高一些，避免 2K 等分辨率下文字贴边识别不全。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    private bool IsRewardPanelOpen(BvPage page)
    {
        return page.Ocr(PrivateServerRewardButtonRect).Any(region => region.Text.Contains("原粹树脂", StringComparison.Ordinal));
    }

    /// <summary>
    /// 原有的“使用原粹树脂”识别区域较窄，2K 等分辨率下可能识别不全；这里用较宽的区域再找一次并点击。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <returns>找到并点击了“使用原粹树脂”时返回 true。</returns>
    private async Task<bool> TryClickUseOriginalResinWide(BvPage page)
    {
        var locator = page.Locator("使用原粹树脂", PrivateServerRewardButtonRect);
        if (!locator.IsExist())
        {
            return false;
        }

        try
        {
            await locator.ClickUntilDisappears(3000);
            await Delay(1000, _ct);
            _logger.LogInformation("{Name}：已点击“使用原粹树脂”", Name);
            return true;
        }
        catch (TimeoutException e)
        {
            _logger.LogWarning("{Name}：点击“使用原粹树脂”失败，原因：{Reason}", Name, e.Message);
            return false;
        }
    }

    /// <summary>
    /// 领奖界面显示“补充原粹树脂”时的处理：
    /// 1. 点击“补充原粹树脂” → 进入“补充原粹树脂”界面（默认选中脆弱树脂）；
    /// 2. 点击“使用” → 进入“快捷使用”界面，把数量调到最大（20）→ 点击“使用”；
    /// 3. 出现“获得”界面 → 点击“点击空白区域继续”这行文字，游戏会自动回到游戏主界面；
    /// 4. 确认已经回到游戏主界面（没有任何弹窗）；
    /// 5. 原地重新交互征讨之花。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <param name="attempt">当前征讨之花的第几次补充。</param>
    /// <returns>已重新打开领奖界面、需要再次尝试领奖时返回 true；
    /// 没有脆弱树脂、补充次数用尽、无法回到游戏主界面或无法重新交互时返回 false（随后结束讨伐）。</returns>
    private async Task<bool> TryReplenishOnRewardPanelAndReinteract(BvPage page, int attempt)
    {
        _logger.LogInformation("{Name}：领奖界面提示原粹树脂不足，第 {Attempt}/{Max} 次尝试使用 {Quantity} 个脆弱树脂补充",
            Name, attempt, PrivateServerMaxReplenishPerReward, PrivateServerFragileResinPerReplenish);

        var outcome = PrivateServerReplenishOutcome.Failed;
        var quantity = 0;
        try
        {
            (outcome, quantity) = await TryUseFragileResinFromRewardPanel(page);
        }
        catch (Exception e) when (e is not (OperationCanceledException or RetryException or NormalEndException))
        {
            _logger.LogWarning(e, "{Name}：补充脆弱树脂时出现异常", Name);
        }

        // 确认真正回到游戏主界面后才继续（还有弹窗会先关掉），避免在菜单里交互或移动角色
        if (!await EnsureCleanMainUi(page, "补充树脂后"))
        {
            return false;
        }

        switch (outcome)
        {
            case PrivateServerReplenishOutcome.Used:
                _logger.LogInformation("{Name}：已使用 {Quantity} 个脆弱树脂补充原粹树脂，重新交互征讨之花", Name, quantity);
                break;
            case PrivateServerReplenishOutcome.MaybeUsed:
                _logger.LogWarning("{Name}：已点击使用脆弱树脂，但未识别到“获得”界面，重新交互征讨之花确认是否补充成功", Name);
                break;
            case PrivateServerReplenishOutcome.NoFragileResin:
                _logger.LogWarning("{Name}：没有可用的脆弱树脂，结束讨伐", Name);
                return false;
            default:
                if (attempt >= PrivateServerMaxReplenishPerReward)
                {
                    _logger.LogWarning("{Name}：脆弱树脂补充失败，结束讨伐", Name);
                    return false;
                }

                _logger.LogWarning("{Name}：本次脆弱树脂补充失败，重新交互征讨之花后再试一次", Name);
                break;
        }

        await Delay(500, _ct);
        return await ReinteractRewardFlower(page);
    }

    /// <summary>
    /// 领奖界面 → 补充原粹树脂 → 脆弱树脂 → 使用 → 数量调到最大 → 使用 → 关闭“获得”界面。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <returns>补充结果和使用数量（数量识别不到时为 0）。</returns>
    private async Task<(PrivateServerReplenishOutcome Outcome, int Quantity)> TryUseFragileResinFromRewardPanel(BvPage page)
    {
        // 1. 点击领奖界面的“补充原粹树脂”，打开“补充原粹树脂”界面
        if (!await TryOpenSupplementPaneFromRewardPanel(page))
        {
            return (PrivateServerReplenishOutcome.Failed, 0);
        }

        // 2. 确认选中的是脆弱树脂（默认就是选中的，下方会显示“脆弱树脂”）；没选中时点击脆弱树脂图标
        //    没确认是脆弱树脂时绝不点击“使用”，避免误用原石等其他道具
        var fragileNameLocator = page.Locator("脆弱树脂", PrivateServerSupplementNameRect).WithRetryInterval(300);
        if ((await fragileNameLocator.TryWaitFor(1500)).Count == 0)
        {
            var fragileResin = new SupplementalResinOption("脆弱树脂", LoadRecognitionObject("FragileResinInSupplementPane"));
            var icons = await page.Locator(fragileResin.Template)
                .WithRoi(ScaleRect(644, 378, 620, 192))
                .WithRetryInterval(300)
                .TryWaitFor(2000);
            if (icons.Count == 0)
            {
                _logger.LogWarning("{Name}：补充界面里没有找到脆弱树脂（可能已经用完）", Name);
                return (PrivateServerReplenishOutcome.NoFragileResin, 0);
            }

            if (!await TrySelectSupplementalResin(page, fragileResin) || !fragileNameLocator.IsExist())
            {
                _logger.LogWarning("{Name}：未能确认已选中脆弱树脂，为避免误用其他道具，取消本次补充", Name);
                return (PrivateServerReplenishOutcome.Failed, 0);
            }
        }

        // 3. 点击“使用”，进入“快捷使用”界面
        if (!await ClickPanelButton(page, "使用", PrivateServerSupplementUseRect, 1178, 781,
                "补充原粹树脂", PrivateServerSupplementTitleRect))
        {
            return (PrivateServerReplenishOutcome.Failed, 0);
        }

        var quickUseTitles = await page.Locator("快捷使用", PrivateServerQuickUseTitleRect)
            .WithRetryInterval(300)
            .TryWaitFor(3000);
        if (quickUseTitles.Count == 0)
        {
            // 没有出现选择数量的界面：可能直接使用了 1 个
            if (await TryCloseObtainDialog(page))
            {
                return (PrivateServerReplenishOutcome.Used, 1);
            }

            _logger.LogWarning("{Name}：点击“使用”后没有出现“快捷使用”界面", Name);
            return (PrivateServerReplenishOutcome.Failed, 0);
        }

        // 再次确认“快捷使用”的是脆弱树脂
        if ((await page.Locator("脆弱树脂", PrivateServerQuickUseNameRect).WithRetryInterval(300).TryWaitFor(1500)).Count == 0)
        {
            _logger.LogWarning("{Name}：“快捷使用”界面未识别到脆弱树脂，为避免误用其他道具，取消本次补充", Name);
            return (PrivateServerReplenishOutcome.Failed, 0);
        }

        // 4. 把使用数量调到最大
        var quantity = await SetQuickUseQuantityToMax(page);

        // 5. 点击“使用”
        if (!await ClickPanelButton(page, "使用", PrivateServerQuickUseUseRect, 1164, 757,
                "快捷使用", PrivateServerQuickUseTitleRect))
        {
            return (PrivateServerReplenishOutcome.Failed, 0);
        }

        // 6. “获得”界面：点击“点击空白区域继续”这行文字
        if (await TryCloseObtainDialog(page))
        {
            return (PrivateServerReplenishOutcome.Used, quantity);
        }

        return (PrivateServerReplenishOutcome.MaybeUsed, quantity);
    }

    /// <summary>
    /// 点击领奖界面的“补充原粹树脂”按钮，直到出现“补充原粹树脂”界面。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <returns>“补充原粹树脂”界面已打开时返回 true。</returns>
    private async Task<bool> TryOpenSupplementPaneFromRewardPanel(BvPage page)
    {
        var titleLocator = page.Locator("补充原粹树脂", PrivateServerSupplementTitleRect).WithRetryInterval(1000);
        var buttonLocator = page.Locator("补充原粹树脂", PrivateServerRewardButtonRect);

        try
        {
            await titleLocator
                .WithRetryAction(_ =>
                {
                    var buttons = buttonLocator.FindAll();
                    if (buttons.Count > 0)
                    {
                        buttons[0].Click();
                    }
                })
                .WaitFor(6000);
            return true;
        }
        catch (TimeoutException e)
        {
            _logger.LogWarning("{Name}：点击“补充原粹树脂”后没有出现补充界面，原因：{Reason}", Name, e.Message);
            return false;
        }
    }

    /// <summary>
    /// 点击弹窗中的按钮：先用 OCR 找按钮文字；没认出文字但确认还在该弹窗时，直接点击按钮的固定位置。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <param name="buttonText">按钮文字。</param>
    /// <param name="textRect">按钮文字所在区域。</param>
    /// <param name="fallbackX">按钮中心 X（1080P 坐标）。</param>
    /// <param name="fallbackY">按钮中心 Y（1080P 坐标）。</param>
    /// <param name="panelTitle">弹窗标题，用于确认还在该弹窗。</param>
    /// <param name="panelTitleRect">弹窗标题区域。</param>
    /// <returns>已点击按钮时返回 true。</returns>
    private async Task<bool> ClickPanelButton(BvPage page, string buttonText, Rect textRect, double fallbackX, double fallbackY,
        string panelTitle, Rect panelTitleRect)
    {
        try
        {
            await page.Locator(buttonText, textRect).Click(3000);
            return true;
        }
        catch (TimeoutException)
        {
            if (page.Locator(panelTitle, panelTitleRect).IsExist())
            {
                _logger.LogInformation("{Name}：未识别到“{Text}”按钮文字，按固定位置点击", Name, buttonText);
                page.Click(fallbackX, fallbackY);
                return true;
            }

            _logger.LogWarning("{Name}：没有找到“{Panel}”界面的“{Text}”按钮", Name, panelTitle, buttonText);
            return false;
        }
    }

    /// <summary>
    /// 在“快捷使用”界面把使用数量调到最大（不超过设定数量，单次最多 20 个）：
    /// 先把滑块从最左端拖到滑条最右端，再点击右侧“+”号补足（到上限后再点不会增加），
    /// 最后识别数量，不足时再补点“+”号。数量识别不到时不会卡住，直接继续。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <returns>识别到的使用数量；识别不到时返回 0。</returns>
    private async Task<int> SetQuickUseQuantityToMax(BvPage page)
    {
        var target = Math.Min(PrivateServerFragileResinPerReplenish, MaxQuickUseQuantity);

        // 滑条右端显示的是本次最多能用的数量（脆弱树脂不足 20 个时会更少）
        var available = RecognizeQuickUseAvailableCount();
        if (available > 0 && available < target)
        {
            target = available;
        }

        if (target >= MaxQuickUseQuantity || target == available)
        {
            // 方法一：把滑块（x=744）拖到滑条最右端（滑条终点约 x=1180，拖过头会停在最大值）
            await DragQuickUseSlider(744, 1200, 648);
        }

        // 方法二：点击右侧“+”号（x=1292），数量从 1 开始，点 target-1 次
        for (var i = 0; i < target - 1; i++)
        {
            page.Click(1292, 648);
            await Delay(150, _ct);
        }

        // 识别数量，不足时补点“+”号（最多补 3 轮）
        var quantity = 0;
        for (var round = 0; round < 3; round++)
        {
            await Delay(400, _ct);
            var recognized = TryRecognizeQuickUseQuantity();
            if (recognized is not > 0)
            {
                break;
            }

            quantity = recognized.Value;
            if (quantity >= target)
            {
                break;
            }

            for (var i = 0; i < target - quantity; i++)
            {
                page.Click(1292, 648);
                await Delay(200, _ct);
            }
        }

        if (quantity > 0)
        {
            _logger.LogInformation("{Name}：脆弱树脂使用数量 {Quantity}（目标 {Target}）", Name, quantity, target);
            return quantity;
        }

        _logger.LogInformation("{Name}：已把脆弱树脂使用数量调到最大（目标 {Target}，数量未能识别）", Name, target);
        return 0;
    }

    /// <summary>
    /// 按住鼠标把“快捷使用”界面的滑块拖到指定位置（1080P 坐标）。
    /// </summary>
    private async Task DragQuickUseSlider(int fromX, int toX, int y)
    {
        try
        {
            GameCaptureRegion.GameRegion1080PPosMove(fromX, y);
            await Delay(200, _ct);
            Simulation.SendInput.Mouse.LeftButtonDown();
            await Delay(150, _ct);
            var step = fromX < toX ? 40 : -40;
            for (var x = fromX; step > 0 ? x <= toX : x >= toX; x += step)
            {
                GameCaptureRegion.GameRegion1080PPosMove(x, y);
                await Delay(30, _ct);
            }

            GameCaptureRegion.GameRegion1080PPosMove(toX, y);
            await Delay(200, _ct);
        }
        finally
        {
            Simulation.SendInput.Mouse.LeftButtonUp();
        }

        await Delay(300, _ct);
    }

    /// <summary>
    /// 关闭补充树脂后的“获得”界面：点击“点击空白区域继续”这行文字
    /// （没认出文字时点击这行文字的固定位置），不会点到画面正中心的原粹树脂图标。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <returns>识别到“获得”界面并已关闭时返回 true；5 秒内没有出现“获得”界面时返回 false。</returns>
    private async Task<bool> TryCloseObtainDialog(BvPage page)
    {
        var appeared = false;
        var stopwatch = Stopwatch.StartNew();
        while (stopwatch.ElapsedMilliseconds < 5000)
        {
            using (var capture = CaptureToRectArea())
            {
                if (IsObtainDialogOpen(capture))
                {
                    appeared = true;
                    break;
                }
            }

            await Delay(300, _ct);
        }

        if (!appeared)
        {
            _logger.LogWarning("{Name}：未识别到“获得”界面", Name);
            return false;
        }

        for (var i = 0; i < 5; i++)
        {
            using (var capture = CaptureToRectArea())
            {
                if (!IsObtainDialogOpen(capture))
                {
                    return true;
                }

                var hint = FindOcrText(capture, PrivateServerObtainHintRect, "空白区域");
                if (hint != null)
                {
                    hint.Click();
                }
                else
                {
                    page.Click(960, 748);
                }
            }

            await Delay(800, _ct);
        }

        using var finalCapture = CaptureToRectArea();
        return !IsObtainDialogOpen(finalCapture);
    }

    /// <summary>
    /// 是否处于“获得”界面（底部“点击空白区域继续”或顶部“获得”标题）。
    /// </summary>
    private bool IsObtainDialogOpen(ImageRegion capture)
    {
        return FindOcrText(capture, PrivateServerObtainHintRect, "空白区域") != null
               || FindOcrText(capture, PrivateServerObtainTitleRect, "获得") != null;
    }

    /// <summary>
    /// 在截图的指定区域 OCR，返回第一个包含指定文字的区域。
    /// </summary>
    private static Region? FindOcrText(ImageRegion capture, Rect rect, string text)
    {
        return capture.FindMulti(RecognitionObject.Ocr(rect))
            .FirstOrDefault(region => region.Text.Contains(text, StringComparison.Ordinal));
    }

    /// <summary>
    /// 确认已经真正回到游戏主界面：左上角派蒙图标可见，并且没有领奖界面、补充原粹树脂、快捷使用、“获得”等弹窗
    /// （这些弹窗后面也能看到派蒙图标，原有的“返回主界面”会误以为已经回到主界面）。
    /// 有“点击空白区域继续”时点击这行文字关闭，其余弹窗按 ESC 关闭。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <param name="stage">日志里显示的阶段名称。</param>
    /// <returns>回到游戏主界面时返回 true；多次尝试仍未回到时返回 false（调用方会结束讨伐，不会再移动角色）。</returns>
    private async Task<bool> EnsureCleanMainUi(BvPage page, string stage)
    {
        var unknownTimes = 0;
        for (var i = 0; i < 15; i++)
        {
            _ct.ThrowIfCancellationRequested();
            using (var capture = CaptureToRectArea())
            {
                var inMainUi = Bv.IsInMainUi(capture);
                var hint = FindOcrText(capture, PrivateServerObtainHintRect, "空白区域");
                var obtainTitle = FindOcrText(capture, PrivateServerObtainTitleRect, "获得");
                var hasPanel = Bv.IsInBigMapUi(capture)
                               || Bv.IsInAnyClosableUi(capture)
                               || FindOcrText(capture, PrivateServerRewardButtonRect, "原粹树脂") != null
                               || FindOcrText(capture, PrivateServerSupplementTitleRect, "补充原粹树脂") != null
                               || FindOcrText(capture, PrivateServerQuickUseTitleRect, "快捷使用") != null;

                if (inMainUi && hint == null && obtainTitle == null && !hasPanel)
                {
                    return true;
                }

                if (hint != null)
                {
                    // “获得”界面：点击“点击空白区域继续”这行文字
                    hint.Click();
                    unknownTimes = 0;
                }
                else if (obtainTitle != null)
                {
                    page.Click(960, 748);
                    unknownTimes = 0;
                }
                else if (hasPanel || ++unknownTimes >= 2)
                {
                    // 未知界面先等一轮（可能是界面切换动画），连续两次仍不是主界面再按 ESC
                    page.Keyboard.KeyPress(User32.VK.VK_ESCAPE);
                    unknownTimes = 0;
                }
            }

            await Delay(900, _ct);
        }

        _logger.LogWarning("{Name}：{Stage}多次尝试仍未回到游戏主界面，为避免在菜单里移动角色，结束讨伐", Name, stage);
        return false;
    }

    /// <summary>
    /// 在游戏主界面重新交互征讨之花：先原地等待“接触征讨之花”提示并按交互键；
    /// 原地找不到时，先确认已回到游戏主界面，再使用原有的寻找征讨之花流程靠近并交互。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <returns>成功重新打开领奖界面时返回 true。</returns>
    private async Task<bool> ReinteractRewardFlower(BvPage page)
    {
        var stopwatch = Stopwatch.StartNew();
        var lastInteractAt = DateTime.MinValue;

        while (stopwatch.Elapsed < TimeSpan.FromSeconds(6))
        {
            _ct.ThrowIfCancellationRequested();
            if (IsRewardPanelOpen(page))
            {
                _logger.LogInformation("{Name}：已重新进入征讨之花领奖界面", Name);
                return true;
            }

            if (HasRewardInteractionPrompt(page) && DateTime.UtcNow - lastInteractAt >= TimeSpan.FromMilliseconds(1000))
            {
                Simulation.SendInput.SimulateAction(GIActions.PickUpOrInteract);
                lastInteractAt = DateTime.UtcNow;
            }

            await Delay(300, _ct);
        }

        // 重新寻找征讨之花会移动角色和视角，必须先确认已经回到游戏主界面
        if (!await EnsureCleanMainUi(page, "重新寻找征讨之花前"))
        {
            return false;
        }

        _logger.LogInformation("{Name}：原地未找到“接触征讨之花”，重新寻找征讨之花", Name);
        try
        {
            await NavigateToReward();
            return true;
        }
        catch (TimeoutException e)
        {
            _logger.LogWarning("{Name}：重新交互征讨之花失败，原因：{Reason}", Name, e.Message);
            return false;
        }
    }

    // ==================== 私服补充树脂（自定义修改）结束 ====================

    /// <summary>
    /// 关闭领奖结果页面，等待回到主界面。
    /// </summary>
    /// <exception cref="Exception">多次尝试后仍未回到主界面时抛出。</exception>
    private async Task CloseRewardResult()
    {
        var page = new BvPage(_ct);
        var closeRect = ScaleRect(850, 960, 220, 35);

        for (var i = 0; i < 20; i++)
        {
            using var capture = CaptureToRectArea();
            if (Bv.IsInMainUi(capture))
            {
                return;
            }

            var closeRegion = capture.FindMulti(RecognitionObject.Ocr(closeRect))
                .FirstOrDefault(r => r.Text.Contains("点击空白区域继续", StringComparison.Ordinal));
            if (closeRegion != null)
            {
                closeRegion.Click();
            }
            else if (i > 5)
            {
                page.Click(960, 540);
            }

            await Delay(300, _ct);
        }

        using var finalCapture = CaptureToRectArea();
        if (!Bv.IsInMainUi(finalCapture))
        {
            throw new Exception("领取奖励后未成功回到主界面");
        }
    }

    /// <summary>
    /// 领奖后为下一轮讨伐重新定位：交互启动 Boss 走战后路线，特殊 Boss 重跑特殊路线，普通 Boss 回到路线终点。
    /// </summary>
    private async Task RepositionAfterFight()
    {
        if (AutoBossData.IsTalkToStartBoss(_taskParam.BossName))
        {
            _logger.LogInformation("{Name}：战后重新靠近交互点", Name);
            await RunPathingFile($"{_taskParam.BossName}战斗后快速前往.json");
            return;
        }

        if (AutoBossData.IsNoPathingSupportBoss(_taskParam.BossName))
        {
            _logger.LogInformation("{Name}：重新执行特殊路线靠近首领", Name);
            await NavigateToBoss();
            return;
        }

        if (AutoBossData.ShouldRerunRoute(_taskParam.BossName))
        {
            _logger.LogInformation("{Name}：重新执行完整路线靠近首领", Name);
            await RunPathingFile($"{_taskParam.BossName}前往.json");
            return;
        }

        _logger.LogInformation("{Name}：重新靠近首领位置并等待 4 秒", Name);
        var routePath = BuildPathingAssetPath($"{_taskParam.BossName}前往.json");
        var originalTask = PathingTask.BuildFromFilePath(routePath) ?? throw new Exception($"路径文件解析失败：{routePath}");
        var lastPosition = originalTask.Positions.LastOrDefault() ?? throw new Exception("路线文件缺少路径点");
        var repositionTask = new PathingTask
        {
            Info = originalTask.Info,
            Config = originalTask.Config,
            Positions = [lastPosition]
        };

        await RunPathingTask(repositionTask);
        await Delay(4000, _ct);
    }

    /// <summary>
    /// 将 1080P 基准矩形缩放到当前资源比例。
    /// </summary>
    /// <param name="x">基准 X 坐标。</param>
    /// <param name="y">基准 Y 坐标。</param>
    /// <param name="width">基准宽度。</param>
    /// <param name="height">基准高度。</param>
    /// <returns>缩放后的矩形。</returns>
    private Rect ScaleRect(int x, int y, int width, int height)
    {
        return new Rect(ScaleX(x), ScaleY(y), ScaleX(width), ScaleY(height));
    }

    /// <summary>
    /// 将 1080P 基准 X 方向长度缩放到当前资源比例。
    /// </summary>
    /// <param name="value">基准长度或坐标。</param>
    /// <returns>缩放后的整数值。</returns>
    private int ScaleX(int value)
    {
        return (int)Math.Round(value * AssetScale);
    }

    /// <summary>
    /// 将 1080P 基准 Y 方向长度缩放到当前资源比例。
    /// </summary>
    /// <param name="value">基准长度或坐标。</param>
    /// <returns>缩放后的整数值。</returns>
    private int ScaleY(int value)
    {
        return (int)Math.Round(value * AssetScale);
    }

}
