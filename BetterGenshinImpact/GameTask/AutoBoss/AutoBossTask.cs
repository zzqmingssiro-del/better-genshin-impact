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
    // 另外，私服领奖结果页的“点击空白区域继续”就在奖励图标正下方，原来的关闭方法只在画面最下方找这行字，
    // 找不到时会点击屏幕正中间，正好点到奖励图标、弹出物品详情而卡住；现在改为在画面下半部分找到这行字并点击它。
    // 下面几个开关改完需要重新编译。

    /// <summary>领奖界面出现“补充原粹树脂”时，是否自动用脆弱树脂补充并重新领取。</summary>
    private static readonly bool PrivateServerReplenishOnRewardPanel = true;

    /// <summary>每次补充使用的脆弱树脂数量（快捷使用界面单次最多 20 个）。</summary>
    private static readonly int PrivateServerFragileResinPerReplenish = 20;

    /// <summary>同一朵征讨之花最多补充几次，防止识别异常时无限消耗脆弱树脂。</summary>
    private static readonly int PrivateServerMaxReplenishPerReward = 2;

    /// <summary>是否跳过每轮开战前的大地图树脂预检（私服预检结果不可信，跳过可省去每轮开关地图的时间）。</summary>
    private static readonly bool PrivateServerSkipResinPreCheck = true;

    /// <summary>领奖后是否用私服版方法关闭奖励结果页（点击“点击空白区域继续”这行字，绝不点击画面中间的奖励图标）。</summary>
    private static readonly bool PrivateServerSafeCloseRewardResult = true;
    // ==================== 私服补充树脂（自定义修改）结束 ====================

    // ==================== 私服首领轮换 / 寻找无图标征讨之花（自定义修改）开关 ====================
    // 私服每个首领每周最多领取 100 次。征讨之花提示“本周收取该宝藏次数已耗尽”时，
    // 自动打开冒险之证 → 讨伐 → 首领，按列表顺序（从左到右、从上到下）选中红框标记的下一个首领，
    // 点击“前往”→“传送并追踪”，再用 BetterGI 自带的路线前往并继续讨伐。
    // 需要先完成前置任务的、附近没有解锁传送锚点的、BetterGI 不支持的、写在跳过名单（User\私服跳过的首领.txt）里的首领会自动跳过。
    // 另外，有些首领的征讨之花头顶没有图标，原来的找花方法找不到就会结束任务；现在找不到图标时改为按花身上的红色花纹寻找。
    // 第 9 版：战斗结束后先原地慢慢转视角找花（转的时候不走动），找到后对准直线走过去；转完几圈还找不到，
    // 就传送到首领附近的传送锚点、按 BetterGI 自带的路线重新跑到首领那里再找一次，还找不到就换下一个首领。
    // 第 10 版：找花前先把镜头拉远（滚轮往下）、视角朝下看，让画面里主要是地面；头顶没有图标的花改按深色叶子和红紫色花苞找，
    // 减少光影和地形颜色的干扰；走到花跟前（或者没找到）时把视角回正。
    // 下面几个开关改完需要重新编译。

    /// <summary>征讨之花提示“本周收取该宝藏次数已耗尽”时，是否按冒险之证首领列表顺序自动换下一个首领继续讨伐（关闭时直接结束任务）。</summary>
    private static readonly bool PrivateServerBossRotation = true;

    /// <summary>任务开始时是否先打开冒险之证，从红框标记的首领开始讨伐（开启后 BetterGI 界面里选择的首领只在识别失败时使用）。</summary>
    private static readonly bool PrivateServerStartFromHandbookSelection = true;

    /// <summary>在冒险之证选好首领后，是否点击“前往”→“传送并追踪”（追踪该首领），之后再走 BetterGI 自带的路线。</summary>
    private static readonly bool PrivateServerHandbookTeleportAndTrack = true;

    /// <summary>
    /// 征讨之花头顶没有图标时，是否改为按花本身的样子寻找：第 5～8 版的找法按花身上的红色花纹找（还找不到时回到首领位置再找一次）；
    /// 第 9 版的找法（PrivateServerSlowScanForFlower）里，第 10 版起改为按深色叶子和红紫色花苞找。
    /// </summary>
    private static readonly bool PrivateServerFindFlowerWithoutIcon = true;

    /// <summary>
    /// 战斗结束后是否先原地慢慢转视角找征讨之花（最多转 3 圈，转的时候不走动），找到后对准、直线走过去，路上多按几次交互键；
    /// 转完还找不到时，传送到首领附近的传送锚点、按 BetterGI 自带的路线重新跑到首领那里再找一次，还找不到就换下一个首领。
    /// 改成 false：用第 5～8 版的找法（找不到图标时按红色花纹边走边找，容易跑出首领区域）。（第 9 版）
    /// </summary>
    private static readonly bool PrivateServerSlowScanForFlower = true;

    /// <summary>本轮原地转了几圈、重新跑图后都没有找到征讨之花（第 9 版）。</summary>
    private volatile bool _psFlowerNotFound;

    /// <summary>
    /// 找征讨之花前，是否先把镜头拉远（滚轮往下滚）、视角朝下看，让画面里主要是地面：远处的地形、天空、光影干扰少了，角色也不容易挡住花。
    /// 走到花跟前（或者没找到）时按一下鼠标中键把视角回正；镜头拉远后不会再拉近。只在 PrivateServerSlowScanForFlower 为 true 时有效。（第 10 版）
    /// </summary>
    private static readonly bool PrivateServerZoomOutAndLookDown = true;

    /// <summary>没找到征讨之花时，是否把找花时看到的画面保存到 BetterGI 文件夹里的 log\pserver_flower（每次最多 8 张），方便以后调整识别。（第 10 版）</summary>
    private static readonly bool PrivateServerSaveFlowerSearchScreenshots = true;

    /// <summary>找花时视角朝下看过、还没来得及回正（例如直接进了领奖界面），下一轮开打前要先回正（第 10 版）。</summary>
    private volatile bool _psCameraNeedsReset;

    /// <summary>本轮在征讨之花处看到了“本周收取该宝藏次数已耗尽”。</summary>
    private volatile bool _psWeeklyLimitReached;

    /// <summary>任务开始时是否已经按冒险之证选择过首领（角色死亡重试时不再重复选择）。</summary>
    private bool _psStartSelectionDone;

    /// <summary>最近一次看到征讨之花（头顶图标或红色花纹）的时间（UTC Ticks）。</summary>
    private long _psRewardTargetSeenTicks;

    /// <summary>最近一次看到“接触征讨之花”提示的时间（UTC Ticks）。看到后原地停下，按一次交互键等结果（第 8 版）。</summary>
    private long _psRewardPromptSeenTicks;

    /// <summary>附近找不到征讨之花时，允许像原来一样边转视角边往前走。</summary>
    private volatile bool _psRewardBlindWalk;

    /// <summary>
    /// 首领轮换时要跳过的首领名单文件（在 BetterGI 安装目录的 User 文件夹里，和你的配置放在一起）。
    /// 用记事本修改后保存即可，下次换首领时生效，不需要重新编译。文件不存在时会按下面的默认内容自动创建。
    /// </summary>
    private const string PrivateServerSkippedBossFileName = @"User\私服跳过的首领.txt";

    /// <summary>
    /// 跳过名单文件的默认内容：每行一个首领名字（写名字的一部分也可以），一行里 # 后面的内容不生效。
    /// </summary>
    private static readonly string[] PrivateServerSkippedBossFileDefaultLines =
    [
        "# 私服首领轮换：这个名单里的首领会被自动跳过。",
        "# 每行写一个首领名字。写名字的一部分也可以，例如“无相之”会跳过所有无相系列的首领。",
        "# 一行里 # 后面的内容不生效（是说明文字）：在行首加 # 就是不跳过这个首领，删掉行首的 # 就是跳过。",
        "# 用记事本修改后保存即可，下次换首领时生效，不需要重新编译 BetterGI。",
        "# 需要先完成前置任务的首领、附近没有解锁传送锚点的首领、BetterGI 不支持的首领，程序会自动跳过，不用写在这里。",
        "",
        "# ===== 你要求跳过的 =====",
        "重拳出击鸭        # 喜欢乱跑，停在首领区域边上",
        "贪食匿叶龙山王    # 私服有 bug，首领刷在场地边上",
        "冰风组曲          # 需要先对话才能开打",
        "歌裴莉娅的葬送    # 冰风组曲（BetterGI 里的名字）",
        "科培琉司的劫罚    # 冰风组曲（BetterGI 里的名字）",
        "无相之            # 无相系列：无相之雷、无相之岩、无相之火、无相之水、无相之草等",
        "魔偶剑鬼          # 一直下雨，再加上冰伤会被冻住",
        "纯水精灵          # 太拖沓，地板会下潜，打不到天上飞的怪",
        "",
        "# ===== 建议考虑跳过的（默认不跳过，删掉行首的 # 就会跳过）=====",
        "# 蕴光月守宫              # BetterGI 标注：所在的分层地图还不支持路径追踪，只能用键鼠宏走过去，比较容易出问题",
        "# 蕴光月幻蝶              # 同上",
        "# 超重型陆巡舰·机动战垒   # 同上",
        "# 雷音权现                # 会瞬移、飞到空中，近战容易打不到（和纯水精灵的问题类似）",
        "# 风蚀沙虫                # 会钻进沙子里到处跑（和重拳出击鸭的问题类似）",
        "# 兆载永劫龙兽            # 会飞到空中，近战容易打不到",
    ];

    /// <summary>本次任务是否已经在日志里列出过跳过名单。</summary>
    private bool _psSkipListLogged;
    // ==================== 私服首领轮换 / 寻找无图标征讨之花（自定义修改）开关结束 ====================

    // ==================== 私服自动领取空月祝福（自定义修改）开关 ====================
    /// <summary>
    /// 每天凌晨 4 点弹出“空月祝福”领取界面时，是否自动领取：暂停战斗、寻路等操作 → 点击空白处领取 →
    /// 等动画结束 → 点击“点击空白区域继续”关闭“获得 原石”界面（不会点中间的原石）→ 继续之前的操作。
    /// 改成 false 就不处理（BetterGI 自带的处理仍然有效，但它只在传送、走路线的时候检查）。
    /// </summary>
    private static readonly bool PrivateServerAutoClaimWelkinMoon = true;

    /// <summary>同一时间只处理一次空月祝福。</summary>
    private readonly SemaphoreSlim _psWelkinLock = new(1, 1);

    /// <summary>最近一次处理空月祝福的时间（UTC Ticks，0 表示还没处理过）。</summary>
    private long _psWelkinHandledTicks;

    /// <summary>正在进行领奖、补充树脂、冒险之证这些自己的界面操作的层数（大于 0 时不把原石图标当作空月祝福）。</summary>
    private int _psOwnUiDepth;

    /// <summary>最近一次打开冒险之证选择首领是否因为操作失败而结束（用于被空月祝福打断后重试）。</summary>
    private bool _psHandbookFailed;
    // ==================== 私服自动领取空月祝福（自定义修改）开关结束 ====================

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
        _psWeeklyLimitReached = false;
        _psFlowerNotFound = false;
        _psCameraNeedsReset = false;
        _psStartSelectionDone = false;
        _psSkipListLogged = false;
        Validate();
        LogScreenResolution();

        Notify.Event("AutoBoss").Success($"{Name}启动");
        // 私服：后台检查每天凌晨 4 点弹出的空月祝福界面，出现时自动领取
        using var psWelkinCts = CancellationTokenSource.CreateLinkedTokenSource(ct);
        var psWelkinWatchdog = PrivateServerAutoClaimWelkinMoon
            ? Task.Run(() => PrivateServerWelkinMoonWatchdog(psWelkinCts.Token))
            : Task.CompletedTask;
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
            // 私服：停止后台检查空月祝福
            psWelkinCts.Cancel();
            try
            {
                await psWelkinWatchdog;
            }
            catch (Exception e)
            {
                _logger.LogDebug(e, "{Name}：停止空月祝福检查时出错", Name);
            }

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

        // 私服：任务开始时，从冒险之证红框标记的首领开始讨伐
        if (PrivateServerBossRotation && PrivateServerStartFromHandbookSelection && !_psStartSelectionDone)
        {
            _psStartSelectionDone = true;
            await PrivateServerPickStartBossFromHandbook();
        }
        
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
            
            // 私服：找花时视角朝下看过、还没回正的（例如直接进了领奖界面），开打前先回正（第 10 版）
            if (_psCameraNeedsReset)
            {
                _psCameraNeedsReset = false;
                Simulation.SendInput.Mouse.MiddleButtonClick();
                _logger.LogInformation("{Name}：视角回正", Name);
                await Delay(300, _ct);
            }

            //4.首次讨伐 or 回过七天神像 则需要重新寻路到首领
            if (shouldNavigateToBoss)
            {
                await NavigateToBoss();
            }
            
            //5.开始战斗
            await RunAutoFight();
            
            //6.寻路到征讨之花（私服：找不到时传送回来按路线重新跑一遍再找；还找不到就换下一个首领）
            await PrivateServerNavigateToReward();

            // 私服：征讨之花提示“本周收取该宝藏次数已耗尽” → 按冒险之证的顺序换下一个首领
            if (_psWeeklyLimitReached)
            {
                if (!await PrivateServerHandleWeeklyLimit())
                {
                    break;
                }

                shouldNavigateToBoss = true;
                continue;
            }
            
            // 私服：原地转了几圈、重新跑图后都没有找到征讨之花 → 按冒险之证的顺序换下一个首领（第 9 版）
            if (_psFlowerNotFound)
            {
                if (!await PrivateServerHandleFlowerNotFound())
                {
                    break;
                }

                shouldNavigateToBoss = true;
                continue;
            }

            //7.交互征讨之花
            bool rewardSuccess;
            // 私服：领奖（包括补充树脂）是自己的界面操作，这期间后台检查不把原石图标当作空月祝福的“获得”界面
            using (PrivateServerEnterOwnUi())
            {
                rewardSuccess = await TakeReward();
            }

            // 私服：征讨之花提示“本周收取该宝藏次数已耗尽” → 按冒险之证的顺序换下一个首领
            if (_psWeeklyLimitReached)
            {
                if (!await PrivateServerHandleWeeklyLimit())
                {
                    break;
                }

                shouldNavigateToBoss = true;
                continue;
            }
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

        // 私服：找花时视角朝下看过、还没回正的，任务结束前回正（第 10 版）
        if (_psCameraNeedsReset)
        {
            _psCameraNeedsReset = false;
            Simulation.SendInput.Mouse.MiddleButtonClick();
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
        // 私服：战斗结束后先原地慢慢转视角找花，找到后对准直线走过去（第 9 版）
        if (PrivateServerSlowScanForFlower)
        {
            await PrivateServerScanAndApproachFlower();
            return;
        }

        using var navigationCts = CancellationTokenSource.CreateLinkedTokenSource(_ct);
        var page = new BvPage(navigationCts.Token);

        _logger.LogInformation("{Name}：开始寻找征讨之花", Name);

        var navigationStopwatch = Stopwatch.StartNew();
        // 私服：头顶没有图标的征讨之花需要更长的寻找时间
        var navigationTimeout = TimeSpan.FromSeconds(PrivateServerFindFlowerWithoutIcon ? 45 : 20);
        Interlocked.Exchange(ref _psRewardTargetSeenTicks, 0);
        Interlocked.Exchange(ref _psRewardPromptSeenTicks, 0);
        _psRewardBlindWalk = !PrivateServerFindFlowerWithoutIcon;
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
                    if (_psWeeklyLimitReached)
                    {
                        _logger.LogInformation("{Name}：征讨之花提示“本周收取该宝藏次数已耗尽”", Name);
                        return;
                    }

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
        // 私服：按了交互键却没有弹出领奖界面（也没认出提示文字）的次数
        var unansweredPresses = 0;

        while (!ct.IsCancellationRequested)
        {
            ct.ThrowIfCancellationRequested();

            // 私服：同时用稍宽的区域确认领奖界面
            if (HasRewardPanelPrompt(page) || IsRewardPanelOpen(page))
            {
                return;
            }

            // 私服：按下交互键后提示“本周收取该宝藏次数已耗尽”（不会弹出领奖界面）
            if (DateTime.UtcNow - lastInteractAt < TimeSpan.FromSeconds(4) && HasWeeklyLimitToast(page))
            {
                _psWeeklyLimitReached = true;
                return;
            }

            if (HasRewardInteractionPrompt(page))
            {
                // 私服：看到提示后原地停下（MoveToRewardTask 暂停往前走），按一次交互键后等一会儿看结果，不连续按。
                // 本周次数用完时不会弹出领奖界面：原来每 0.3 秒按一次、边走边跳，角色会走过头，提示文字也会反复重新弹出而认不出来
                Interlocked.Exchange(ref _psRewardPromptSeenTicks, DateTime.UtcNow.Ticks);
                if (DateTime.UtcNow - lastInteractAt >= TimeSpan.FromMilliseconds(PrivateServerInteractRetryMs))
                {
                    if (lastInteractAt != DateTime.MinValue)
                    {
                        unansweredPresses++;
                        if (unansweredPresses >= PrivateServerUnansweredInteractLimit)
                        {
                            // 私服：私服上按交互键打不开领奖界面，只会是本周次数用完了（提示文字没认出来时的兜底）
                            _logger.LogWarning("{Name}：按了 {Count} 次交互键都没有弹出领奖界面（也没认出提示文字），按“本周收取该宝藏次数已耗尽”处理",
                                Name, unansweredPresses);
                            _psWeeklyLimitReached = true;
                            return;
                        }

                        _logger.LogInformation("{Name}：按交互键后没有弹出领奖界面，再按一次", Name);
                    }

                    Simulation.SendInput.SimulateAction(GIActions.PickUpOrInteract);
                    lastInteractAt = DateTime.UtcNow;
                }
            }

            // 私服：刚按过交互键时看得勤一些（0.15 秒一次），平时和原来一样 0.3 秒一次
            await Delay(DateTime.UtcNow - lastInteractAt < TimeSpan.FromSeconds(4) ? 150 : 300, ct);
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
        // 私服：头顶没有图标时的寻找状态
        var flowerSearch = new PrivateServerFlowerSearchState();

        while (!ct.IsCancellationRequested)
        {
            ct.ThrowIfCancellationRequested();
            var boxRegions = page.Locator(LoadRecognitionObject("RewardBox")).FindAll();
            if (boxRegions.Count < 1)
            {
                // 私服：转了一圈仍没有头顶图标时，改为按征讨之花的红色花纹寻找
                if (PrivateServerFindFlowerWithoutIcon
                    && await PrivateServerSteerToFlowerWithoutIcon(flowerSearch, centerX, ct))
                {
                    continue;
                }

                _logger.LogWarning("{Name}：未找到征讨之花图标，调整视角重试", Name);
                Simulation.SendInput.Mouse.MoveMouseBy(ScaleX(200), 0);
                await Delay(250, ct);
                continue;
            }

            var icon = boxRegions[0];
            Interlocked.Exchange(ref _psRewardTargetSeenTicks, DateTime.UtcNow.Ticks);
            flowerSearch.ResetRotation();

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

                // 私服：已经看到“接触征讨之花”提示时原地停下，等交互结果（本周次数用完时不会弹出领奖界面，继续往前走、跳会走过头）
                if (DateTime.UtcNow.Ticks - Interlocked.Read(ref _psRewardPromptSeenTicks) < TimeSpan.FromSeconds(3).Ticks)
                {
                    if (isMovingForward)
                    {
                        Simulation.SendInput.SimulateAction(GIActions.MoveForward, KeyType.KeyUp);
                        isMovingForward = false;
                    }

                    await Delay(200, ct);
                    continue;
                }

                // 私服：还没看到征讨之花（头顶图标或红色花纹）时先原地转视角寻找，不盲目往前走
                if (PrivateServerFindFlowerWithoutIcon && !_psRewardBlindWalk
                    && DateTime.UtcNow.Ticks - Interlocked.Read(ref _psRewardTargetSeenTicks) > TimeSpan.FromSeconds(1.5).Ticks)
                {
                    if (isMovingForward)
                    {
                        Simulation.SendInput.SimulateAction(GIActions.MoveForward, KeyType.KeyUp);
                        isMovingForward = false;
                    }

                    await Delay(200, ct);
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

            if (HasWeeklyLimitToast(page))
            {
                // 私服：提示“本周收取该宝藏次数已耗尽”
                _psWeeklyLimitReached = true;
            }

            await CloseResinSupplementPrompt(page);
            await _returnMainUiTask.Start(_ct);
            return false;
        }

        await TryRecognizeRewardResult(page);
        if (PrivateServerSafeCloseRewardResult)
        {
            // 私服：点击“点击空白区域继续”这行字关闭奖励结果页，不点击画面中间的奖励图标（会弹出物品详情而卡住）
            await PrivateServerCloseRewardResult(page);
        }
        else
        {
            await CloseRewardResult();
        }

        if (_psWeeklyLimitReached)
        {
            return false;
        }

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

    /// <summary>“获得”界面 / 领奖结果页顶部“获得”标题区域。</summary>
    private Rect PrivateServerObtainTitleRect => ScaleRect(840, 240, 240, 110);

    /// <summary>
    /// “点击空白区域继续”文字的查找范围：画面下半部分的一大块区域（奖励图标下方）。
    /// 私服上这行字紧挨在图标下方（y≈748），官方版在画面最下方（y≈977），两种位置都能找到。
    /// </summary>
    private Rect PrivateServerObtainHintRect => ScaleRect(460, 680, 1000, 390);

    /// <summary>找不到“点击空白区域继续”时点击的空白处（1080P 坐标）：在奖励图标下方，不会点到任何图标。</summary>
    private const int PrivateServerBlankClickX = 960;

    /// <summary>找不到“点击空白区域继续”时点击的空白处（1080P 坐标）。</summary>
    private const int PrivateServerBlankClickY = 900;

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
                    page.Click(PrivateServerBlankClickX, PrivateServerBlankClickY);
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
            // 私服：每天凌晨 4 点弹出的空月祝福界面，先领取（不然会被当成未知界面按 ESC）
            if (await PrivateServerTryClaimWelkinMoonNow())
            {
                unknownTimes = 0;
                continue;
            }

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
                    page.Click(PrivateServerBlankClickX, PrivateServerBlankClickY);
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

    /// <summary>
    /// 关闭领奖结果页（私服版）。
    /// 原来的关闭方法只在画面最下方找“点击空白区域继续”，私服上这行字在奖励图标正下方，找不到时它会点击屏幕正中间，
    /// 正好点到奖励图标、弹出物品详情，任务就卡住了。
    /// 这里改为：在画面下半部分的大范围内找这行字并点击它；一直找不到时，只点击奖励图标下方的空白处，绝不点击画面中间。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <exception cref="Exception">30 秒内仍未回到游戏主界面时抛出（和原来一样结束任务）。</exception>
    private async Task PrivateServerCloseRewardResult(BvPage page)
    {
        var stopwatch = Stopwatch.StartNew();
        var seenResult = false;
        var mainUiTimes = 0;
        var lastBlankClick = TimeSpan.Zero;

        while (stopwatch.Elapsed < TimeSpan.FromSeconds(30))
        {
            _ct.ThrowIfCancellationRequested();
            using (var capture = CaptureToRectArea())
            {
                var hint = FindOcrText(capture, PrivateServerObtainHintRect, "空白区域");
                if (hint != null)
                {
                    // 点击“点击空白区域继续”这行字
                    seenResult = true;
                    mainUiTimes = 0;
                    hint.Click();
                    await Delay(1000, _ct);
                    continue;
                }

                var hasTitle = FindOcrText(capture, PrivateServerObtainTitleRect, "获得") != null;
                if (hasTitle)
                {
                    seenResult = true;
                }

                if (!seenResult && !_psWeeklyLimitReached && HasWeeklyLimitToast(capture))
                {
                    // 私服：领奖时提示“本周收取该宝藏次数已耗尽”（没有发放奖励）
                    _psWeeklyLimitReached = true;
                    _logger.LogInformation("{Name}：领奖时提示“本周收取该宝藏次数已耗尽”", Name);
                }

                if (!hasTitle && Bv.IsInMainUi(capture)
                              && FindOcrText(capture, PrivateServerRewardButtonRect, "原粹树脂") == null)
                {
                    // 已经看到过奖励结果页：连续 2 次确认回到游戏主界面即可；
                    // 还没看到过：奖励结果页可能还没弹出来，多等一会儿再确认
                    mainUiTimes++;
                    if ((seenResult && mainUiTimes >= 2) || mainUiTimes >= 8)
                    {
                        return;
                    }
                }
                else
                {
                    mainUiTimes = 0;

                    // 不在游戏主界面，又找不到“点击空白区域继续”：先等奖励动画播完；
                    // 超过 5 秒后，每隔约 1.5 秒点击一次奖励图标下方的空白处（万一弹出了物品详情，也能把它关掉）
                    if (stopwatch.Elapsed > TimeSpan.FromSeconds(5)
                        && stopwatch.Elapsed - lastBlankClick > TimeSpan.FromMilliseconds(1500))
                    {
                        _logger.LogInformation("{Name}：未识别到“点击空白区域继续”，点击奖励下方的空白处", Name);
                        page.Click(PrivateServerBlankClickX, PrivateServerBlankClickY);
                        lastBlankClick = stopwatch.Elapsed;
                    }
                }
            }

            await Delay(300, _ct);
        }

        using var finalCapture = CaptureToRectArea();
        if (!Bv.IsInMainUi(finalCapture))
        {
            throw new Exception("领取奖励后未成功回到主界面");
        }
    }

    // ==================== 私服补充树脂（自定义修改）结束 ====================

    // ==================== 私服首领轮换 / 寻找无图标征讨之花（自定义修改）开始 ====================

    // ---------- 界面坐标（1080P 基准，按用户截图测量） ----------

    /// <summary>
    /// “本周收取该宝藏次数已耗尽”提示的识别区域（画面上方中间，1080P）。
    /// 这个提示是没有底框的白字，位置可能上下浮动，所以范围放宽（第 8 版：原来是 610, 175, 700, 80）。
    /// </summary>
    private static readonly Rect PrivateServerWeeklyLimitToastRect = new(480, 110, 960, 220);

    /// <summary>提示文字里的关键词，认出任意一个就算（文字识别有时只能认出一部分）。</summary>
    private static readonly string[] PrivateServerWeeklyLimitKeywords = ["耗尽", "收取该宝藏", "宝藏次数", "次数已耗"];

    /// <summary>在征讨之花前按交互键后，等多久还没有领奖界面才再按一次（毫秒）。</summary>
    private const int PrivateServerInteractRetryMs = 2500;

    /// <summary>按了几次交互键都没有弹出领奖界面（也没认出提示文字）时，按“本周次数已用完”处理。</summary>
    private const int PrivateServerUnansweredInteractLimit = 3;

    /// <summary>冒险之证最左侧一栏（见闻/委托/秘境/讨伐/向导/备战）的识别区域。</summary>
    private static readonly Rect PrivateServerHandbookTabRect = new(200, 190, 200, 600);

    /// <summary>讨伐页左页上方筛选下拉框当前值（全部/普通/精英/首领/其他）的识别区域。</summary>
    private static readonly Rect PrivateServerHandbookFilterRect = new(390, 180, 250, 50);

    /// <summary>筛选下拉框展开后选项列表的识别区域。</summary>
    private static readonly Rect PrivateServerHandbookFilterListRect = new(390, 232, 250, 280);

    /// <summary>冒险之证右页上方首领名字的识别区域。</summary>
    private static readonly Rect PrivateServerHandbookTitleRect = new(1030, 245, 560, 65);

    /// <summary>冒险之证右页“前往”按钮的识别区域。</summary>
    private static readonly Rect PrivateServerHandbookGotoRect = new(1380, 800, 200, 85);

    /// <summary>大地图右侧首领面板“传送并追踪”按钮的识别区域。</summary>
    private static readonly Rect PrivateServerMapTeleportTrackRect = new(1560, 960, 340, 90);

    /// <summary>筛选下拉框的所有选项。</summary>
    private static readonly string[] PrivateServerHandbookFilterNames = ["全部", "普通", "精英", "首领", "其他"];

    /// <summary>首领列表三列图标中心的 X 坐标。</summary>
    private static readonly int[] PrivateServerGridColumnX = [500, 682, 865];

    /// <summary>首领列表相邻两行图标中心的垂直距离。</summary>
    private const int PrivateServerGridRowPitch = 164;

    /// <summary>首领列表可见区域的上边界。</summary>
    private const int PrivateServerGridTop = 245;

    /// <summary>首领列表可见区域的下边界。</summary>
    private const int PrivateServerGridBottom = 885;

    /// <summary>点击图标前，图标中心需要在这个范围内（完整可见）。</summary>
    private const int PrivateServerGridSafeTop = 300;

    /// <summary>点击图标前，图标中心需要在这个范围内（完整可见）。</summary>
    private const int PrivateServerGridSafeBottom = 800;

    /// <summary>用来判断首领列表滚动了多少的区域。</summary>
    private static readonly Rect PrivateServerGridScrollRect = new(405, 250, 540, 630);

    /// <summary>红框（当前选中的首领）所在圆环的半径。</summary>
    private static readonly int[] PrivateServerRingRadii = [66, 68, 70];

    /// <summary>识别征讨之花红色花纹时忽略的区域：上方按钮、小地图、队伍列表、下方血条/技能、角色本身。</summary>
    private static readonly Rect[] PrivateServerFlowerIgnoreRects =
    [
        new(0, 0, 1920, 110), new(0, 0, 330, 320), new(1560, 230, 360, 400),
        new(0, 960, 1920, 120), new(1600, 880, 320, 200), new(840, 280, 240, 700)
    ];

    /// <summary>按红色花纹找花时，把花放在画面的这个位置（相对画面中心的比例：1180/960，即角色右侧一点）。</summary>
    private const double PrivateServerFlowerAimRatio = 1180.0 / 960.0;

    /// <summary>花在这个范围内（1080P 下 x 1100～1260）时不再转动视角。</summary>
    private const double PrivateServerFlowerAimMinRatio = 1100.0 / 960.0;

    /// <summary>花在这个范围内（1080P 下 x 1100～1260）时不再转动视角。</summary>
    private const double PrivateServerFlowerAimMaxRatio = 1260.0 / 960.0;

    /// <summary>判定为征讨之花所需的最少红色像素（在缩小到 960×540 的画面上统计）。</summary>
    private const int PrivateServerFlowerMinRedPixels = 60;

    /// <summary>识别首领名字时忽略的符号（OCR 可能把“·”认成其他点号）。</summary>
    private const string PrivateServerNameIgnoredChars = "·・•．.。‧∙⋅･-－—「」『』\"'“”";

    private enum PrivateServerHandbookStepResult
    {
        Selected,
        EndOfList,
        Failed
    }

    private readonly record struct PrivateServerGridCell(int Col, double Y, double Score);

    private readonly record struct PrivateServerHandbookStep(PrivateServerHandbookStepResult Result, int Col, double Y);

    /// <summary>冒险之证“前往”→“传送并追踪”的结果。</summary>
    private enum PrivateServerTeleportResult
    {
        /// <summary>已传送并回到游戏主界面。</summary>
        Teleported,

        /// <summary>大地图上显示“追踪并引导”：附近没有解锁的传送锚点。</summary>
        NoWaypoint,

        /// <summary>冒险之证右页没有找到“前往”（还在冒险之证里）。</summary>
        NoGotoButton,

        /// <summary>其他原因没有完成传送。</summary>
        Failed
    }

    /// <summary>冒险之证里当前选中的首领能不能刷。</summary>
    private enum PrivateServerCandidateResult
    {
        /// <summary>就刷这个首领。</summary>
        Selected,

        /// <summary>跳过，继续在冒险之证里点下一个。</summary>
        Skip,

        /// <summary>跳过，但已经离开了冒险之证（打开过大地图），需要重新打开冒险之证再点下一个。</summary>
        SkipAndReopen
    }

    /// <summary>
    /// 寻找无图标征讨之花时的状态：先转一圈找头顶图标，找不到再按红色花纹找，还找不到就边走边找。
    /// </summary>
    private sealed class PrivateServerFlowerSearchState
    {
        public bool ColorPhase;
        public double RotatedDegrees;
        public int Steps;
        public float? LastAngle;
        public DateTime LastLogAt = DateTime.MinValue;

        public void Track(float? angle)
        {
            if (angle is null)
            {
                return;
            }

            if (LastAngle is { } last)
            {
                var diff = Math.Abs(angle.Value - last) % 360;
                if (diff > 180)
                {
                    diff = 360 - diff;
                }

                // 忽略偶尔识别错误造成的大跳变
                if (diff < 90)
                {
                    RotatedDegrees += diff;
                }
            }

            LastAngle = angle;
        }

        public void ResetRotation()
        {
            RotatedDegrees = 0;
            Steps = 0;
            LastAngle = null;
        }
    }

    private Rect ScaleRect(Rect rect)
    {
        return ScaleRect(rect.X, rect.Y, rect.Width, rect.Height);
    }

    /// <summary>
    /// 画面上方中间是否显示“本周收取该宝藏次数已耗尽”。
    /// </summary>
    private bool HasWeeklyLimitToast(BvPage page)
    {
        return page.Ocr(ScaleRect(PrivateServerWeeklyLimitToastRect))
            .Any(region => PrivateServerIsWeeklyLimitText(region.Text));
    }

    /// <summary>
    /// 画面上方中间是否显示“本周收取该宝藏次数已耗尽”。
    /// </summary>
    private bool HasWeeklyLimitToast(ImageRegion capture)
    {
        return capture.FindMulti(RecognitionObject.Ocr(ScaleRect(PrivateServerWeeklyLimitToastRect)))
            .Any(region => PrivateServerIsWeeklyLimitText(region.Text));
    }

    /// <summary>识别到的文字是不是“本周收取该宝藏次数已耗尽”（含任意一个关键词）。</summary>
    private static bool PrivateServerIsWeeklyLimitText(string text)
    {
        return PrivateServerWeeklyLimitKeywords.Any(keyword => text.Contains(keyword, StringComparison.Ordinal));
    }

    /// <summary>
    /// 寻找征讨之花。
    /// 第 9 版（PrivateServerSlowScanForFlower）：原地转了几圈都没找到时，传送到首领附近的传送锚点、按 BetterGI 自带的路线重新跑到首领那里再找一次；
    /// 还找不到就设置 _psFlowerNotFound，由 RunBossLoop 换下一个首领。
    /// 关掉第 9 版时：超时找不到时（例如头顶没有图标、花在视野外），先回到首领路线终点附近，再找一次。
    /// </summary>
    private async Task PrivateServerNavigateToReward()
    {
        try
        {
            await NavigateToReward();
        }
        catch (TimeoutException e) when (PrivateServerSlowScanForFlower)
        {
            // 私服（第 9 版）：原地转了几圈都没找到 → 传送到首领附近的传送锚点，按 BetterGI 自带的路线重新跑到首领那里，再找一次
            _logger.LogWarning("{Name}：{Message}，传送到附近的传送锚点，按路线重新跑到首领那里再找一次", Name, e.Message);
            if (!await EnsureCleanMainUi(new BvPage(_ct), "重新跑图前"))
            {
                throw;
            }

            await NavigateToBoss();
            try
            {
                await NavigateToReward();
            }
            catch (TimeoutException again)
            {
                // 还是没找到：交给 RunBossLoop 换下一个首领
                _logger.LogWarning("{Name}：{Message}，重新跑图后还是没有找到征讨之花", Name, again.Message);
                _psFlowerNotFound = true;
            }
        }
        catch (TimeoutException e) when (PrivateServerFindFlowerWithoutIcon && !AutoBossData.IsNoPathingSupportBoss(_taskParam.BossName))
        {
            _logger.LogWarning("{Name}：{Message}，回到首领位置后再找一次征讨之花", Name, e.Message);
            if (!await EnsureCleanMainUi(new BvPage(_ct), "重新寻找征讨之花前"))
            {
                throw;
            }

            await PrivateServerWalkToBossPosition();
            await NavigateToReward();
        }
    }

    /// <summary>
    /// 走到当前首领“前往”路线的终点（首领所在位置）。
    /// </summary>
    private async Task PrivateServerWalkToBossPosition()
    {
        var routePath = BuildPathingAssetPath($"{_taskParam.BossName}前往.json");
        var originalTask = PathingTask.BuildFromFilePath(routePath) ?? throw new Exception($"路径文件解析失败：{routePath}");
        var lastPosition = originalTask.Positions.LastOrDefault() ?? throw new Exception("路线文件缺少路径点");
        var walkTask = new PathingTask
        {
            Info = originalTask.Info,
            Config = originalTask.Config,
            Positions = [lastPosition]
        };

        _logger.LogInformation("{Name}：回到 {Boss} 的位置", Name, _taskParam.BossName);
        await RunPathingTask(walkTask);
    }

    /// <summary>
    /// 头顶图标找不到时的处理。返回 true 表示已经按红色花纹调整了视角（调用方继续下一轮）；
    /// 返回 false 表示调用方按原来的方式转动视角继续找。
    /// </summary>
    private async Task<bool> PrivateServerSteerToFlowerWithoutIcon(PrivateServerFlowerSearchState state, double centerX, CancellationToken ct)
    {
        using var capture = CaptureToRectArea();
        state.Track(PrivateServerTryGetCameraAngle(capture));
        state.Steps++;
        var fullTurn = state.RotatedDegrees >= 360 || state.Steps >= 50;

        if (!state.ColorPhase)
        {
            if (!fullTurn)
            {
                // 先像原来一样转一圈找头顶的图标
                return false;
            }

            state.ColorPhase = true;
            state.ResetRotation();
            fullTurn = false;
            _logger.LogInformation("{Name}：转了一圈没有找到征讨之花头顶的图标，改为按征讨之花的红色花纹寻找", Name);
        }

        if (PrivateServerTryFindFlowerByColor(capture, out var flowerX, out var redPixels))
        {
            Interlocked.Exchange(ref _psRewardTargetSeenTicks, DateTime.UtcNow.Ticks);
            state.ResetRotation();
            if (DateTime.UtcNow - state.LastLogAt > TimeSpan.FromSeconds(3))
            {
                state.LastLogAt = DateTime.UtcNow;
                _logger.LogInformation("{Name}：按红色花纹找到了征讨之花（{Pixels} 个红色像素），正在靠近", Name, redPixels);
            }

            // 花是场景里的实物，正对画面中间时会被角色挡住（角色所在区域也不参与识别），
            // 所以把花放在角色右侧一点（1080P 下 x≈1180）再往前走，角色会绕一个小弧线走到花跟前
            var aimX = centerX * PrivateServerFlowerAimRatio;
            if (flowerX < centerX * PrivateServerFlowerAimMinRatio || flowerX > centerX * PrivateServerFlowerAimMaxRatio)
            {
                Simulation.SendInput.Mouse.MoveMouseBy((int)Math.Round(flowerX - aimX), 0);
            }

            await Delay(250, ct);
            return true;
        }

        if (fullTurn && !_psRewardBlindWalk)
        {
            _psRewardBlindWalk = true;
            _logger.LogWarning("{Name}：附近也没有找到征讨之花的红色花纹，改为边转视角边往前走寻找", Name);
        }

        return false;
    }

    private static float? PrivateServerTryGetCameraAngle(ImageRegion capture)
    {
        try
        {
            return BetterGenshinImpact.GameTask.Common.Map.CameraOrientation.Compute(capture.SrcMat);
        }
        catch
        {
            return null;
        }
    }

    /// <summary>
    /// 按征讨之花茎和花苞上的暗红色花纹寻找征讨之花（头顶没有图标时使用）。
    /// 忽略界面按钮、小地图、队伍列表和角色本身所在的区域；红色像素需要足够多且集中在一处。
    /// </summary>
    /// <param name="capture">当前截图。</param>
    /// <param name="targetX">征讨之花在截图中的 X 坐标。</param>
    /// <param name="redPixels">红色像素数量（缩小到 960×540 后统计）。</param>
    private static bool PrivateServerTryFindFlowerByColor(ImageRegion capture, out double targetX, out int redPixels)
    {
        targetX = 0;
        redPixels = 0;
        var src = capture.SrcMat;
        if (src.Empty() || src.Width < 2 || src.Height < 2)
        {
            return false;
        }

        using var bgr = PrivateServerCropBgr(src, new Rect(0, 0, src.Width, src.Height));
        using var small = new Mat();
        Cv2.Resize(bgr, small, new Size(bgr.Width / 2, bgr.Height / 2), 0, 0, InterpolationFlags.Area);
        using var hsv = new Mat();
        Cv2.CvtColor(small, hsv, ColorConversionCodes.BGR2HSV);
        using var low = new Mat();
        using var high = new Mat();
        using var mask = new Mat();
        Cv2.InRange(hsv, new Scalar(0, 90, 45), new Scalar(8, 255, 230), low);
        Cv2.InRange(hsv, new Scalar(165, 90, 45), new Scalar(180, 255, 230), high);
        Cv2.BitwiseOr(low, high, mask);

        // 1080P 坐标 → 缩小后的坐标
        var k = small.Width / 1920.0;
        var bounds = new Rect(0, 0, mask.Width, mask.Height);
        foreach (var r in PrivateServerFlowerIgnoreRects)
        {
            var scaled = new Rect((int)(r.X * k), (int)(r.Y * k), (int)Math.Ceiling(r.Width * k) + 1, (int)Math.Ceiling(r.Height * k) + 1) & bounds;
            if (scaled.Width <= 0 || scaled.Height <= 0)
            {
                continue;
            }

            using var sub = new Mat(mask, scaled);
            sub.SetTo(Scalar.Black);
        }

        redPixels = Cv2.CountNonZero(mask);
        var minPixels = (int)Math.Round(PrivateServerFlowerMinRedPixels * k * k * 4);
        if (redPixels < Math.Max(minPixels, 20))
        {
            return false;
        }

        using var points = new Mat();
        Cv2.FindNonZero(mask, points);
        if (points.Empty())
        {
            return false;
        }

        points.GetArray(out Point[] pts);
        if (pts.Length == 0)
        {
            return false;
        }

        var meanX = pts.Average(p => (double)p.X);
        var band = 160 * k;
        var concentrated = pts.Count(p => Math.Abs(p.X - meanX) <= band) / (double)pts.Length;
        if (concentrated < 0.6)
        {
            return false;
        }

        targetX = meanX / small.Width * src.Width;
        return true;
    }

    /// <summary>
    /// 从截图中裁剪一块区域并统一转成 3 通道 BGR。
    /// </summary>
    private static Mat PrivateServerCropBgr(Mat src, Rect rect)
    {
        using var crop = new Mat(src, rect);
        var bgr = new Mat();
        if (crop.Channels() == 4)
        {
            Cv2.CvtColor(crop, bgr, ColorConversionCodes.BGRA2BGR);
        }
        else if (crop.Channels() == 1)
        {
            Cv2.CvtColor(crop, bgr, ColorConversionCodes.GRAY2BGR);
        }
        else
        {
            crop.CopyTo(bgr);
        }

        return bgr;
    }

    /// <summary>
    /// 本周该首领的领取次数已用完：开启首领轮换时，按冒险之证顺序换下一个首领；否则结束任务。
    /// </summary>
    /// <returns>已换到下一个首领时返回 true；需要结束任务时返回 false。</returns>
    private async Task<bool> PrivateServerHandleWeeklyLimit()
    {
        _psWeeklyLimitReached = false;
        _logger.LogInformation("{Name}：{Boss} 本周的领取次数已用完（本周收取该宝藏次数已耗尽）", Name, _taskParam.BossName);
        if (!PrivateServerBossRotation)
        {
            _logger.LogInformation("{Name}：没有开启首领轮换，结束任务", Name);
            return false;
        }

        var nextBoss = await PrivateServerSelectBossInHandbook(advance: true);
        if (nextBoss == null)
        {
            return false;
        }

        _logger.LogInformation("{Name}：换成讨伐 {Boss}", Name, nextBoss);
        _taskParam.BossName = nextBoss;
        return true;
    }

    /// <summary>
    /// 任务开始时，从冒险之证红框标记的首领开始讨伐。
    /// </summary>
    private async Task PrivateServerPickStartBossFromHandbook()
    {
        _logger.LogInformation("{Name}：打开冒险之证，从红框标记的首领开始讨伐", Name);
        var boss = await PrivateServerSelectBossInHandbook(advance: false);
        if (boss == null)
        {
            _logger.LogWarning("{Name}：没能从冒险之证确定要讨伐的首领，继续讨伐界面里选择的首领：{Boss}", Name, _taskParam.BossName);
            return;
        }

        if (boss != _taskParam.BossName)
        {
            _logger.LogInformation("{Name}：冒险之证红框标记的首领是 {Boss}，改为讨伐它（界面里选择的是 {UiBoss}）", Name, boss, _taskParam.BossName);
        }

        _taskParam.BossName = boss;
    }

    /// <summary>
    /// 在冒险之证“讨伐 → 首领”列表里选择要讨伐的首领，并（按开关）点击“前往”→“传送并追踪”。
    /// 会跳过：需要先完成前置任务的、在跳过名单里的、BetterGI 不支持的、附近没有解锁传送锚点的首领。
    /// </summary>
    /// <param name="advance">false：使用红框标记的首领（不能刷时往后找）；true：从红框标记的下一个首领开始找。</param>
    /// <returns>选中的首领名称；列表已经到末尾或操作失败时返回 null。</returns>
    private async Task<string?> PrivateServerSelectBossInHandbook(bool advance)
    {
        var skipList = PrivateServerLoadSkippedBosses();
        var reopened = false;
        string? cappedBoss = null;
        var welkinRetries = 0;
        for (var attempt = 0; attempt < 40; attempt++)
        {
            var welkinTicks = Interlocked.Read(ref _psWelkinHandledTicks);
            _psHandbookFailed = false;
            var (reopen, boss) = await PrivateServerSelectBossInHandbookOnce(advance, reopened, skipList, cappedBoss);
            if (!reopen && boss == null && _psHandbookFailed && welkinRetries < 2
                && Interlocked.Read(ref _psWelkinHandledTicks) != welkinTicks)
            {
                // 私服：冒险之证操作被空月祝福界面打断（已经自动领取），重新打开冒险之证，从红框标记的首领继续
                welkinRetries++;
                _logger.LogInformation("{Name}：冒险之证操作被空月祝福界面打断，重新打开冒险之证继续", Name);
                if (advance && !reopened)
                {
                    // 本周已讨伐完毕的首领：重新打开时如果红框还停在它上面，就从它的下一个开始找
                    cappedBoss = _taskParam.BossName;
                }

                advance = false;
                continue;
            }

            if (!reopen)
            {
                return boss;
            }

            // 刚才的首领附近没有解锁的传送锚点：大地图已经关掉，红框停在这个首领上，重新打开冒险之证从它的下一个开始找
            advance = true;
            reopened = true;
        }

        _logger.LogWarning("{Name}：连续跳过的首领太多，停止在冒险之证里寻找", Name);
        return null;
    }

    /// <summary>
    /// 打开一次冒险之证选择首领，结束时关闭冒险之证 / 大地图回到游戏主界面。
    /// </summary>
    /// <returns>Reopen 为 true：刚才的首领附近没有解锁的传送锚点，需要重新打开冒险之证继续找；
    /// 否则 Boss 为选中的首领（null 表示列表已经到末尾或操作失败）。</returns>
    /// <param name="cappedBoss">被空月祝福打断后重新打开时，本周已讨伐完毕的首领：红框还停在它上面时从它的下一个开始找。</param>
    private async Task<(bool Reopen, string? Boss)> PrivateServerSelectBossInHandbookOnce(bool advance, bool reopened, IReadOnlyList<string> skipList,
        string? cappedBoss = null)
    {
        // 私服：冒险之证是自己的界面操作，这期间后台检查不把原石图标当作空月祝福的“获得”界面
        using var psOwnUi = PrivateServerEnterOwnUi();
        var page = new BvPage(_ct);
        try
        {
            if (!await PrivateServerOpenHandbookBossList(page))
            {
                _logger.LogWarning("{Name}：打开冒险之证首领列表失败", Name);
                _psHandbookFailed = true;
                return (false, null);
            }

            var title = await PrivateServerReadHandbookTitle(null);
            _logger.LogInformation("{Name}：冒险之证当前红框标记的首领：{Title}", Name, title ?? "（没有识别到名字）");

            if (!advance)
            {
                var redBoss = title == null ? null : PrivateServerMatchSupportedBoss(title);
                if (cappedBoss != null && redBoss == cappedBoss)
                {
                    // 被空月祝福打断后重新打开：红框还停在本周已讨伐完毕的首领上，从它的下一个开始找
                    _logger.LogInformation("{Name}：红框还停在本周已讨伐完毕的 {Boss} 上，从它的下一个开始找", Name, cappedBoss);
                }
                else
                {
                    var first = await PrivateServerEvaluateHandbookCandidate(page, title, skipList, isNext: false);
                    if (first.Result == PrivateServerCandidateResult.Selected)
                    {
                        return (false, first.Boss);
                    }

                    if (first.Result == PrivateServerCandidateResult.SkipAndReopen)
                    {
                        return (true, null);
                    }
                }
            }
            else if (!reopened)
            {
                var titleBoss = title == null ? null : PrivateServerMatchSupportedBoss(title);
                if (titleBoss != null && titleBoss != _taskParam.BossName)
                {
                    _logger.LogWarning("{Name}：冒险之证红框标记的首领（{Title}）和刚才讨伐的首领（{Boss}）不一样，按红框的顺序继续", Name, titleBoss, _taskParam.BossName);
                }
            }

            var selected = await PrivateServerLocateSelectedCell();
            if (selected == null)
            {
                _logger.LogWarning("{Name}：冒险之证首领列表里找不到红框标记的首领", Name);
                _psHandbookFailed = true;
                return (false, null);
            }

            var (col, y) = selected.Value;
            var previousTitle = title;
            for (var i = 0; i < 80; i++)
            {
                var step = await PrivateServerSelectNextCell(page, col, y);
                if (step.Result == PrivateServerHandbookStepResult.EndOfList)
                {
                    if (advance)
                    {
                        _logger.LogInformation("{Name}：已经是冒险之证首领列表的最后一个了，列表里的首领本周都已讨伐完毕（不能刷的首领已跳过），结束任务", Name);
                    }
                    else
                    {
                        _logger.LogInformation("{Name}：冒险之证首领列表里，红框之后已经没有能刷的首领了", Name);
                    }

                    return (false, null);
                }

                if (step.Result == PrivateServerHandbookStepResult.Failed)
                {
                    _logger.LogWarning("{Name}：在冒险之证里选择下一个首领失败", Name);
                    _psHandbookFailed = true;
                    return (false, null);
                }

                (col, y) = (step.Col, step.Y);
                var name = await PrivateServerReadHandbookTitle(previousTitle);
                if (name != null)
                {
                    previousTitle = name;
                }

                var candidate = await PrivateServerEvaluateHandbookCandidate(page, name, skipList, isNext: true);
                if (candidate.Result == PrivateServerCandidateResult.Selected)
                {
                    return (false, candidate.Boss);
                }

                if (candidate.Result == PrivateServerCandidateResult.SkipAndReopen)
                {
                    return (true, null);
                }
            }

            return (false, null);
        }
        catch (Exception e) when (e is not (OperationCanceledException or NormalEndException or RetryException))
        {
            _logger.LogWarning("{Name}：冒险之证操作出错：{Message}", Name, e.Message);
            _psHandbookFailed = true;
            return (false, null);
        }
        finally
        {
            // 关闭冒险之证 / 大地图，回到游戏主界面
            if (!_ct.IsCancellationRequested)
            {
                await EnsureCleanMainUi(page, "冒险之证操作结束后");
            }
        }
    }

    private bool PrivateServerRouteFilesExist(string boss)
    {
        return GetRequiredRouteFiles(boss).All(route => File.Exists(BuildPathingAssetPath(route)));
    }

    /// <summary>
    /// 判断冒险之证当前选中的首领能不能刷。需要先完成前置任务的、在跳过名单里的、BetterGI 不支持的、缺少路线文件的首领直接跳过；
    /// 能刷时（按开关）点击“前往”→“传送并追踪”。大地图上显示“追踪并引导”（附近没有解锁的传送锚点）时也跳过。
    /// </summary>
    /// <param name="page">当前页面。</param>
    /// <param name="title">右页识别到的首领名字（没有识别到时为 null）。</param>
    /// <param name="skipList">跳过名单。</param>
    /// <param name="isNext">是否是红框之后的首领（只影响日志）。</param>
    private async Task<(PrivateServerCandidateResult Result, string? Boss)> PrivateServerEvaluateHandbookCandidate(BvPage page, string? title,
        IReadOnlyList<string> skipList, bool isNext)
    {
        // 右页下方的按钮是“前置任务”而不是“前往”：还没有完成前置任务（这种首领的名字也显示成问号）
        var buttonText = await PrivateServerWaitText(PrivateServerHandbookGotoRect, ["前往", "前置"], 1500, click: false);
        if (buttonText != null && buttonText.Contains("前置", StringComparison.Ordinal))
        {
            _logger.LogInformation("{Name}：跳过需要先完成前置任务的首领：{Title}", Name, title ?? "（名字还没解锁）");
            return (PrivateServerCandidateResult.Skip, null);
        }

        var boss = title == null ? null : PrivateServerMatchSupportedBoss(title);
        if (PrivateServerFindSkipKeyword(skipList, title, boss) != null)
        {
            _logger.LogInformation("{Name}：按跳过名单跳过首领：{Title}", Name, boss ?? title);
            return (PrivateServerCandidateResult.Skip, null);
        }

        if (boss == null)
        {
            _logger.LogInformation("{Name}：跳过 BetterGI 暂不支持的首领：{Title}", Name, title ?? "（没有识别到名字）");
            return (PrivateServerCandidateResult.Skip, null);
        }

        if (!PrivateServerRouteFilesExist(boss))
        {
            _logger.LogInformation("{Name}：跳过缺少路线文件的首领：{Boss}", Name, boss);
            return (PrivateServerCandidateResult.Skip, null);
        }

        if (isNext)
        {
            _logger.LogInformation("{Name}：冒险之证已选中下一个首领：{Boss}", Name, boss);
        }

        if (!PrivateServerHandbookTeleportAndTrack)
        {
            return (PrivateServerCandidateResult.Selected, boss);
        }

        var teleport = await PrivateServerClickGotoAndTeleport(page);
        if (teleport == PrivateServerTeleportResult.NoWaypoint)
        {
            _logger.LogInformation("{Name}：{Boss} 附近没有解锁的传送锚点（大地图上显示“追踪并引导”），跳过，回到冒险之证选下一个", Name, boss);
            return (PrivateServerCandidateResult.SkipAndReopen, null);
        }

        if (teleport == PrivateServerTeleportResult.Teleported)
        {
            _logger.LogInformation("{Name}：已通过冒险之证“传送并追踪” {Boss}", Name, boss);
        }
        else
        {
            _logger.LogWarning("{Name}：冒险之证“传送并追踪”没有完成，直接用 BetterGI 自带的路线前往 {Boss}", Name, boss);
        }

        return (PrivateServerCandidateResult.Selected, boss);
    }

    /// <summary>
    /// 读取跳过首领名单（User\私服跳过的首领.txt）。文件不存在时按默认内容创建；读取失败时使用默认名单。
    /// 每次换首领时都会重新读取，所以运行中修改名单也会在下次换首领时生效。
    /// </summary>
    private IReadOnlyList<string> PrivateServerLoadSkippedBosses()
    {
        var path = Global.Absolute(PrivateServerSkippedBossFileName);
        IEnumerable<string> lines;
        try
        {
            if (!File.Exists(path))
            {
                Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                File.WriteAllText(path, string.Join("\r\n", PrivateServerSkippedBossFileDefaultLines) + "\r\n", new System.Text.UTF8Encoding(true));
                _logger.LogInformation("{Name}：已创建跳过首领名单：{Path}", Name, path);
            }

            lines = File.ReadAllLines(path);
        }
        catch (Exception e)
        {
            _logger.LogWarning("{Name}：读取跳过首领名单失败（{Message}），使用默认名单", Name, e.Message);
            lines = PrivateServerSkippedBossFileDefaultLines;
        }

        var list = PrivateServerParseSkippedBosses(lines);
        if (!_psSkipListLogged)
        {
            _psSkipListLogged = true;
            _logger.LogInformation("{Name}：首领轮换会跳过这些首领：{List}（名单可以用记事本修改：{Path}）", Name,
                list.Count == 0 ? "（无）" : string.Join("、", list), path);
        }

        return list;
    }

    /// <summary>
    /// 解析跳过名单：每行一个名字，# 或 ＃ 后面的内容不生效；忽略空格和“·”等符号；少于 2 个字的忽略。
    /// </summary>
    private static List<string> PrivateServerParseSkippedBosses(IEnumerable<string> lines)
    {
        var list = new List<string>();
        foreach (var line in lines)
        {
            var text = line;
            var comment = text.IndexOfAny(new[] { '#', '＃' });
            if (comment >= 0)
            {
                text = text[..comment];
            }

            var name = PrivateServerNormalizeBossName(text);
            if (name.Length >= 2 && !list.Contains(name))
            {
                list.Add(name);
            }
        }

        return list;
    }

    /// <summary>
    /// 冒险之证里的名字或对应的 BetterGI 首领名称包含跳过名单里的某一项时，返回这一项；否则返回 null。
    /// </summary>
    private static string? PrivateServerFindSkipKeyword(IReadOnlyList<string> keywords, string? title, string? boss)
    {
        var normalizedTitle = title == null ? string.Empty : PrivateServerNormalizeBossName(title);
        var normalizedBoss = boss == null ? string.Empty : PrivateServerNormalizeBossName(boss);
        foreach (var keyword in keywords)
        {
            if ((normalizedTitle.Length > 0 && normalizedTitle.Contains(keyword, StringComparison.Ordinal))
                || (normalizedBoss.Length > 0 && normalizedBoss.Contains(keyword, StringComparison.Ordinal)))
            {
                return keyword;
            }
        }

        return null;
    }

    /// <summary>
    /// 打开冒险之证 → 点击最左侧的“讨伐” → 左页上方的下拉框选择“首领”。
    /// </summary>
    private async Task<bool> PrivateServerOpenHandbookBossList(BvPage page)
    {
        if (!await EnsureCleanMainUi(page, "打开冒险之证前"))
        {
            return false;
        }

        var tabClicked = false;
        for (var attempt = 0; attempt < 3 && !tabClicked; attempt++)
        {
            if (attempt == 1)
            {
                // 私服：第二次直接按 F1（防止 BetterGI 的按键设置和游戏里不一样）
                page.Keyboard.KeyPress(User32.VK.VK_F1);
            }
            else
            {
                Simulation.SendInput.SimulateAction(GIActions.OpenAdventurerHandbook);
            }

            await Delay(1000, _ct);
            tabClicked = await PrivateServerWaitText(PrivateServerHandbookTabRect, ["讨伐"], 5000, click: true) != null;
            if (!tabClicked)
            {
                _logger.LogInformation("{Name}：第 {Attempt} 次打开冒险之证后没有找到“讨伐”", Name, attempt + 1);
                if (attempt < 2 && !await EnsureCleanMainUi(page, "重新打开冒险之证前"))
                {
                    return false;
                }
            }
        }

        if (!tabClicked)
        {
            // 私服：记录画面左侧认出的文字，方便排查
            string seen;
            using (var capture = CaptureToRectArea())
            {
                seen = string.Join("、", capture.FindMulti(RecognitionObject.Ocr(ScaleRect(PrivateServerHandbookTabRect)))
                    .Select(region => region.Text).Take(8));
            }

            _logger.LogWarning("{Name}：没有找到冒险之证最左侧的“讨伐”（画面左侧认出的文字：{Texts}）", Name,
                string.IsNullOrEmpty(seen) ? "无" : seen);
            return false;
        }

        await Delay(800, _ct);
        for (var attempt = 0; attempt < 4; attempt++)
        {
            var current = await PrivateServerWaitText(PrivateServerHandbookFilterRect, PrivateServerHandbookFilterNames, 3000, click: false);
            if (current == null)
            {
                _logger.LogWarning("{Name}：没有找到讨伐页左上方的筛选下拉框", Name);
                return false;
            }

            if (current.Contains("首领", StringComparison.Ordinal))
            {
                await Delay(500, _ct);
                return true;
            }

            // 点开下拉框，选择“首领”
            await PrivateServerWaitText(PrivateServerHandbookFilterRect, PrivateServerHandbookFilterNames, 1000, click: true);
            await Delay(700, _ct);
            if (await PrivateServerWaitText(PrivateServerHandbookFilterListRect, ["首领"], 2000, click: true) != null)
            {
                await Delay(1000, _ct);
            }
        }

        _logger.LogWarning("{Name}：讨伐页的下拉框没能切换到“首领”", Name);
        return false;
    }

    /// <summary>
    /// 在区域内等待任意一个文字出现；click 为 true 时点击它。
    /// </summary>
    /// <returns>识别到的文字；超时返回 null。</returns>
    private async Task<string?> PrivateServerWaitText(Rect rect1080, IReadOnlyList<string> texts, int timeoutMs, bool click)
    {
        var stopwatch = Stopwatch.StartNew();
        while (true)
        {
            _ct.ThrowIfCancellationRequested();
            using (var capture = CaptureToRectArea())
            {
                var region = capture.FindMulti(RecognitionObject.Ocr(ScaleRect(rect1080)))
                    .FirstOrDefault(r => texts.Any(t => r.Text.Contains(t, StringComparison.Ordinal)));
                if (region != null)
                {
                    if (click)
                    {
                        region.Click();
                    }

                    return region.Text;
                }
            }

            if (stopwatch.ElapsedMilliseconds >= timeoutMs)
            {
                return null;
            }

            await Delay(300, _ct);
        }
    }

    /// <summary>
    /// 识别冒险之证右页上方的首领名字。
    /// </summary>
    /// <param name="previous">切换前的名字；不为空时会等待名字变化，3 秒内没变化返回 null。</param>
    private async Task<string?> PrivateServerReadHandbookTitle(string? previous)
    {
        string? last = null;
        for (var i = 0; i < 10; i++)
        {
            _ct.ThrowIfCancellationRequested();
            using (var capture = CaptureToRectArea())
            {
                var text = string.Concat(capture.FindMulti(RecognitionObject.Ocr(ScaleRect(PrivateServerHandbookTitleRect)))
                    .OrderBy(r => r.X)
                    .Select(r => r.Text)).Trim();
                if (!string.IsNullOrWhiteSpace(text))
                {
                    last = text;
                    if (previous == null || PrivateServerNormalizeBossName(text) != PrivateServerNormalizeBossName(previous))
                    {
                        return text;
                    }
                }
            }

            await Delay(300, _ct);
        }

        return previous == null ? last : null;
    }

    private static string PrivateServerNormalizeBossName(string text)
    {
        return new string(text.Where(ch => !char.IsWhiteSpace(ch) && !PrivateServerNameIgnoredChars.Contains(ch)).ToArray());
    }

    /// <summary>
    /// 把冒险之证里识别到的名字对应到 BetterGI 支持的首领名称。
    /// 忽略空格和“·”等符号后完全一致才算匹配；名字较长（6 个字以上）时允许 OCR 认错 1 个字。
    /// </summary>
    private static string? PrivateServerMatchSupportedBoss(string ocrText)
    {
        var text = PrivateServerNormalizeBossName(ocrText);
        if (text.Length < 2)
        {
            return null;
        }

        foreach (var boss in AutoBossData.SupportedBossNames)
        {
            if (PrivateServerNormalizeBossName(boss) == text)
            {
                return boss;
            }
        }

        string? best = null;
        var bestDistance = int.MaxValue;
        var tie = false;
        foreach (var boss in AutoBossData.SupportedBossNames)
        {
            var name = PrivateServerNormalizeBossName(boss);
            if (name.Length < 6)
            {
                continue;
            }

            var distance = PrivateServerEditDistance(name, text);
            if (distance < bestDistance)
            {
                bestDistance = distance;
                best = boss;
                tie = false;
            }
            else if (distance == bestDistance)
            {
                tie = true;
            }
        }

        return bestDistance <= 1 && !tie ? best : null;
    }

    private static int PrivateServerEditDistance(string a, string b)
    {
        var dp = new int[b.Length + 1];
        for (var j = 0; j <= b.Length; j++)
        {
            dp[j] = j;
        }

        for (var i = 1; i <= a.Length; i++)
        {
            var prev = dp[0];
            dp[0] = i;
            for (var j = 1; j <= b.Length; j++)
            {
                var temp = dp[j];
                dp[j] = Math.Min(Math.Min(dp[j] + 1, dp[j - 1] + 1), prev + (a[i - 1] == b[j - 1] ? 0 : 1));
                prev = temp;
            }
        }

        return dp[b.Length];
    }

    /// <summary>
    /// 在首领列表里找到红框（当前选中的首领）：在三列图标的位置上逐行检查图标外圈的红色圆环。
    /// </summary>
    private PrivateServerGridCell? PrivateServerFindSelectedCell(ImageRegion capture)
    {
        var src = capture.SrcMat;
        var roi = ScaleRect(380, PrivateServerGridTop - 5, 600, PrivateServerGridBottom - PrivateServerGridTop + 10) & new Rect(0, 0, src.Width, src.Height);
        if (roi.Width <= 0 || roi.Height <= 0)
        {
            return null;
        }

        using var bgr = PrivateServerCropBgr(src, roi);
        using var hsv = new Mat();
        Cv2.CvtColor(bgr, hsv, ColorConversionCodes.BGR2HSV);
        using var low = new Mat();
        using var high = new Mat();
        using var mask = new Mat();
        Cv2.InRange(hsv, new Scalar(0, 60, 110), new Scalar(12, 255, 255), low);
        Cv2.InRange(hsv, new Scalar(170, 60, 110), new Scalar(180, 255, 255), high);
        Cv2.BitwiseOr(low, high, mask);

        var best = new PrivateServerGridCell(-1, 0, 0);
        for (var col = 0; col < PrivateServerGridColumnX.Length; col++)
        {
            for (var y = PrivateServerGridTop + 12; y <= PrivateServerGridBottom - 5; y += 3)
            {
                var score = PrivateServerRingScore(mask, roi, PrivateServerGridColumnX[col], y);
                if (score > best.Score)
                {
                    best = new PrivateServerGridCell(col, y, score);
                }
            }
        }

        if (best.Col < 0)
        {
            return null;
        }

        var refined = best;
        for (var dy = -3; dy <= 3; dy++)
        {
            var score = PrivateServerRingScore(mask, roi, PrivateServerGridColumnX[best.Col], best.Y + dy);
            if (score > refined.Score)
            {
                refined = new PrivateServerGridCell(best.Col, best.Y + dy, score);
            }
        }

        return refined.Score >= 0.3 ? refined : null;
    }

    /// <summary>
    /// 计算以 (cx, cy)（1080P 坐标）为中心的圆环上红色像素的比例；跳过图标下方的等级标签和列表外的部分。
    /// </summary>
    private double PrivateServerRingScore(Mat mask, Rect roi, double cx, double cy)
    {
        var hit = 0;
        var total = 0;
        foreach (var radius in PrivateServerRingRadii)
        {
            for (var angle = 0; angle < 360; angle += 5)
            {
                var rad = angle * Math.PI / 180.0;
                var x = cx + radius * Math.Cos(rad);
                var y = cy + radius * Math.Sin(rad);
                if (y > cy + 50 || y < PrivateServerGridTop || y > PrivateServerGridBottom)
                {
                    continue;
                }

                var px = (int)Math.Round(x * AssetScale) - roi.X;
                var py = (int)Math.Round(y * AssetScale) - roi.Y;
                if (px < 0 || py < 0 || px >= mask.Width || py >= mask.Height)
                {
                    continue;
                }

                total++;
                if (mask.At<byte>(py, px) != 0)
                {
                    hit++;
                }
            }
        }

        return total >= 40 ? (double)hit / total : 0;
    }

    /// <summary>
    /// 判断首领列表某个格子里有没有首领图标（空格子是纯色背景）。
    /// </summary>
    private bool PrivateServerCellHasIcon(ImageRegion capture, int col, double y)
    {
        var src = capture.SrcMat;
        var cx = ScaleX(PrivateServerGridColumnX[col]);
        var cy = (int)Math.Round(y * AssetScale);
        var r = Math.Max(ScaleX(38), 10);
        var rect = new Rect(cx - r, cy - r, 2 * r + 1, 2 * r + 1) & new Rect(0, 0, src.Width, src.Height);
        if (rect.Width < r || rect.Height < r)
        {
            return false;
        }

        using var bgr = PrivateServerCropBgr(src, rect);
        using var gray = new Mat();
        Cv2.CvtColor(bgr, gray, ColorConversionCodes.BGR2GRAY);
        using var circle = new Mat(gray.Size(), MatType.CV_8UC1, Scalar.Black);
        Cv2.Circle(circle, new Point(cx - rect.X, cy - rect.Y), r, Scalar.White, -1);
        Cv2.MeanStdDev(gray, out _, out var stddev, circle);
        return stddev.Val0 >= 15;
    }

    /// <summary>
    /// 在首领列表上滚动鼠标滚轮。
    /// </summary>
    /// <param name="clicks">滚动格数，负数向下滚动。</param>
    /// <returns>列表内容垂直移动的距离（1080P 像素，负数表示内容向上移动）；无法判断时返回 null。</returns>
    private async Task<double?> PrivateServerScrollGrid(int clicks)
    {
        var rect = ScaleRect(PrivateServerGridScrollRect);
        using var before = PrivateServerGrabGray(rect);
        GameCaptureRegion.GameRegion1080PPosMove(682, 560);
        await Delay(150, _ct);
        Simulation.SendInput.Mouse.VerticalScroll(clicks);
        await Delay(900, _ct);
        using var after = PrivateServerGrabGray(rect);
        if (before == null || after == null || before.Size() != after.Size())
        {
            return null;
        }

        using var a = new Mat();
        using var b = new Mat();
        using var window = new Mat();
        before.ConvertTo(a, MatType.CV_32FC1);
        after.ConvertTo(b, MatType.CV_32FC1);
        var shift = Cv2.PhaseCorrelate(a, b, window, out var response);
        if (response < 0.15)
        {
            return null;
        }

        return shift.Y / AssetScale;
    }

    private Mat? PrivateServerGrabGray(Rect rect)
    {
        using var capture = CaptureToRectArea();
        var src = capture.SrcMat;
        var r = rect & new Rect(0, 0, src.Width, src.Height);
        if (r.Width <= 0 || r.Height <= 0)
        {
            return null;
        }

        using var bgr = PrivateServerCropBgr(src, r);
        var gray = new Mat();
        Cv2.CvtColor(bgr, gray, ColorConversionCodes.BGR2GRAY);
        return gray;
    }

    /// <summary>
    /// 找到红框标记的首领在列表中的位置；当前画面没有时，先往下滚动找，再往上滚动找。
    /// </summary>
    private async Task<(int Col, double Y)?> PrivateServerLocateSelectedCell()
    {
        foreach (var clicks in new[] { -2, 2 })
        {
            for (var i = 0; i < 30; i++)
            {
                using (var capture = CaptureToRectArea())
                {
                    if (PrivateServerFindSelectedCell(capture) is { } cell)
                    {
                        return (cell.Col, cell.Y);
                    }
                }

                var shift = await PrivateServerScrollGrid(clicks);
                if (shift is { } moved && Math.Abs(moved) < 3)
                {
                    // 已经滚动到底（或到顶）了，再检查一次当前画面
                    using var capture = CaptureToRectArea();
                    if (PrivateServerFindSelectedCell(capture) is { } last)
                    {
                        return (last.Col, last.Y);
                    }

                    break;
                }
            }
        }

        return null;
    }

    /// <summary>
    /// 选中红框标记的下一个首领（同一行的右边一个；已经是最右边时换到下一行的第一个），需要时先滚动列表。
    /// </summary>
    /// <param name="page">当前视觉定位页面。</param>
    /// <param name="col">当前红框所在的列（0～2）。</param>
    /// <param name="y">当前红框图标中心的 Y 坐标（1080P）。</param>
    private async Task<PrivateServerHandbookStep> PrivateServerSelectNextCell(BvPage page, int col, double y)
    {
        var targetCol = col < 2 ? col + 1 : 0;
        var rowOffset = col < 2 ? 0 : PrivateServerGridRowPitch;
        var targetY = y + rowOffset;

        // 1. 下一个图标没有完整显示时，滚动列表
        for (var i = 0; i < 25; i++)
        {
            if (targetY >= PrivateServerGridSafeTop && targetY <= PrivateServerGridSafeBottom)
            {
                break;
            }

            var down = targetY > PrivateServerGridSafeBottom;
            var shift = await PrivateServerScrollGrid(down ? -1 : 1);
            double? moved = null;
            using (var capture = CaptureToRectArea())
            {
                // 红框还在画面里时，用红框的新位置判断滚动了多少（最准确）
                if (PrivateServerFindSelectedCell(capture) is { } cell && cell.Col == col)
                {
                    moved = cell.Y - y;
                }
            }

            moved ??= shift;
            if (moved is null)
            {
                _logger.LogWarning("{Name}：无法判断首领列表滚动了多少", Name);
                return new PrivateServerHandbookStep(PrivateServerHandbookStepResult.Failed, 0, 0);
            }

            if (Math.Abs(moved.Value) < 3)
            {
                // 列表已经滚不动了
                if (down && targetY > PrivateServerGridBottom - 40)
                {
                    // 下面没有更多行了
                    return new PrivateServerHandbookStep(PrivateServerHandbookStepResult.EndOfList, 0, 0);
                }

                if (!down && targetY < PrivateServerGridTop + 40)
                {
                    return new PrivateServerHandbookStep(PrivateServerHandbookStepResult.Failed, 0, 0);
                }

                // 下一个图标大部分可见，直接点击
                break;
            }

            y += moved.Value;
            targetY = y + rowOffset;
        }

        if (targetY < PrivateServerGridTop + 40 || targetY > PrivateServerGridBottom - 40)
        {
            _logger.LogWarning("{Name}：没能把下一个首领滚动到可见位置", Name);
            return new PrivateServerHandbookStep(PrivateServerHandbookStepResult.Failed, 0, 0);
        }

        // 2. 下一个格子是空的，说明已经到列表末尾
        using (var capture = CaptureToRectArea())
        {
            if (!PrivateServerCellHasIcon(capture, targetCol, targetY))
            {
                return new PrivateServerHandbookStep(PrivateServerHandbookStepResult.EndOfList, 0, 0);
            }
        }

        // 3. 点击下一个首领的图标，确认红框移动过去了
        for (var attempt = 0; attempt < 2; attempt++)
        {
            page.Click(PrivateServerGridColumnX[targetCol], targetY);
            await Delay(1000, _ct);
            using var capture = CaptureToRectArea();
            if (PrivateServerFindSelectedCell(capture) is { } cell && cell.Col == targetCol)
            {
                return new PrivateServerHandbookStep(PrivateServerHandbookStepResult.Selected, cell.Col, cell.Y);
            }
        }

        return new PrivateServerHandbookStep(PrivateServerHandbookStepResult.Failed, 0, 0);
    }

    /// <summary>
    /// 点击冒险之证右页的“前往”，在打开的大地图上点击“传送并追踪”，等待传送完成回到游戏主界面。
    /// 大地图上显示的是“追踪并引导”时，说明附近没有解锁的传送锚点：不点击，返回 NoWaypoint。
    /// </summary>
    private async Task<PrivateServerTeleportResult> PrivateServerClickGotoAndTeleport(BvPage page)
    {
        if (await PrivateServerWaitText(PrivateServerHandbookGotoRect, ["前往"], 3000, click: true) == null)
        {
            _logger.LogWarning("{Name}：冒险之证右页没有找到“前往”", Name);
            return PrivateServerTeleportResult.NoGotoButton;
        }

        await Delay(1200, _ct);
        var mapButton = await PrivateServerWaitText(PrivateServerMapTeleportTrackRect, ["传送", "引导"], 6000, click: false);
        if (mapButton == null)
        {
            _logger.LogWarning("{Name}：大地图上没有找到“传送并追踪”", Name);
            return PrivateServerTeleportResult.Failed;
        }

        if (!mapButton.Contains("传送", StringComparison.Ordinal))
        {
            // “追踪并引导”：附近没有解锁的传送锚点，不点击
            return PrivateServerTeleportResult.NoWaypoint;
        }

        if (await PrivateServerWaitText(PrivateServerMapTeleportTrackRect, ["传送"], 2000, click: true) == null)
        {
            _logger.LogWarning("{Name}：大地图上没有找到“传送并追踪”", Name);
            return PrivateServerTeleportResult.Failed;
        }

        await Delay(2000, _ct);
        var stopwatch = Stopwatch.StartNew();
        var mainUiTimes = 0;
        while (stopwatch.Elapsed < TimeSpan.FromSeconds(40))
        {
            _ct.ThrowIfCancellationRequested();
            using (var capture = CaptureToRectArea())
            {
                if (Bv.IsInMainUi(capture) && !Bv.IsInBigMapUi(capture))
                {
                    if (++mainUiTimes >= 3)
                    {
                        return PrivateServerTeleportResult.Teleported;
                    }
                }
                else
                {
                    mainUiTimes = 0;
                }
            }

            await Delay(500, _ct);
        }

        return PrivateServerTeleportResult.Failed;
    }

    // ---------- 第 9 版：战斗结束后原地慢慢转视角找征讨之花，找到后对准直线走过去 ----------
    // ---------- 第 10 版：找花前先把镜头拉远、视角朝下看；头顶没有图标的花改按“深色叶子 + 红紫色花苞”找 ----------

    /// <summary>原地转视角找花时最多转几圈（第 9 版）。</summary>
    private const int PrivateServerFlowerScanRounds = 3;

    /// <summary>原地转视角找花时每一步转多少度，数字越小转得越慢（第 9 版）。</summary>
    private const double PrivateServerFlowerScanStepDegrees = 15;

    /// <summary>往花走的路上，每隔多少毫秒按一次交互键（第 9 版）。</summary>
    private const int PrivateServerApproachInteractIntervalMs = 600;

    /// <summary>往花走的路上，看不到花超过多少毫秒就停下来重新找（第 9 版）。</summary>
    private const int PrivateServerApproachLostMs = 1500;

    /// <summary>一次最多连续走多少秒；还没走到花跟前就停下来重新找，免得跑出首领区域（第 9 版）。</summary>
    private const int PrivateServerApproachMaxWalkSeconds = 8;

    /// <summary>一次找花（包括走过去）最多用多少秒（第 9 版）。</summary>
    private const int PrivateServerFlowerSearchMaxSeconds = 120;

    /// <summary>鼠标移动多少像素视角转 1 度的初始估计值；转动时会用小地图上的视角方向实际测量并修正（第 9 版）。</summary>
    private const double PrivateServerInitialMousePxPerDegree = 5.3;

    /// <summary>画面横向的视野角度，用来把花在画面上的位置换算成要转的角度（第 9 版）。</summary>
    private const double PrivateServerHorizontalFovDegrees = 73;

    /// <summary>头顶图标在画面这个高度（比例）以下时，说明花在身后，不算找到，继续转（第 9 版）。</summary>
    private const double PrivateServerFlowerIconFrontMaxRatio = 0.7;

    /// <summary>找花前滚轮往下滚几格，把镜头拉远（第 10 版）。</summary>
    private const int PrivateServerZoomOutScrollClicks = 10;

    /// <summary>
    /// 视角回正后再往下看多少度（第 10 版）。数字越大，画面里地面越多、干扰越少，但看到的范围越近，
    /// 太大时离得稍远的花会看不到（往下看到底时只能看到身边 5 米左右）。
    /// </summary>
    private const double PrivateServerLookDownDegrees = 50;

    /// <summary>一次找花最多朝几个目标走过去；都没有走到花跟前，就当作这次没找到，免得被认错的东西带着到处走（第 10 版）。</summary>
    private const int PrivateServerMaxApproachAttempts = 4;

    /// <summary>按叶子和花苞找到的花，中心在画面这个高度（1080P 的 Y 坐标）以下时，说明在角色身边或身后，不算找到，继续转（第 10 版）。</summary>
    private const int PrivateServerLeafBudFrontMaxY = 650;

    /// <summary>每次找花最多存几张截图（只在没找到花时保存，转第一圈时每转大约 45 度存一张）（第 10 版）。</summary>
    private const int PrivateServerFlowerScreenshotsPerSearch = 8;

    /// <summary>截图文件夹里最多留几张，超过时删掉最早的（第 10 版）。</summary>
    private const int PrivateServerFlowerScreenshotsKeep = 48;

    // 下面是按“深色叶子 + 红紫色花苞”找花时用的颜色范围和大小（第 10 版，按你发来的截图调的，一般不用改）。
    // 颜色按 OpenCV 的 HSV 表示：H（色调）0～180，S（饱和度）、V（亮度）0～255；像素数量按截图缩小到 960×540 后统计。

    // 深色叶子（墨绿～深蓝色）：色调范围、饱和度下限、亮度上限（叶子比地面暗）
    private const int PrivateServerLeafMinHue = 40;
    private const int PrivateServerLeafMaxHue = 125;
    private const int PrivateServerLeafMinSaturation = 45;
    private const int PrivateServerLeafMaxValue = 95;

    // 红紫色花苞和花纹：色调在 PrivateServerBudMinHue 以上（紫红色）或 PrivateServerBudMaxRedHue 以下（红色），饱和度比红褐色泥土更高
    private const int PrivateServerBudMinHue = 125;
    private const int PrivateServerBudMaxRedHue = 8;
    private const int PrivateServerBudMinSaturation = 100;
    private const int PrivateServerBudMinValue = 50;
    private const int PrivateServerBudMaxValue = 235;

    // 一块里至少要有多少深色叶子像素、多少红紫色像素；两种颜色里少的那种至少占这一块的多少（只有一种颜色的不算）
    private const int PrivateServerFlowerMinLeafPixels = 60;
    private const int PrivateServerFlowerMinBudPixels = 25;
    private const double PrivateServerFlowerMinCueShare = 0.05;

    // 这一块的长宽比最多多少（太扁的是地上的条纹、悬崖边）、最多多少像素（太大的是大片地形）、把靠得很近的像素连成一块的范围
    private const double PrivateServerFlowerMaxAspect = 3.0;
    private const int PrivateServerFlowerMaxBlobPixels = 30000;
    private const int PrivateServerFlowerMergeSize = 9;

    /// <summary>按叶子和花苞找花时忽略的区域（1080P）：小地图、右上角按钮、队伍列表、下方按钮和血条、技能图标、角色本身（第 10 版）。</summary>
    private static readonly Rect[] PrivateServerLeafBudIgnoreRects =
    [
        new(0, 0, 330, 320), new(1450, 0, 470, 120), new(1560, 230, 360, 400),
        new(0, 960, 1920, 120), new(1600, 880, 320, 200), new(820, 360, 280, 540)
    ];

    /// <summary>找花的阶段（第 9 版）。</summary>
    private enum PrivateServerFlowerPhase
    {
        /// <summary>原地慢慢转视角找花（不走动）。</summary>
        Scan,

        /// <summary>找到了花，原地转视角对准。</summary>
        Aim,

        /// <summary>已经对准，按住前进直线走过去。</summary>
        Approach
    }

    /// <summary>
    /// 第 9 版找花：视角回正后，原地慢慢转视角寻找征讨之花，最多转 PrivateServerFlowerScanRounds 圈，转的时候不走动；
    /// 找到后原地对准，再按住前进直线走过去，路上每隔一会儿按一次交互键。
    /// 看到“接触征讨之花”后停下，按一次交互键等结果；按了 3 次都没有弹出领奖界面，就按本周次数已用完处理（同第 8 版）。
    /// 第 10 版：找之前先把镜头拉远、视角朝下看（PrivateServerZoomOutAndLookDown）；头顶没有图标的花改按深色叶子和红紫色花苞找；
    /// 只在游戏主界面（左上角能看到派蒙）时才认花；最多朝 PrivateServerMaxApproachAttempts 个目标走过去；找完把视角回正。
    /// 进入领奖界面、或确认本周次数已用完时返回；没有找到时抛出 TimeoutException。
    /// </summary>
    private async Task PrivateServerScanAndApproachFlower()
    {
        var page = new BvPage(_ct);
        var captureRect = TaskContext.Instance().SystemInfo.ScaleMax1080PCaptureRect;
        var width = (double)captureRect.Width;
        var height = (double)captureRect.Height;
        var centerX = width / 2.0;
        var focal = centerX / Math.Tan(PrivateServerHorizontalFovDegrees / 2 * Math.PI / 180);
        var rewardBox = LoadRecognitionObject("RewardBox");
        var climbRect = ScaleRect(1686, 1030, 60, 23);

        var pxPerDegree = PrivateServerInitialMousePxPerDegree;
        var phase = PrivateServerFlowerPhase.Scan;
        double scannedDegrees = 0;
        var roundsLogged = 0;
        var scanSteps = 0;
        double? candidateX = null;
        var lastSeenAt = DateTime.MinValue;
        var walkStartedAt = DateTime.MinValue;
        var isWalking = false;
        var lastInteractAt = DateTime.MinValue;
        var lastPromptPressAt = DateTime.MinValue;
        var unansweredPresses = 0;
        var approachAttempts = 0;
        double? lastAimFromX = null;
        double lastAimMovePx = 0;
        var cameraTilted = false;
        var tiltChecked = false;
        double tiltPx = 0;
        var reachedPanel = false;
        DateTime? notInWorldSince = null;
        var notInWorldLogged = false;
        var screenshots = new List<byte[]>();
        var lastShotStep = -1;
        var stopwatch = Stopwatch.StartNew();

        // 画面上的横坐标 → 相对画面中心的角度（度）
        double AngleOf(double x) => Math.Atan((x - centerX) / focal) * 180 / Math.PI;

        void StopWalking()
        {
            if (isWalking)
            {
                Simulation.SendInput.SimulateAction(GIActions.MoveForward, KeyType.KeyUp);
                isWalking = false;
            }
        }

        _logger.LogInformation("{Name}：开始寻找征讨之花：原地慢慢转视角找（最多转 {Rounds} 圈），找到后对准直线走过去", Name, PrivateServerFlowerScanRounds);

        // 视角回正（鼠标中键）：视角回到角色身后的默认高度（BetterGI 寻找地脉花奖励时也是这样做的）
        Simulation.SendInput.Mouse.MiddleButtonClick();
        await Delay(500, _ct);

        try
        {
            if (PrivateServerZoomOutAndLookDown)
            {
                // 第 10 版：镜头拉远（滚轮往下），再把视角往下转一些，让画面里主要是地面
                tiltPx = await PrivateServerZoomOutAndLookDownCamera(pxPerDegree);
                cameraTilted = true;
            }

            while (true)
            {
                _ct.ThrowIfCancellationRequested();
                if (stopwatch.Elapsed > TimeSpan.FromSeconds(PrivateServerFlowerSearchMaxSeconds))
                {
                    throw new TimeoutException("寻找征讨之花超时");
                }

                // 1. 按过交互键后：看是否进入了领奖界面、是否提示本周次数已用完
                if (lastInteractAt != DateTime.MinValue)
                {
                    if (HasRewardPanelPrompt(page) || IsRewardPanelOpen(page))
                    {
                        reachedPanel = true;
                        _logger.LogInformation("{Name}：已进入征讨之花领奖界面", Name);
                        return;
                    }

                    if (DateTime.UtcNow - lastInteractAt < TimeSpan.FromSeconds(4) && HasWeeklyLimitToast(page))
                    {
                        _psWeeklyLimitReached = true;
                        _logger.LogInformation("{Name}：征讨之花提示“本周收取该宝藏次数已耗尽”", Name);
                        return;
                    }
                }

                // 2. 出现“接触征讨之花”：已经在花跟前，停下来，按一次交互键等结果
                if (HasRewardInteractionPrompt(page))
                {
                    StopWalking();
                    if (cameraTilted)
                    {
                        // 第 10 版：已经走到花跟前了，先把视角回正，再按交互键
                        Simulation.SendInput.Mouse.MiddleButtonClick();
                        cameraTilted = false;
                        _logger.LogInformation("{Name}：已经走到征讨之花跟前，视角回正", Name);
                        await Delay(300, _ct);
                    }

                    if (DateTime.UtcNow - lastPromptPressAt >= TimeSpan.FromMilliseconds(PrivateServerInteractRetryMs))
                    {
                        if (lastPromptPressAt != DateTime.MinValue)
                        {
                            unansweredPresses++;
                            if (unansweredPresses >= PrivateServerUnansweredInteractLimit)
                            {
                                _logger.LogWarning("{Name}：按了 {Count} 次交互键都没有弹出领奖界面（也没认出提示文字），按“本周收取该宝藏次数已耗尽”处理",
                                    Name, unansweredPresses);
                                _psWeeklyLimitReached = true;
                                _logger.LogInformation("{Name}：征讨之花提示“本周收取该宝藏次数已耗尽”", Name);
                                return;
                            }

                            _logger.LogInformation("{Name}：按交互键后没有弹出领奖界面，再按一次", Name);
                        }

                        Simulation.SendInput.SimulateAction(GIActions.PickUpOrInteract);
                        lastPromptPressAt = DateTime.UtcNow;
                        lastInteractAt = lastPromptPressAt;
                    }

                    await Delay(150, _ct);
                    continue;
                }

                // 3. 在画面里找花（头顶图标优先，其次按深色叶子和红紫色花苞找）；只在游戏主界面（能看到派蒙）时才认
                var found = false;
                var byIcon = false;
                double targetX = 0;
                float? angleBefore = null;
                bool inWorld;
                using (var capture = CaptureToRectArea())
                {
                    using (var paimon = capture.Find(BetterGenshinImpact.GameTask.Common.Element.Assets.ElementRecognition.Get("PaimonMenu", capture)))
                    {
                        inWorld = paimon.IsExist();
                    }

                    if (inWorld)
                    {
                        found = PrivateServerFindFlowerTarget(capture, rewardBox, height, out targetX, out byIcon);
                        angleBefore = PrivateServerTryGetCameraAngle(capture);

                        // 转第一圈时每转大约 45 度存一张截图（没找到花时才写到硬盘上）
                        if (PrivateServerSaveFlowerSearchScreenshots && !found && phase == PrivateServerFlowerPhase.Scan
                            && scanSteps % 3 == 0 && scanSteps != lastShotStep && screenshots.Count < PrivateServerFlowerScreenshotsPerSearch)
                        {
                            lastShotStep = scanSteps;
                            var jpg = PrivateServerEncodeHalfSizeJpeg(capture.SrcMat);
                            if (jpg != null)
                            {
                                screenshots.Add(jpg);
                            }
                        }
                    }
                }

                if (!inWorld)
                {
                    // 第 10 版：不在游戏主界面（左上角看不到派蒙，例如弹出了别的界面）时，不认花、不走动，等一会儿再看
                    StopWalking();
                    if (phase == PrivateServerFlowerPhase.Approach)
                    {
                        phase = PrivateServerFlowerPhase.Aim;
                    }

                    lastSeenAt = DateTime.UtcNow;
                    notInWorldSince ??= DateTime.UtcNow;
                    if (!notInWorldLogged && DateTime.UtcNow - notInWorldSince > TimeSpan.FromSeconds(5))
                    {
                        notInWorldLogged = true;
                        _logger.LogInformation("{Name}：现在不在游戏主界面（左上角看不到派蒙），先等一下再找征讨之花", Name);
                    }

                    await Delay(300, _ct);
                    continue;
                }

                notInWorldSince = null;

                // 第 10 版：不管按图标还是按叶子和花苞找到，都把花放在画面正中间（视角朝下看时，正前方的花在角色头顶上方）
                var aimX = centerX;
                var tolerance = width * 0.04;

                if (phase == PrivateServerFlowerPhase.Scan)
                {
                    if (found)
                    {
                        // 按叶子和花苞找到时，原地停一下再看一眼，两次都在同一个位置看到才算（免得把别的东西当成花）
                        if (!byIcon && (candidateX is not { } firstX || Math.Abs(firstX - targetX) > 150))
                        {
                            candidateX = targetX;
                            await Delay(300, _ct);
                            continue;
                        }

                        candidateX = null;
                        lastSeenAt = DateTime.UtcNow;
                        scannedDegrees = 0;
                        roundsLogged = 0;
                        lastAimFromX = null;
                        phase = PrivateServerFlowerPhase.Aim;
                        _logger.LogInformation("{Name}：找到了征讨之花（{How}），先对准，再直线走过去", Name, byIcon ? "头顶图标" : "叶子和花苞");
                        continue;
                    }

                    candidateX = null;
                    if (scannedDegrees >= 360.0 * PrivateServerFlowerScanRounds)
                    {
                        throw new TimeoutException($"原地转了 {PrivateServerFlowerScanRounds} 圈也没有找到征讨之花");
                    }

                    // 慢慢转一小步，再看小地图上的视角方向实际转了多少度
                    var stepPx = pxPerDegree * PrivateServerFlowerScanStepDegrees;
                    await PrivateServerTurnCameraSmoothly(stepPx);
                    scanSteps++;
                    await Delay(200, _ct);
                    float? angleAfter;
                    using (var after = CaptureToRectArea())
                    {
                        angleAfter = PrivateServerTryGetCameraAngle(after);
                    }

                    var turned = PrivateServerAngleBetween(angleBefore, angleAfter);
                    if (turned is >= 3 and <= 90)
                    {
                        var measured = Math.Clamp(stepPx / turned.Value, 0.5, 60);
                        pxPerDegree = Math.Clamp(pxPerDegree * 0.5 + measured * 0.5, 0.5, 60);
                        scannedDegrees += turned.Value;

                        // 第 10 版：第一次量出实际的鼠标灵敏度后，按实际灵敏度修正一次往下看的角度
                        if (cameraTilted && !tiltChecked)
                        {
                            tiltChecked = true;
                            var wantedPx = PrivateServerLookDownDegrees * measured;
                            if (Math.Abs(wantedPx - tiltPx) >= Math.Max(10, tiltPx * 0.3))
                            {
                                await PrivateServerTurnCameraSmoothly(0, wantedPx - tiltPx);
                                tiltPx = wantedPx;
                                await Delay(200, _ct);
                            }
                        }
                    }
                    else
                    {
                        scannedDegrees += PrivateServerFlowerScanStepDegrees;
                    }

                    var rounds = (int)(scannedDegrees / 360);
                    if (rounds > roundsLogged && rounds < PrivateServerFlowerScanRounds)
                    {
                        roundsLogged = rounds;
                        _logger.LogInformation("{Name}：已经原地转了 {Rounds} 圈，还没找到征讨之花，继续转", Name, rounds);
                    }

                    continue;
                }

                if (phase == PrivateServerFlowerPhase.Aim)
                {
                    if (!found)
                    {
                        if (DateTime.UtcNow - lastSeenAt > TimeSpan.FromMilliseconds(1200))
                        {
                            phase = PrivateServerFlowerPhase.Scan;
                            _logger.LogInformation("{Name}：看不到征讨之花了，继续转视角寻找", Name);
                        }
                        else
                        {
                            await Delay(150, _ct);
                        }

                        continue;
                    }

                    lastSeenAt = DateTime.UtcNow;
                    // 根据上一次转动后花在画面上移动了多少，修正“鼠标移动多少像素转 1 度”
                    if (lastAimFromX is { } fromX && Math.Abs(lastAimMovePx) >= 8)
                    {
                        var moved = AngleOf(fromX) - AngleOf(targetX);
                        if (Math.Abs(moved) >= 1 && Math.Sign(moved) == Math.Sign(lastAimMovePx))
                        {
                            pxPerDegree = Math.Clamp(pxPerDegree * 0.5 + lastAimMovePx / moved * 0.5, 0.5, 60);
                        }
                    }

                    lastAimFromX = null;
                    if (Math.Abs(targetX - aimX) <= tolerance)
                    {
                        // 已经对准：按住前进直线走过去
                        approachAttempts++;
                        Simulation.SendInput.SimulateAction(GIActions.MoveForward, KeyType.KeyDown);
                        isWalking = true;
                        walkStartedAt = DateTime.UtcNow;
                        phase = PrivateServerFlowerPhase.Approach;
                        continue;
                    }

                    var aimPx = Math.Clamp((AngleOf(targetX) - AngleOf(aimX)) * pxPerDegree * 0.8, -pxPerDegree * 60, pxPerDegree * 60);
                    await PrivateServerTurnCameraSmoothly(aimPx);
                    lastAimFromX = targetX;
                    lastAimMovePx = aimPx;
                    await Delay(250, _ct);
                    continue;
                }

                // 4. 正在走过去：边走边微调方向，路上每隔一会儿按一次交互键
                if (page.Locator("Space", climbRect).IsExist())
                {
                    StopWalking();
                    _logger.LogInformation("{Name}：检测到攀爬状态，尝试脱离", Name);
                    Simulation.SendInput.SimulateAction(GIActions.Drop);
                    await Delay(1000, _ct);
                    phase = PrivateServerFlowerPhase.Scan;
                    continue;
                }

                if (found)
                {
                    lastSeenAt = DateTime.UtcNow;
                    if (Math.Abs(targetX - aimX) > tolerance)
                    {
                        // 边走边转的幅度小一些，免得左右摇摆
                        var steerPx = Math.Clamp((AngleOf(targetX) - AngleOf(aimX)) * pxPerDegree * 0.5, -pxPerDegree * 15, pxPerDegree * 15);
                        Simulation.SendInput.Mouse.MoveMouseBy((int)Math.Round(steerPx), 0);
                    }
                }
                else if (DateTime.UtcNow - lastSeenAt > TimeSpan.FromMilliseconds(PrivateServerApproachLostMs))
                {
                    StopWalking();
                    if (approachAttempts >= PrivateServerMaxApproachAttempts)
                    {
                        throw new TimeoutException($"朝征讨之花走了 {approachAttempts} 次都没有走到跟前");
                    }

                    phase = PrivateServerFlowerPhase.Scan;
                    _logger.LogInformation("{Name}：走的途中看不到征讨之花了，停下来重新转视角寻找", Name);
                    continue;
                }

                if (DateTime.UtcNow - walkStartedAt > TimeSpan.FromSeconds(PrivateServerApproachMaxWalkSeconds))
                {
                    StopWalking();
                    if (approachAttempts >= PrivateServerMaxApproachAttempts)
                    {
                        throw new TimeoutException($"朝征讨之花走了 {approachAttempts} 次都没有走到跟前");
                    }

                    phase = PrivateServerFlowerPhase.Scan;
                    _logger.LogInformation("{Name}：走了 {Seconds} 秒还没走到征讨之花跟前，停下来重新寻找", Name, PrivateServerApproachMaxWalkSeconds);
                    continue;
                }

                if (DateTime.UtcNow - lastInteractAt >= TimeSpan.FromMilliseconds(PrivateServerApproachInteractIntervalMs))
                {
                    Simulation.SendInput.SimulateAction(GIActions.PickUpOrInteract);
                    lastInteractAt = DateTime.UtcNow;
                }

                await Delay(100, _ct);
            }
        }
        catch (TimeoutException)
        {
            // 第 10 版：没找到花时，把找花时看到的画面存下来，方便以后调整识别
            PrivateServerSaveFlowerScreenshotsToLog(screenshots);
            throw;
        }
        finally
        {
            StopWalking();
            Simulation.SendInput.SimulateAction(GIActions.MoveForward, KeyType.KeyUp);
            if (cameraTilted)
            {
                if (reachedPanel)
                {
                    // 已经进了领奖界面，这时按中键没有用：等下一轮开打前再把视角回正
                    _psCameraNeedsReset = true;
                }
                else
                {
                    Simulation.SendInput.Mouse.MiddleButtonClick();
                    _logger.LogInformation("{Name}：视角回正", Name);
                }
            }
        }
    }

    /// <summary>
    /// 第 10 版：滚轮往下滚 PrivateServerZoomOutScrollClicks 格把镜头拉远，再把视角往下转大约 PrivateServerLookDownDegrees 度，
    /// 让画面里主要是地面（减少远处地形、天空、光影的干扰），角色在画面里也小一些，不容易挡住花。
    /// </summary>
    /// <param name="pxPerDegree">鼠标移动多少像素视角转 1 度（估计值，转第一步后会按实际测量修正一次）。</param>
    /// <returns>往下移动鼠标的像素。</returns>
    private async Task<double> PrivateServerZoomOutAndLookDownCamera(double pxPerDegree)
    {
        for (var i = 0; i < PrivateServerZoomOutScrollClicks; i++)
        {
            Simulation.SendInput.Mouse.VerticalScroll(-1);
            await Delay(40, _ct);
        }

        await Delay(300, _ct);
        var tiltPx = Math.Max(0, PrivateServerLookDownDegrees) * pxPerDegree;
        await PrivateServerTurnCameraSmoothly(0, tiltPx);
        await Delay(300, _ct);
        _logger.LogInformation("{Name}：镜头拉远并朝下看（滚轮往下 {Clicks} 格，视角往下约 {Degrees} 度）", Name, PrivateServerZoomOutScrollClicks, PrivateServerLookDownDegrees);
        return tiltPx;
    }

    /// <summary>
    /// 在截图里找征讨之花：先找头顶的图标（图标在画面下方时花在身后，不算找到），
    /// 没有图标时按深色叶子和红紫色花苞找（需要开启 PrivateServerFindFlowerWithoutIcon；在角色身边或身后的不算）。（第 9、10 版）
    /// </summary>
    /// <param name="capture">当前截图（1080P）。</param>
    /// <param name="rewardBox">头顶图标的模板。</param>
    /// <param name="height">截图高度。</param>
    /// <param name="targetX">花（或图标）在截图中的 X 坐标。</param>
    /// <param name="byIcon">是不是按头顶图标找到的。</param>
    private static bool PrivateServerFindFlowerTarget(ImageRegion capture, RecognitionObject rewardBox, double height, out double targetX, out bool byIcon)
    {
        targetX = 0;
        byIcon = false;
        using (var icon = capture.Find(rewardBox))
        {
            if (icon.IsExist())
            {
                if (icon.Y + icon.Height / 2.0 >= height * PrivateServerFlowerIconFrontMaxRatio)
                {
                    return false;
                }

                targetX = icon.X + icon.Width / 2.0;
                byIcon = true;
                return true;
            }
        }

        if (!PrivateServerFindFlowerWithoutIcon)
        {
            return false;
        }

        var src = capture.SrcMat;
        if (!PrivateServerTryFindFlowerByLeafAndBud(src, out targetX, out var targetY, out _, out _))
        {
            return false;
        }

        return targetY * 1080.0 / src.Height < PrivateServerLeafBudFrontMaxY;
    }

    /// <summary>
    /// 第 10 版：按“深色叶子 + 红紫色花苞”找征讨之花（头顶没有图标时用）。
    /// 把深色叶子的像素和红紫色（花苞、花纹）的像素连成一块一块；某一块里两种颜色都够多、形状不太扁、大小合适，就当作征讨之花，
    /// 有好几块时选两种颜色都最多的那块。小地图、按钮、队伍列表、技能图标和角色本身所在的区域不看。
    /// 只看一种颜色时，红褐色的泥土、岩浆、深色的石头都容易被认错；两种颜色挨在一起的，在你发来的截图里只有征讨之花。
    /// </summary>
    /// <param name="src">当前截图。</param>
    /// <param name="targetX">花在截图中的 X 坐标（这一块的中心）。</param>
    /// <param name="targetY">花在截图中的 Y 坐标（这一块的中心）。</param>
    /// <param name="leafPixels">这一块里深色叶子的像素数量（缩小到 960×540 后统计）。</param>
    /// <param name="budPixels">这一块里红紫色的像素数量（缩小到 960×540 后统计）。</param>
    private static bool PrivateServerTryFindFlowerByLeafAndBud(Mat src, out double targetX, out double targetY, out int leafPixels, out int budPixels)
    {
        targetX = 0;
        targetY = 0;
        leafPixels = 0;
        budPixels = 0;
        if (src.Empty() || src.Width < 2 || src.Height < 2)
        {
            return false;
        }

        using var bgr = PrivateServerCropBgr(src, new Rect(0, 0, src.Width, src.Height));
        using var small = new Mat();
        Cv2.Resize(bgr, small, new Size(bgr.Width / 2, bgr.Height / 2), 0, 0, InterpolationFlags.Area);
        using var hsv = new Mat();
        Cv2.CvtColor(small, hsv, ColorConversionCodes.BGR2HSV);

        using var leaf = new Mat();
        Cv2.InRange(hsv, new Scalar(PrivateServerLeafMinHue, PrivateServerLeafMinSaturation, 0),
            new Scalar(PrivateServerLeafMaxHue, 255, PrivateServerLeafMaxValue), leaf);
        using var budPurple = new Mat();
        using var budRed = new Mat();
        using var bud = new Mat();
        Cv2.InRange(hsv, new Scalar(PrivateServerBudMinHue, PrivateServerBudMinSaturation, PrivateServerBudMinValue),
            new Scalar(180, 255, PrivateServerBudMaxValue), budPurple);
        Cv2.InRange(hsv, new Scalar(0, PrivateServerBudMinSaturation, PrivateServerBudMinValue),
            new Scalar(PrivateServerBudMaxRedHue, 255, PrivateServerBudMaxValue), budRed);
        Cv2.BitwiseOr(budPurple, budRed, bud);

        // 不看小地图、按钮、队伍列表、技能图标和角色本身
        var k = small.Width / 1920.0;
        var bounds = new Rect(0, 0, small.Width, small.Height);
        foreach (var r in PrivateServerLeafBudIgnoreRects)
        {
            var scaled = new Rect((int)(r.X * k), (int)(r.Y * k), (int)Math.Ceiling(r.Width * k) + 1, (int)Math.Ceiling(r.Height * k) + 1) & bounds;
            if (scaled.Width <= 0 || scaled.Height <= 0)
            {
                continue;
            }

            using (var leafPart = new Mat(leaf, scaled))
            {
                leafPart.SetTo(Scalar.Black);
            }

            using (var budPart = new Mat(bud, scaled))
            {
                budPart.SetTo(Scalar.Black);
            }
        }

        // 把靠得很近的叶子和花苞像素连成一块
        using var both = new Mat();
        Cv2.BitwiseOr(leaf, bud, both);
        using var kernel = Cv2.GetStructuringElement(MorphShapes.Ellipse, new Size(PrivateServerFlowerMergeSize, PrivateServerFlowerMergeSize));
        using var merged = new Mat();
        Cv2.MorphologyEx(both, merged, MorphTypes.Close, kernel);
        using var labels = new Mat();
        using var stats = new Mat();
        using var centroids = new Mat();
        var count = Cv2.ConnectedComponentsWithStats(merged, labels, stats, centroids, PixelConnectivity.Connectivity8);

        var bestScore = 0;
        for (var i = 1; i < count; i++)
        {
            var x = stats.At<int>(i, 0);
            var y = stats.At<int>(i, 1);
            var w = stats.At<int>(i, 2);
            var h = stats.At<int>(i, 3);
            var area = stats.At<int>(i, 4);
            if (w <= 0 || h <= 0 || area < PrivateServerFlowerMinLeafPixels + PrivateServerFlowerMinBudPixels || area > PrivateServerFlowerMaxBlobPixels)
            {
                continue;
            }

            if (Math.Max(w / (double)h, h / (double)w) > PrivateServerFlowerMaxAspect)
            {
                continue;
            }

            // 数一数这一块里分别有多少叶子像素、多少花苞像素
            var box = new Rect(x, y, w, h);
            using var labelPart = new Mat(labels, box);
            using var component = new Mat();
            Cv2.InRange(labelPart, new Scalar(i), new Scalar(i), component);
            using var leafPart2 = new Mat(leaf, box);
            using var budPart2 = new Mat(bud, box);
            using var leafIn = new Mat();
            using var budIn = new Mat();
            Cv2.BitwiseAnd(leafPart2, component, leafIn);
            Cv2.BitwiseAnd(budPart2, component, budIn);
            var leafCount = Cv2.CountNonZero(leafIn);
            var budCount = Cv2.CountNonZero(budIn);
            if (leafCount < PrivateServerFlowerMinLeafPixels || budCount < PrivateServerFlowerMinBudPixels
                || Math.Min(leafCount, budCount) < PrivateServerFlowerMinCueShare * (leafCount + budCount))
            {
                continue;
            }

            var score = Math.Min(leafCount, budCount);
            if (score <= bestScore)
            {
                continue;
            }

            bestScore = score;
            leafPixels = leafCount;
            budPixels = budCount;
            targetX = (x + w / 2.0) / small.Width * src.Width;
            targetY = (y + h / 2.0) / small.Height * src.Height;
        }

        return bestScore > 0;
    }

    /// <summary>把截图缩小一半、压缩成 JPG（第 10 版，没找到花时保存用）；失败时返回 null。</summary>
    private static byte[]? PrivateServerEncodeHalfSizeJpeg(Mat src)
    {
        try
        {
            if (src.Empty() || src.Width < 2 || src.Height < 2)
            {
                return null;
            }

            using var bgr = PrivateServerCropBgr(src, new Rect(0, 0, src.Width, src.Height));
            using var small = new Mat();
            Cv2.Resize(bgr, small, new Size(bgr.Width / 2, bgr.Height / 2), 0, 0, InterpolationFlags.Area);
            Cv2.ImEncode(".jpg", small, out var buffer, new ImageEncodingParam(ImwriteFlags.JpegQuality, 85));
            return buffer;
        }
        catch (Exception)
        {
            return null;
        }
    }

    /// <summary>
    /// 第 10 版：没找到征讨之花时，把找花时看到的画面保存到 BetterGI 文件夹里的 log\pserver_flower（文件夹里最多留 PrivateServerFlowerScreenshotsKeep 张，
    /// 多了删掉最早的）。以后还是经常找不到时，可以把这些图片发出来，用来调整识别。
    /// </summary>
    /// <param name="images">已经压缩好的截图。</param>
    private void PrivateServerSaveFlowerScreenshotsToLog(List<byte[]> images)
    {
        if (!PrivateServerSaveFlowerSearchScreenshots || images.Count == 0)
        {
            return;
        }

        try
        {
            var folder = Global.Absolute(@"log\pserver_flower");
            Directory.CreateDirectory(folder);
            var stamp = DateTime.Now.ToString("yyyyMMdd-HHmmss", CultureInfo.InvariantCulture);
            for (var i = 0; i < images.Count; i++)
            {
                File.WriteAllBytes(Path.Combine(folder, $"{stamp}-{i + 1}.jpg"), images[i]);
            }

            foreach (var old in new DirectoryInfo(folder).GetFiles("*.jpg").OrderByDescending(f => f.Name, StringComparer.Ordinal).Skip(PrivateServerFlowerScreenshotsKeep))
            {
                old.Delete();
            }

            _logger.LogInformation("{Name}：没找到征讨之花，找花时看到的画面已保存到 {Folder}（{Count} 张）", Name, folder, images.Count);
        }
        catch (Exception e)
        {
            _logger.LogDebug(e, "{Name}：保存找花截图失败", Name);
        }
    }

    /// <summary>分 5 次慢慢移动鼠标转动视角（大约 150 毫秒），不会一下子转很多（第 9 版；第 10 版加了上下方向）。</summary>
    /// <param name="pixels">鼠标横向移动的像素，正数向右转。</param>
    /// <param name="verticalPixels">鼠标纵向移动的像素，正数往下看。</param>
    private async Task PrivateServerTurnCameraSmoothly(double pixels, double verticalPixels = 0)
    {
        const int pieces = 5;
        var movedX = 0;
        var movedY = 0;
        for (var i = 1; i <= pieces; i++)
        {
            var targetX = (int)Math.Round(pixels * i / pieces);
            var targetY = (int)Math.Round(verticalPixels * i / pieces);
            if (targetX != movedX || targetY != movedY)
            {
                Simulation.SendInput.Mouse.MoveMouseBy(targetX - movedX, targetY - movedY);
                movedX = targetX;
                movedY = targetY;
            }

            await Delay(30, _ct);
        }
    }

    /// <summary>两次视角方向之间相差多少度（0～180）；任意一次没识别出来时返回 null（第 9 版）。</summary>
    private static double? PrivateServerAngleBetween(float? before, float? after)
    {
        if (before is not { } a || after is not { } b)
        {
            return null;
        }

        var diff = Math.Abs(b - a) % 360;
        return diff > 180 ? 360 - diff : diff;
    }

    /// <summary>
    /// 原地转了几圈、传送回来按路线重新跑到首领那里后，还是没有找到征讨之花：
    /// 开启首领轮换时，按冒险之证顺序换下一个首领；否则结束任务（第 9 版）。
    /// </summary>
    /// <returns>已换到下一个首领时返回 true；需要结束任务时返回 false。</returns>
    private async Task<bool> PrivateServerHandleFlowerNotFound()
    {
        _psFlowerNotFound = false;
        _logger.LogWarning("{Name}：{Boss} 的征讨之花找了两次都没有找到", Name, _taskParam.BossName);
        if (!PrivateServerBossRotation)
        {
            _logger.LogInformation("{Name}：没有开启首领轮换，结束任务", Name);
            return false;
        }

        var nextBoss = await PrivateServerSelectBossInHandbook(advance: true);
        if (nextBoss == null)
        {
            return false;
        }

        _logger.LogInformation("{Name}：换成讨伐 {Boss}", Name, nextBoss);
        _taskParam.BossName = nextBoss;
        return true;
    }

    // ==================== 私服首领轮换 / 寻找无图标征讨之花（自定义修改）结束 ====================

    // ==================== 私服自动领取空月祝福（自定义修改）开始 ====================

    /// <summary>空月祝福界面的识别结果。</summary>
    private enum PrivateServerWelkinScreen
    {
        /// <summary>不是空月祝福界面。</summary>
        None,

        /// <summary>“点击领取今日空月祝福奖励”界面。</summary>
        Claim,

        /// <summary>领取后的“获得 原石”界面（或者被战斗时的点击打开的原石详情）。</summary>
        Obtain,
    }

    /// <summary>空月祝福界面下方“点击领取今日空月祝福奖励”文字的识别范围（1080P 坐标，会按游戏分辨率缩放）。</summary>
    private Rect PrivateServerWelkinTextRect => ScaleRect(560, 800, 800, 140);

    /// <summary>领取时点击的空白位置（1080P 坐标）：左上角，避开画面中间的原石图标。</summary>
    private const int PrivateServerWelkinBlankX = 100;

    /// <summary>领取时点击的空白位置（1080P 坐标）。</summary>
    private const int PrivateServerWelkinBlankY = 100;

    /// <summary>“获得 原石”界面看不到提示文字时，最多点击几次空白处（防止误识别时一直乱点）。</summary>
    private const int PrivateServerWelkinMaxObtainBlankClicks = 5;

    /// <summary>
    /// 后台检查空月祝福界面：任务运行期间每秒检查一次，发现后暂停战斗、寻路等操作并自动领取，领取完继续。
    /// 空月祝福在游戏服务器时间每天凌晨 4 点弹出，私服的时间可能和官服不一样，所以这里不限制时间段。
    /// </summary>
    /// <param name="ct">任务结束时取消。</param>
    private async Task PrivateServerWelkinMoonWatchdog(CancellationToken ct)
    {
        while (!ct.IsCancellationRequested)
        {
            try
            {
                await Task.Delay(1000, ct);
                if (RunnerContext.Instance.IsSuspend)
                {
                    // 手动暂停中（或者正在处理），不打扰
                    continue;
                }

                PrivateServerWelkinScreen screen;
                using (var capture = CaptureToRectArea())
                {
                    screen = PrivateServerDetectWelkinMoon(capture, allowObtain: Volatile.Read(ref _psOwnUiDepth) == 0);
                }

                if (screen != PrivateServerWelkinScreen.None)
                {
                    await PrivateServerClaimWelkinMoon(
                        screen == PrivateServerWelkinScreen.Claim ? "检测到空月祝福界面" : "检测到空月祝福的“获得 原石”界面", ct);
                }
            }
            catch (OperationCanceledException)
            {
                break;
            }
            catch (Exception e)
            {
                _logger.LogDebug(e, "{Name}：检查空月祝福界面时出错", Name);
                try
                {
                    await Task.Delay(3000, ct);
                }
                catch (OperationCanceledException)
                {
                    break;
                }
            }
        }
    }

    /// <summary>
    /// 判断当前画面是不是空月祝福界面。
    /// </summary>
    /// <param name="capture">游戏截图。</param>
    /// <param name="allowObtain">是否把“获得 原石”界面也算进去。自己操作领奖、补充树脂、冒险之证时不算：补充树脂的界面里也有原石图标。</param>
    private PrivateServerWelkinScreen PrivateServerDetectWelkinMoon(ImageRegion capture, bool allowObtain)
    {
        // 能看到左上角的派蒙图标 = 在游戏主界面（领奖、补充树脂的界面后面也能看到派蒙），不是空月祝福
        if (PrivateServerPaimonVisible(capture))
        {
            return PrivateServerWelkinScreen.None;
        }

        // BetterGI 自带的空月祝福图标识别，或者下方的“点击领取今日空月祝福奖励”文字
        if (Bv.IsInBlessingOfTheWelkinMoon(capture)
            || FindOcrText(capture, PrivateServerWelkinTextRect, "空月祝福") != null)
        {
            return PrivateServerWelkinScreen.Claim;
        }

        if (allowObtain && PrivateServerPrimogemVisible(capture))
        {
            return PrivateServerWelkinScreen.Obtain;
        }

        return PrivateServerWelkinScreen.None;
    }

    /// <summary>左上角的派蒙图标是否可见（只看图标，比 Bv.IsInMainUi 快，适合后台频繁检查）。</summary>
    private static bool PrivateServerPaimonVisible(ImageRegion capture)
    {
        using var paimon = capture.Find(BetterGenshinImpact.GameTask.Common.Element.Assets.ElementRecognition.Get("PaimonMenu", capture));
        return paimon.IsExist();
    }

    /// <summary>画面中间三分之一的高度范围内是否有原石图标（BetterGI 自带的原石图片）。</summary>
    private static bool PrivateServerPrimogemVisible(ImageRegion capture)
    {
        using var primogem = capture.Find(BetterGenshinImpact.GameTask.Common.Element.Assets.ElementRecognition.Get("Primogem", capture));
        return primogem.IsExist();
    }

    /// <summary>
    /// 在“回到游戏主界面”等自己的检查里顺便处理空月祝福：画面是空月祝福界面时领取并返回 true。
    /// </summary>
    private async Task<bool> PrivateServerTryClaimWelkinMoonNow()
    {
        if (!PrivateServerAutoClaimWelkinMoon)
        {
            return false;
        }

        bool found;
        using (var capture = CaptureToRectArea())
        {
            found = PrivateServerDetectWelkinMoon(capture, allowObtain: false) == PrivateServerWelkinScreen.Claim;
        }

        if (!found)
        {
            return false;
        }

        await PrivateServerClaimWelkinMoon("检测到空月祝福界面", _ct);
        return true;
    }

    /// <summary>
    /// 领取空月祝福：暂停战斗、寻路等操作 → 点击左上角空白处领取 → 等两三秒的动画 →
    /// 点击“点击空白区域继续”这行字关闭“获得 原石”界面（不会点中间的原石）→ 恢复之前的操作。
    /// 注意：这里只能用 Task.Delay 等待，不能用 Delay / Sleep（暂停期间它们会一直等下去，造成卡死）。
    /// </summary>
    /// <param name="reason">日志里显示的原因。</param>
    /// <param name="ct">取消令牌。</param>
    private async Task PrivateServerClaimWelkinMoon(string reason, CancellationToken ct)
    {
        await _psWelkinLock.WaitAsync(ct);
        var runner = RunnerContext.Instance;
        var suspendedHere = false;
        var acted = false;
        try
        {
            if (!runner.IsSuspend)
            {
                // 暂停任务：正在进行的战斗、寻路会在下一次等待时停下来（BetterGI 日志会显示“快捷键触发暂停，等待解除”）
                runner.IsSuspend = true;
                suspendedHere = true;
            }

            // 等正在进行的按键、点击停下来
            await Task.Delay(800, ct);

            var stopwatch = Stopwatch.StartNew();
            var clearTimes = 0;
            var claimClicked = false;
            var obtainSeen = false;
            var obtainBlankClicks = 0;
            var lastClaimClick = TimeSpan.Zero;
            while (stopwatch.Elapsed < TimeSpan.FromSeconds(40))
            {
                ct.ThrowIfCancellationRequested();
                var clickBlank = false;
                var clickedHint = false;
                using (var capture = CaptureToRectArea())
                {
                    if (PrivateServerDetectWelkinMoon(capture, allowObtain: false) == PrivateServerWelkinScreen.Claim)
                    {
                        // “点击领取今日空月祝福奖励”：点击左上角空白处领取
                        clickBlank = true;
                        claimClicked = true;
                        lastClaimClick = stopwatch.Elapsed;
                    }
                    else
                    {
                        var hint = FindOcrText(capture, PrivateServerObtainHintRect, "空白区域");
                        if (hint != null)
                        {
                            // “获得 原石”界面：点击“点击空白区域继续”这行字关闭，不点中间的原石
                            hint.Click();
                            clickedHint = true;
                            obtainSeen = true;
                        }
                        else if (obtainBlankClicks < PrivateServerWelkinMaxObtainBlankClicks
                                 && !PrivateServerPaimonVisible(capture)
                                 && (PrivateServerPrimogemVisible(capture)
                                     || FindOcrText(capture, PrivateServerObtainTitleRect, "获得") != null))
                        {
                            // 看不到提示文字，但还在“获得 原石”界面（或者原石详情）：点击左上角空白处关闭
                            clickBlank = true;
                            obtainSeen = true;
                            obtainBlankClicks++;
                        }
                    }
                }

                if (clickBlank || clickedHint)
                {
                    if (!acted)
                    {
                        acted = true;
                        _logger.LogInformation("{Name}：{Reason}，暂停当前操作，自动领取", Name, reason);
                    }

                    if (clickBlank)
                    {
                        GameCaptureRegion.GameRegion1080PPosClick(PrivateServerWelkinBlankX, PrivateServerWelkinBlankY);
                    }

                    clearTimes = 0;
                    await Task.Delay(clickedHint ? 1000 : 800, ct);
                    continue;
                }

                // 点击领取后有两三秒的动画，动画结束才出现“获得”界面，这段时间不算已经关闭
                if (claimClicked && !obtainSeen && stopwatch.Elapsed - lastClaimClick < TimeSpan.FromSeconds(8))
                {
                    await Task.Delay(500, ct);
                    continue;
                }

                if (++clearTimes >= 3)
                {
                    break;
                }

                await Task.Delay(500, ct);
            }

            if (!acted)
            {
                _logger.LogDebug("{Name}：{Reason}，但再次检查时界面已经关闭", Name, reason);
            }
            else if (clearTimes >= 3)
            {
                _logger.LogInformation("{Name}：空月祝福已领取，继续之前的操作", Name);
            }
            else
            {
                _logger.LogWarning("{Name}：空月祝福界面 40 秒内没能关闭，先继续之前的操作", Name);
            }
        }
        finally
        {
            if (suspendedHere)
            {
                runner.IsSuspend = false;
            }

            if (acted)
            {
                Interlocked.Exchange(ref _psWelkinHandledTicks, DateTime.UtcNow.Ticks);
            }

            _psWelkinLock.Release();
        }
    }

    /// <summary>
    /// 进入自己的界面操作（领奖、补充树脂、冒险之证）：这期间后台检查不把原石图标当作空月祝福的“获得”界面
    /// （补充树脂的界面里也有原石选项）。用 using 包起来，结束时自动退出。
    /// </summary>
    private IDisposable PrivateServerEnterOwnUi()
    {
        Interlocked.Increment(ref _psOwnUiDepth);
        return new PrivateServerOwnUiScope(this);
    }

    /// <summary><see cref="PrivateServerEnterOwnUi"/> 的退出器。</summary>
    private sealed class PrivateServerOwnUiScope(AutoBossTask owner) : IDisposable
    {
        private int _disposed;

        public void Dispose()
        {
            if (Interlocked.Exchange(ref _disposed, 1) == 0)
            {
                Interlocked.Decrement(ref owner._psOwnUiDepth);
            }
        }
    }

    // ==================== 私服自动领取空月祝福（自定义修改）结束 ====================

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
