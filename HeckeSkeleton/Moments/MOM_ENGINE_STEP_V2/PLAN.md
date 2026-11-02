# MOM_ENGINE_STEP_V2 模块与分组计划

目标是原有 `EngineInduction.Source.PairedStepHypothesis`，参数空间为 `WithLp 2 (ℝ × ℝ)`。新公开入口为 `HeckeSkeleton.Moments.EngineStepV2.pairedStepHypothesis`，没有添加输出估计或子项 admissibility 假设。

## 当前阶段

**更新：按协调员评论 6573415153，先补实所有数据构造，再重新检验所有下游陈述。当前仍未达到正式骨架里程碑。逐定义来源、估计与状态见 [DATA_CONSTRUCTIONS.md](DATA_CONSTRUCTIONS.md)。新增构造 helper 属其对应构造组。**

这是一份陈述骨架：未完成组使用显式 `sorry`，包括尚待实现的数据构造。骨架 CI 只证明声明/定义的类型和接线正确，不代表配对引擎定理已证明。每组完成后须去掉本组所有占位，并在独立 Lean 进程中递归检查全部已加载 V2 声明（包含 private/generated），只允许 `propext`、`Classical.choice`、`Quot.sound`。

## 设计

- 左右使用同一个 `Bool` 参数化的 ChildFamily；两侧的能量与 Cauchy 配对使用同一个正测度。
- 原始叶子保留实际多项式与两个 Fourier 核；main/1/6/7 共用一个 pool，零槽使用 direct 且 pool 为空。
- 全部内部 carrier 在 `Output.toConclusion` 处统一调用 base 的 `PairedEngineConclusion.ofFintype`。同一输出的额外性质通过 `toConclusion_property` 传递。
- 统一阶数先于 Cp/Hp；统一 coefficient/heightDegree/threshold 先于移动源、节点和频率。
- 所有生产估计只针对 `selectedCall request`。任意 PreparedCall 的常数可为零，故不会对任意 PreparedCall 假设或声称完整生产定理。
- 实际构造要证明完整 source、四项 terminal、kernel mass、profile/support/capacity 结果。它们是内部工作项，不是最终入口的新增前提。
- 只引用已合入 base 的 STEP/INDUCTION 模块；不依赖 A 线未合入模块，也不修改其定义。

## 分组与依赖

| 组 | 模块数 | 上游 V2 组 | 责任 |
|---|---:|---|---|
| G1 | 8 | 无 | 公共有限族、原始 arithmetic identity、有限叶子、重编号、归一化；本会话继续完成 |
| G2 | 3 | G1 的 OriginalInput | 原源请求、Mellin profile、统一 orders/constants/schedule |
| G3 | 2 | G1、G2 | 原两次变换、完整 correlation、具体有限叶子和同一 child admissibility/capacity |
| G4 | 3 | G1、G2、G3 | 四项 terminal、两独立 divisor 的质量、同输出组装 |
| G5 | 3 | G1–G4 | 同核参数嵌入、真实 child labels、严格 Mellin 家族及原目标 |

G2 的统一数值选择须与 G3/G4 的内部预算一起协调；不能随意选择常数后让后继证明猜测其规格。G3/G4 内的长证明可以拆出同组 helper 模块；新模块须进入 manifest 与 Interface，每组上限 100。

## 逐模块估计

当前骨架共 19 个模块，1549 行。以下是完成证明后的粗略规划上限，不是已完成行数；总计约 57,620 行，目标小于 100,000 行。

| 组 | 模块 | 当前骨架行数 | 预计完成后行数 |
|---|---|---:|---:|
| G1 | `ChildFamily` | 126 | 180 |
| G1 | `FiniteKernelFamily` | 98 | 220 |
| G1 | `ScalarLedger` | 100 | 160 |
| G1 | `Output` | 81 | 160 |
| G1 | `OriginalInput` | 69 | 200 |
| G1 | `HybridExpansion` | 89 | 350 |
| G1 | `LeafCoverage` | 53 | 200 |
| G1 | `LeafNormalization` | 81 | 400 |
| G2 | `SourceFrame` | 140 | 400 |
| G2 | `PreparedCall` | 113 | 600 |
| G2 | `UniformChoices` | 78 | 6000 |
| G3 | `SourceProduction` | 78 | 15000 |
| G3 | `ChildProduction` | 58 | 15000 |
| G4 | `TerminalCalibration` | 69 | 10000 |
| G4 | `KernelCalibration` | 68 | 8000 |
| G4 | `LocalProduction` | 47 | 100 |
| G5 | `StrictFamily` | 114 | 500 |
| G5 | `SourceHypothesis` | 51 | 100 |
| G5 | `Interface` | 36 | 50 |

## 论文与 base 接口

数学顺序对应 `weil_seven_eighths_revised.tex` §4.8（2741–3074 行）：第一次 common-support 变换、一次 pool 放大、完整第二次 correlation、allocation、同核 children 与一次 whole-slot capacity 删除。支持受限 volume 与 mesh 的原量词按 PR #9 说明保留（1548–1559、2687–2745、2936–2941、3023–3025、3122–3138 行）。

复用 base 的 `ParentRawAtoms`、`ActualHybridLeaf`、`SecondSideFrame.arithmeticCalibration`、`PairedEngineConclusion.ofFintype`、`universalLabeledEngineOutput`、`RecipeMellinStrictFamily`；统一实例只在需要处 local 启用。

## 编译与验收

专用 workflow 使用固定工具链和缓存，精确 checkout PR head，调用 `.github/v2/build.py` 编译全部 V2 模块。manifest 必须无重无漏覆盖全部模块。已完成组另起 fresh Lean，递归收集全部加载的 V2 公理；日志记录 head、每份源哈希与实际退出码。当前 draft 只运行专用门禁；标 ready 或手动触发时再运行原 `integration-build.yml` 全项目门禁。
