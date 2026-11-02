# MOM_ENGINE_STEP_V2 数据构造与分组证明计划

## 原目标与当前阶段

公开入口仍为 `HeckeSkeleton.Moments.EngineStepV2.pairedStepHypothesis`，目标为原 `EngineInduction.Source.PairedStepHypothesis (WithLp 2 (ℝ × ℝ)) c`。全部原始参数、mesh、支持受限 volume 量词及 induction 输入保持不变；没有添加 parent bound、child admissibility、terminal 或 mass 结论作前提。

按 PR #31 评论 6573415153，**当前阶段是具体数据构造与 CI 修复，尚未达到正式陈述骨架里程碑**。截至 `fc56067838b5054e506eb8934a387ca6a5684175`，84 个模块、25,778 物理行（含注释与空行）已直接推送。统一 schedule/bounds/call 和两次变换的实际有限展开已具体定义；`selectedNormalization` 的最终实际叶子接线正在完成。逐定义构造来源与状态见 [DATA_CONSTRUCTIONS.md](DATA_CONSTRUCTIONS.md)。

数据字段必须是实际 record、有限集合、原核、原 profile、原 label 的构造。结构内 Prop 字段及 theorem 的证明可在此阶段使用显式 `sorry`；不得用新写的占位存在性定理配合 choice 隐藏数据。引用已合入且已证明的原分析/算术存在性定理选择统一常数和原 Mellin profile 是实际构造。

## 共享设计

- 左右使用同一 Bool 参数化 ChildFamily、共同正 Fourier 测度、同一最终 child 与 kernel。
- 第一次源保留原系数、原物理行、实际 cutoff、原 common/mask/divisor/phase labels；第二次源保留完整相关式。
- direct 与 pooled 共用 ActualGaussStage → covered leaf → literal normalization；main/1/6/7 保留同一个 prime pool、各自原 prime 和 valuation。零槽采用 direct；空原行采用真实空有限族。
- 规范化 carrier 同时保留两侧独立被动 divisor 与矩形标记；whole-slot capacity 删除仅作用于真实 literal profile，不能换成裸 seminorm 或任意同型输出。
- profile orders 先于 Cp/Hp；统一常数与 threshold 先于 moving recipe、node、频率。调用 control 是实际 Mellin amplitude 的明确幂；所有生产规格仅针对 selectedCall。
- 原输出通过 PairedEngineConclusion.ofFintype 一次收口，额外性质沿同一输出运输。
- 仅引用已合入的 STEP/INDUCTION API；A 线用作构造来源，迁移后的新声明全部位于 EngineStepV2。abbrev 的实例仅 local 启用。

## 分组、顺序与预算

分组已按实际 import 图调整，当前不存在后组被前组导入的逆向依赖。公共 literal/物理数据和数值预算同属 G2，解决旧草图中 G2 与 G3 交叉依赖的问题。每组少于 100 模块；后续 helper 按依赖加入对应组并同步 manifest/Interface。

| 组 | 当前模块数 | 可依赖的前组 | 责任 | 当前模块完成预算 |
|---|---:|---|---|---:|
| G1 | 8 | 无 | 公共有限族与原始叶子接口 | 1870 |
| G2 | 60 | G1 | 公共物理数据、规范化构造与统一数值预算 | 47800 |
| G3 | 10 | G1–G2 | 选定原源、同一叶子与实际输出 | 7000 |
| G4 | 3 | G1–G3 | 四个终端与完整核质量 | 11200 |
| G5 | 3 | G1–G4 | 严格输出族与原目标 | 1050 |

现有模块逐项预算合计 **68,920 行**。另外预留 **8,000 行**给最终 normalization 接线、CI 发现的必要 helper 和不可省略的证明，合计规划 **76,920 行**，保持低于 100,000 行目标。这是根据真实迁移闭包修正后的工程估计，取代最初 19 模块草图的 57,620 行；不是完成证明后的实测压缩结果。新增 helper 会从对应预算/预留中列账，不能只统计包装入口。

当前保留的 theorem/Prop 占位尚未验收。真实对象全部接通后，CI 必须逐一编译全部声明；此后先推进 G1 八模块证明。每组完成时，清空本组占位并在 fresh Lean 中对本组所有加载声明（含 private/generated）的依赖递归检查公理，仅允许 propext、Classical.choice、Quot.sound。

## 逐模块当前行数与完成预算

| 组 | 模块 | 当前物理行 | 预计完成行数 |
|---|---|---:|---:|
| G1 | `ChildFamily` | 126 | 180 |
| G1 | `FiniteKernelFamily` | 98 | 220 |
| G1 | `ScalarLedger` | 100 | 160 |
| G1 | `Output` | 101 | 160 |
| G1 | `OriginalInput` | 69 | 200 |
| G1 | `HybridExpansion` | 89 | 350 |
| G1 | `LeafCoverage` | 53 | 200 |
| G1 | `LeafNormalization` | 81 | 400 |
| G2 | `AnalyticChoices` | 103 | 350 |
| G2 | `BlockGaussStage` | 305 | 400 |
| G2 | `ChoiceBox` | 275 | 400 |
| G2 | `CoveredStage` | 165 | 250 |
| G2 | `DirectLeaves` | 145 | 200 |
| G2 | `DirectParent` | 97 | 150 |
| G2 | `DirectPreparation` | 167 | 250 |
| G2 | `DirectStages` | 130 | 200 |
| G2 | `ExceptionalChoices` | 160 | 250 |
| G2 | `FirstGaussData` | 340 | 500 |
| G2 | `FirstGeometry` | 142 | 200 |
| G2 | `FirstNormalization` | 97 | 150 |
| G2 | `FirstSource` | 232 | 300 |
| G2 | `FullSupportParameters` | 339 | 400 |
| G2 | `GaussOrbitRows` | 386 | 450 |
| G2 | `GaussStage` | 335 | 400 |
| G2 | `LiteralAnalyticProduction` | 245 | 300 |
| G2 | `LiteralAtlas` | 1191 | 3400 |
| G2 | `LiteralAtoms` | 274 | 550 |
| G2 | `LiteralCalibration` | 1319 | 2700 |
| G2 | `LiteralCapacity` | 942 | 2750 |
| G2 | `LiteralCovered` | 1122 | 2350 |
| G2 | `LiteralCoveredProduction` | 423 | 500 |
| G2 | `LiteralCoveredStrip` | 234 | 500 |
| G2 | `LiteralGeometry` | 121 | 500 |
| G2 | `LiteralInput` | 125 | 250 |
| G2 | `LiteralPassive` | 2691 | 7200 |
| G2 | `LiteralPhases` | 1959 | 5150 |
| G2 | `LiteralProduction` | 1197 | 1600 |
| G2 | `LiteralProfiles` | 542 | 1300 |
| G2 | `LiteralTransforms` | 575 | 1800 |
| G2 | `LiteralWindows` | 2337 | 5300 |
| G2 | `MassIndexChoices` | 128 | 200 |
| G2 | `MassProfileChoices` | 133 | 300 |
| G2 | `NormalizedFamilyAdapter` | 161 | 250 |
| G2 | `OriginalPoolStages` | 126 | 250 |
| G2 | `ParentTerminals` | 159 | 250 |
| G2 | `PatternRows` | 207 | 300 |
| G2 | `PhysicalConstants` | 168 | 250 |
| G2 | `PoolAttachment` | 104 | 200 |
| G2 | `PoolLeaves` | 113 | 200 |
| G2 | `PooledFirstLeaves` | 180 | 250 |
| G2 | `PooledParent` | 110 | 200 |
| G2 | `PreparedCall` | 117 | 200 |
| G2 | `PrimitiveFirstSource` | 197 | 300 |
| G2 | `ProfileChoices` | 146 | 300 |
| G2 | `RawTerminalData` | 166 | 250 |
| G2 | `RawTerminals` | 104 | 200 |
| G2 | `RowClasses` | 258 | 350 |
| G2 | `SectorRows` | 322 | 400 |
| G2 | `SectorStage` | 95 | 150 |
| G2 | `SourceCoordinates` | 206 | 300 |
| G2 | `SourceFrame` | 140 | 200 |
| G2 | `SourceGates` | 197 | 250 |
| G2 | `SourcePool` | 71 | 150 |
| G2 | `SourcePredicates` | 123 | 200 |
| G2 | `SourceSupport` | 293 | 350 |
| G2 | `TargetArithmetic` | 70 | 150 |
| G2 | `UnmaskedStage` | 139 | 200 |
| G2 | `VolumeChoices` | 148 | 200 |
| G3 | `ChildProduction` | 58 | 2200 |
| G3 | `SelectedLeafPacket` | 126 | 200 |
| G3 | `SelectedLeaves` | 123 | 250 |
| G3 | `SelectedLiteralInputs` | 236 | 500 |
| G3 | `SelectedPredicates` | 169 | 250 |
| G3 | `SelectedProfileData` | 107 | 200 |
| G3 | `SelectedSource` | 191 | 300 |
| G3 | `SelectedStages` | 174 | 300 |
| G3 | `SourceProduction` | 141 | 1800 |
| G3 | `UniformChoices` | 200 | 1000 |
| G4 | `TerminalCalibration` | 69 | 6000 |
| G4 | `KernelCalibration` | 69 | 5000 |
| G4 | `LocalProduction` | 47 | 200 |
| G5 | `StrictFamily` | 115 | 700 |
| G5 | `SourceHypothesis` | 51 | 150 |
| G5 | `Interface` | 89 | 200 |

## 数据优先的执行顺序

1. 按 DATA_CONSTRUCTIONS 清单完成真实数据及 helper，写完一批即通过 GitHub 推送。
2. 全部下游在真实对象上编译通过后，在 PR #31 记录精确 head、完整模块数、CI run 和本计划的最终版本。
3. 随即填完并验收 G1；再按 G2 → G3 → G4 → G5 推进。不以含数据占位的旧骨架作为里程碑。
4. 原目标全部无占位、递归三公理审计和全项目门禁通过后才考虑 ready for review；目前保持 [不合并] draft。

## 论文与编译依据

论文对应 `weil_seven_eighths_revised.tex` §4.8（2741–3074 行）：原 common-support 变换、一次 pool 放大、完整第二 correlation、allocation、同核 children 与一次 whole-slot capacity 删除。PR #9 指出的 volume/mesh 原量词保留（1548–1559、2687–2745、2936–2941、3023–3025、3122–3138 行）。

所有编译交给 GitHub CI，未运行本地 Lean。专用 workflow 精确 checkout PR head、使用固定工具链和原项目缓存，build.py 验证 manifest 无重无漏、编译全部模块、记录源哈希与真实退出码。只有标记 proved 的组才要求无 sorry 并执行递归三公理审计。draft 期间专用门禁持续运行；ready-for-review 或手动触发时执行原全项目门禁。
