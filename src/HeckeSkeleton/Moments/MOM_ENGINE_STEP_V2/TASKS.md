# MOM_ENGINE_STEP_V2：24 项任务、闭合入口与分组计划

## 交付边界与当前状态

完整入口位于 `PairedStep.lean`。对原 `TargetContext`，它直接提供：

```lean
theorem Assembly.pairedStepHypothesis (c : TargetContext K) :
    EngineInduction.Source.PairedStepHypothesis (WithLp 2 (ℝ × ℝ)) c
```

此入口使用 `canonicalSourceParameters c`，在证明内部以 24 项实际任务定理构造 `TaskProofs`，再调用已证的完整条件组装。公开定理没有 `TaskProofs`、额外 certificate、已完成 output 或额外 analytic bound 前提。N4 使用 `originalCapacityTask_uniform`；N9 使用原窗口入口 `Tasks.originalWindowKernelMass`。Raw/Ordinary 保留原真定义与同一 source 的绑定。

全部代码位于 `HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2/`。当前完整登记 **416 模块 / 69,145 物理 Lean 行 / 15 个严格证明组**，每个模块恰登记一次；没有待证 g1 组。下表公开名字省略共同前缀 `HeckeSkeleton.Moments.EngineStepV2.Blueprint.`，文件名省略 `.lean`。原公开命题、量词与数学数值条件保持。

蓝图和接入分批验证：完整条件组装在 `393f72f1`、S1/S2 在 `ab99c810`、第一接入批在 `c1775792`、第二接入批在 `87ab0348` 完成真实 B 验证；T3 原件随后在 `e2367125` 接入并独立复验。本次最终闭合仍由同一新 head 的完整 V2 fresh 门禁与全项目门禁统一验收；任务分支旧绿色不能替代该次验证。最终 CI 记录和固定 head 见 PR #31。

## 精确任务入口、依赖与规模

证明预算是最初逐项估计，包含该项所有私有 helper；已报告实现的实际规模及修正后的总预算见下文。依赖表示数学消费关系，不要求把待证 Tasks 文件 import 到纯合同里。

| 编号 | 任务文件 / 公开 theorem | 纯合同文件 / 命题 | 数学依赖 | 论文 §4.8 行号 | 原估计证明行数 |
|---|---|---|---|---|---|
| S1 | `TasksFirstTransform` / `Tasks.firstTransform` | `FirstSourceContracts` / `FirstTransformTask` | 原输入、SourceParameters | 2800–2828 | 2,500–4,000 |
| S2 | `TasksFirstAllowance` / `Tasks.firstAllowance` | `FirstCauchyContracts` / `FirstAllowanceTask` | S1实现关系、原profiles | 2827–2850 | 2,500–4,000 |
| S3 | `TasksAmplification` / `Tasks.amplification` | `PoolContracts` / `AmplificationTask` | S2、同一mesh/window | 2852–2881 | 3,000–4,000 |
| S4 | `TasksSecondTransform` / `Tasks.secondTransform` | `SecondContracts` / `SecondTransformTask` | S3、同一原source | 2883–2894；3004–3010 | 3,000–4,000 |
| S5 | `TasksNominalGeometry` / `Tasks.nominalGeometry` | `GeometryContracts` / `NominalGeometryTask` | S2–S4 | 2895–2906 | 1,500–3,000 |
| S6 | `TasksFiniteLeaves` / `Tasks.finiteLeaves` | `RawContracts` / `FiniteLeafTask` | S4、S5 | 2908–2925 | 2,500–4,000 |
| N1 | `TasksOriginalAtoms` / `Tasks.originalAtoms` | `OrdinaryContracts` / `OriginalAtomTask` | S6 | 2800–2820；2908–2925 | 3,000–4,000 |
| N2 | `TasksPassiveRefinement` / `Tasks.passive_refinement` | `RefinementContracts` / `PassiveRefinementTask` | N1、S6原profiles | 2908–2925 | 4,000–5,000 |
| N3 | `TasksOriginalCalibration` / `Tasks.original_calibration` | `CalibrationContracts` / `OriginalCalibrationTask` | N2、同一原profiles | 2908–2946 | 3,000–4,000 |
| N4 | `TasksOriginalCapacity` / `originalCapacityTask_uniform` | `N4CalibrationContracts` / `UniformOriginalCapacityTask` | S5、同一N3calibration | 2883–2946 | 3,000–4,000 |
| N5a | `ProfileFormulaTask` / `Tasks.profile_formula_control` | `ProfileFormula` / `ProfileFormulaTask` | base CanonicalLogProfiles | 3043–3073 | 2,000–3,000 |
| N5b | `TasksProfileWindows` / `Tasks.profile_windows` | `ProfileWindowContracts` / `ProfileWindowTask` | N3原全局字典、N5a | 2927–2946；3043–3073 | 2,500–4,000 |
| N6 | `TasksFullKappa` / `Tasks.fullKappaNormalization` | `FullKappaData / FullKappaContracts` / `FullKappaTask` | 同一N3、N4、N5b数据 | 2927–2946；3043–3073 | 2,500–4,000 |
| N7a | `TasksChildArithmetic` / `Tasks.child_arithmetic` | `ChildArithmeticContracts` / `ChildArithmeticTask` | 同一N3、N4、N6children | 2908–2925；3011–3018 | 3,000–4,000 |
| N7b | `TasksChildProfiles` / `Tasks.child_profiles` | `ChildProfileContracts` / `ChildProfileTask` | 同一N4、N5b、N6children | 3011–3018；3043–3073 | 2,000–3,000 |
| N8a | `TasksSourceIndex` / `Tasks.sourceIndex` | `SourceIndexContracts` / `SourceIndexTask` | S1–S6原trace/geometry/raw | 2842–2850；2852–2881；2895–2906 | 3,000–4,000 |
| N8b | `TasksNormalizedMass` / `Tasks.normalizedMass` | `NormalizedMassContracts` / `NormalizedMassTask` | N2–N7、同一N8a ledger | 2908–2946 | 3,000–4,000 |
| N9 | `N9OriginalWindowMass` / `Tasks.originalWindowKernelMass` | `N9OriginalWindowContracts` / `OriginalWindowKernelMassTask` | S1、S4、同一N5b窗口/N6容量 | 3043–3073 | 2,000–3,000 |
| T1 | `TasksFirstZero` / `Tasks.firstZero` | `FirstZeroContracts` / `FirstZeroTask` | S1实现关系、原ProfileInput/Ready | 2822–2850 | 2,000–3,500 |
| T2 | `TasksSecondZero` / `Tasks.secondZero` | `SecondZeroContracts` / `SecondZeroTask` | S2–S4、原windows | 3004–3007 | 2,500–4,000 |
| T3a | `TasksExceptionalRecovery` / `Tasks.exceptional_recovery` | `ExceptionalRecoveryContracts` / `ExceptionalRecoveryTask` | S4–S6、N1 | 2948–2965 | 3,000–4,000 |
| T3b | `TasksExceptionalSummation` / `Tasks.exceptional_summation` | `ExceptionalSummationContracts` / `ExceptionalSummationTask` | T3a、同一N8a、N1/N2/N5b、原几何 | 2967–3002 | 4,000–5,000 |
| T4 | `TasksTails` / `Tasks.tails` | `TailContracts` / `TailTask` | S1、S3、S4、原kernels/windows | 3004–3010 | 3,000–4,000 |
| U1 | `TasksUniform` / `Tasks.uniformPreparation` | `UniformContracts` / `UniformChoiceTask` | 已选六类数值costs/demands | 3043–3073 | 2,500–4,000 |

N8 已按原 source 索引质量与 normalized 标签质量拆成 N8a、N8b，所以总数是 **24**，早期文档的 23 项不能作为缺少 N8b 的依据。T3b 复用同一 N8a ledger，不另选 harmonic sum 或重复支付 pool 因子。

## 完整组装与编译分组

`Assembly.pairedStepHypothesis_of_blueprint` 使用 `canonicalSourceParameters c`，从 `TaskProofs` 推出原目标；`pairedStepHypothesis_of_taskProofs` 保留一般 `SourceParameters c`。三种内部证书都在组装证明内由任务证明构造。新增的无条件 `pairedStepHypothesis` 将每个字段绑定到对应实际任务定理。

组装先处理原 paired rows 为空的情况；非空时使用同一 source trace、residual refinement、N3 calibration、N6 capacity、normalized family 和 kernels，支付四类 terminal cost 与两类质量。N4 demand、N6 analytic choices、各 orders 的 N5b 窗口和 N9 cost 均在 moving call 前选择。N8 和 N9 使用同一 `LeafNormalization` 的两个投影；N5a 仍是完整任务结构的一项。

| manifest 组 | 模块数 | 内容 |
|---|---:|---|
| g0 | 91 | 真实数据、纯合同、共用辅助、U1 与完整条件组装。 |
| s1_s2_helpers | 9 | S1/S2 的共同证明辅助。 |
| s1 | 1 | 原第一变换；required Tasks.firstTransform。 |
| s2 | 1 | 原 allowance；required Tasks.firstAllowance。 |
| s3_s5 | 17 | 独立放大与原 nominal geometry。 |
| s4_t4 | 30 | 原第二变换与两类真实尾项。 |
| t1_t2 | 28 | 第一零项与完整第二零项。 |
| n5a_n5b | 6 | 原 profile 公式与精确 clipping/window。 |
| n7a_n7b | 4 | 同一 child 的 arithmetic 与 profile transport。 |
| s6_n1 | 31 | 原有限叶子、原 occurrence 和系数。 |
| n2_n3 | 42 | 完整 residual refinement 与原 calibration。 |
| n4_n6 | 24 | uniform 原 capacity 与完整 κ normalization。 |
| n8_n9 | 59 | 原 source/normalized mass 与精确原窗口 kernel mass。 |
| t3a_t3b | 71 | 原 exceptional source 的分类恢复与 summation。 |
| g2 | 2 | Interface 与无条件 PairedStep；required root 仅 PairedStep。 |

所有组均为 `proved: true`，上限仍为每组 100 模块。每组在 fresh Lean 环境中递归检查全部已加载 V2 声明，覆盖 private/generated；白名单仅 `propext`、`Classical.choice`、`Quot.sound`。30 个 required theorem 同时检查声明种类及来源 root，包含最终无条件入口。源码/配置/HEAD 前后完整性与 300 秒逐进程 watchdog 保持。

原任务分支 scope 保持：T3a/T3b 为 97 个显式目标，N8a/N8b/N9 为 108 个。相同共享模块只登记一次；shared proof 采用负责该任务的已验收版本，保留 N4ScaleProduct/N4ExtractionScale 的现有拆分，不以任务分支旧副本覆盖。

## 原始证明来源与实际规模

采用以下固定 head 的任务所有者原始证明。B 合并共享依赖登记并增加闭合入口；B 在 `PassiveSupportRecovery` 补齐任务要求的 `linter.unusedSectionVars false` 设置，证明体和公开陈述不变。N8 所有者在原分支补齐了 `N8NormalizedCommonBounds` 的同一设置。U1 和真实基线沿用 B 已验收证明。

| 单元 | 来源 PR | 原始 head |
|---|---:|---|
| S1/S2 | #36 | `4fe26b9b1fe34c7d8c0848289bd459428cd234a1` |
| S3/S5 | #35 | `cecf781c42dc4af5d294da2639d5796599473b1c` |
| S4/T4 | #33 | `fab1ee0661c79035a18ebf7ff45c052eacd7efe3` |
| S6/N1 | #32 | `c50de627c4ad94e4bc01a4c62ea5ffcc067cfde5` |
| N2/N3 | #34 | `2cee7b3eac5e6c094e0f3164728f950478d0253e` |
| N4/N6 | #39 | `19bcb867999aa3a3d762cce1f9f15df899508851` |
| N5a/N5b | #38 | `f61cc2ac54f44622cfd58b512e90dad28e706a3f` |
| N7a/N7b | #40 | `7b23c66db3aa23eada2bfef798ff409149cbc88b` |
| N8a/N8b/N9 | #42 | `375ecc23d112a9618ba8fea6ef7c0f83e259fbdd` |
| T1/T2 | #37 | `4df84d859507fc80904841b69d78d28130d58c18` |
| T3a/T3b | #41 | `11f915e5041c649df06dcc09cfb598f009b8d10d` |
| 完整条件组装 | #44 | `8fcb6bf40b03c29c0f1d837707b119f9da3c9513` |

最终按 V2 全目录去重计数为 **69,145 行**，含全部 helper、公开合同、Interface 和组装，低于 100,000 行目标。早期逐项预算为 65,000–93,500 行；现以实际完整源码计数为准。

全项目 `integration-build.yml` 在 B 的最终 draft head 上运行所有原 project libraries，并保留原有公理检查，另打印闭合 `Assembly.pairedStepHypothesis`。head 更新始终触发构建；Ready 状态变化不重复运行同一输入。标为可审查前须核对已通过构建的 B head、base head 与实际 synthetic merge，若 base 变化则同步后重新验证。PR 保留 `[不合并]`。

## 可参考的 A 线代码

已核对 [PR9](https://github.com/Rogerhu12/hecke-seven-eighths/pull/9) 的论文对应说明，并固定读取：

- [base `996cb49685a51cf789ea962af9f725b02dc363c7`](https://github.com/Rogerhu12/hecke-seven-eighths/tree/996cb49685a51cf789ea962af9f725b02dc363c7/HeckeSkeleton/Moments)。
- [A 线候选 `c59c60c29f12c794036539900965e8c1094a2de9`](https://github.com/Rogerhu12/hecke-seven-eighths/tree/c59c60c29f12c794036539900965e8c1094a2de9/HeckeSkeleton/Moments/MOM_ENGINE_STEP)。

下列共 70 个不同参考模块：42 个已合 base，28 个仍属 A 候选；42 个 base 文件在两个固定版本的 blob 相同。所有路径已验证存在并核对用途。默认前缀为 `HeckeSkeleton/Moments/MOM_ENGINE_STEP/`；`INDUCTION/` 代表 `HeckeSkeleton/Moments/MOM_ENGINE_INDUCTION/`。A 候选只提供实现参考，不表示已经通过 B 的证明验收。

| 任务 | 已合 base 的参考 | A 未合候选参考 | 用途 |
|---|---|---|---|
| S1 | `CanonicalFirstLogChart.lean`；`ActualDirectFirstSource.lean` | `CanonicalJointFirstSource.lean` | 原第一 Fourier 图、完整原系数入口、joint budget 对应的原始行半径。 |
| S2 | `FirstAllowanceNormalization.lean`；`FirstDivisorPhysicalSource.lean` | `CanonicalFirstCombinedAllowance.lean` | 两个真实 Cauchy allowance、逐 divisor 物理截断和 common-radical 权重。 |
| S3 | `CanonicalOriginalPool.lean`；`PoolGaussDecomposition.lean` | `OriginalAmplifiedCarrier.lean` | 同一个固定 pool、main 与 1/6/7 residual 的精确分解、原 prime/tag 载体。 |
| S4 | `SecondCorrelationSource.lean`；`CanonicalSecondLogChart.lean` | `CanonicalUnmaskedSecondStage.lean` | 完整非 primitive 第二相关和、原 modulus、第二 log 图和原系数。 |
| S5 | `ActualNominalGeometry.lean` | `CanonicalFirstRowGeometry.lean`；`CanonicalPatternChildWindows.lean` | 原 ideal norm 的 nominal ledger、retained scale、nonunit pattern 和完整删除窗口。 |
| S6 | `SourceCartesianCover.lean`；`SecondClassProduction.lean` | `ActualGaussFiniteLeaves.lean` | 实际独立 divisor/allocation、Cartesian cover、完整 leaf key 与同一 kernel 对。 |
| N1 | `HybridLeafOrdinaryBinding.lean`；`CanonicalLiteralLocations.lean` | `CanonicalLiteralSourceCoefficients.lean` | ordinary binding、左右 Fourier 符号与位置、原 comparison rectangle 的系数字典。 |
| N2 | — | `CanonicalLiteralPassiveSource.lean`；`CanonicalLiteralPassiveSupport.lean`；`CanonicalLiteralPassiveDeletion.lean` | 完整 smooth carrier、固定模数与 residual coprimality、逐 occurrence 的有限展开。 |
| N3 | `CompleteMovingRowRecipe.lean` | `CanonicalLiteralCoveredCalibration.lean`；`CanonicalLiteralProfileData.lean` | 同一原 rectangle 的 calibration、完整 moving/remaining recipe 和全局 profile 公式。 |
| N4 | `UnrestrictedSixthCapacity.lean`；`SixthDeletionCapacity.lean` | `CanonicalLiteralCapacityLengths.lean` | pattern capacity、完整 sixth-root 修正、实际 row/support/raw-degree 长度。 |
| N5a | `CanonicalLogProfiles.lean`；`CanonicalLogProfileBounds.lean` | `CanonicalLiteralSchwartzProfiles.lean` | log-norm Fourier multiplier、实幂和 Schwartz seminorm、实际 representative。 |
| N5b | `CanonicalClippedProfileBounds.lean` | `CanonicalLiteralSchwartzProfiles.lean`；`CanonicalLiteralCoveredComputedProfiles.lean` | 实际 dilation/clipping、显式 coefficient、同一 occurrence 的 raw/clipped windows。 |
| N6 | `CanonicalFullKappaNormalization.lean`；`CanonicalFullKappaPrime.lean` | `CanonicalLiteralFullKappaInput.lean` | 原 prime analytic data、完整 κ 区间、同一 normalization 的 enlarged radius。 |
| N7a | `CharacterRecipePreservation.lean`；`INDUCTION/CompleteSourceReflection.lean` | `CanonicalLiteralPassiveInheritance.lean` | 同一 child 的 character/mask/slot 运输、完整 recipe 的 reflection arithmetic。 |
| N7b | `CanonicalChosenChildProfiles.lean`；`INDUCTION/ActiveFamilyAnnulus.lean`；`INDUCTION/ActualEngineProfiles.lean` | — | 同一 active child 的紧 annulus 和原宽度下降对应的 ranked profile primitive。 |
| N8a | `TwoDivisorLabelMass.lean`；`CommonHarmonicMass.lean` | `OriginalAmplifiedCarrier.lean` | 两个独立 divisor、真实 finite phase、common-radical harmonic sum、单 pool prefactor。 |
| N8b | `NormalizedOriginalLabelMass.lean` | `PassiveAllocationScalarMass.lean`；`PassiveDeletionMass.lean` | 同一 normalized pair 的逐原 index 权重、passive scalar 和全部 occurrence 标签质量。 |
| N9 | `CanonicalChildFourierControl.lean`；`NormalizedIndexedKernelMass.lean` | `CanonicalLiteralMassProfilePower.lean` | 同一 capacity child 的 Fourier atom control、同 kernel 质量、call 前固定 degree/cost。 |
| T1 | `ActualFirstZero.lean`；`FirstZeroAmplitude.lean` | `CanonicalPrimitiveFirstTerminalBounds.lean` | 真实 first zero、原 seminorm estimate、原 source 的 terminal normalization。 |
| T2 | `SecondZeroDiagonal.lean`；`SecondZeroNormalization.lean` | `CanonicalSharpSecondZeroLedger.lean` | 完整 Euler diagonal、原 central norm 抵消、direct/main/error 的同一 sharp ledger。 |
| T3a | `ActualExceptionalRows.lean`；`CanonicalExceptionalUniformRows.lean` | `CanonicalLiteralExceptionalClassification.lean` | 原 residual sixth-free class、提取 base 的幂整除与下界、unit sector/fibre 计数。 |
| T3b | `ExceptionalOriginalIntegral.lean`；`CanonicalExceptionalVolume.lean` | `CanonicalExceptionalOriginalIntegral.lean` | 同一 exceptional source 的 centered volume、原两个 kernel、allowance/divisor/Theta 标签。 |
| T4 | `TailBudget.lean`；`SecondTailBudget.lean` | `CanonicalPrimitiveSecondTerminalUniform.lean` | 第一、第二真实 masked truncation mass、原 common 标签和固定 orders/cost。 |
| U1 | `CanonicalPrimitiveEngineProfileOrders.lean` | `CanonicalPrimitiveEngineChoices.lean`；`CanonicalPrimitiveUniformEngine.lean` | 有限 backward orders、数值 maxima、原 Mellin windows、共同 Ready 和 funding。 |

N2 必须在完整 smooth carrier 上展开 residual mask，不能在已被同一 mask 截断的 carrier 上写恒等式来代替恢复缺失项。T3b 的 base `CanonicalExceptionalVolume` 仍把原固定字符 ideal-sum remainder 作为明确的解析边界，不能因此声称 base 已无条件完成整个 centered exceptional volume。

## 证明与验收规矩

1. 保持公开陈述、量词和同一对象绑定；必要变更先在 PR31 提出并列出论文依据及受影响证明。
2. 每批完成就直接推 GitHub，等待专用 CI 自然终态并读完完整日志/工件后再推下一批；不在本地运行 Lean/Lake，不取消失败待定的运行。
3. 新模块登记 manifest/Interface；每文件关闭 unusedSectionVars linter；abbrev 上的 Fintype 等实例只作 local 注册。
4. 原本已冻结的 N5a（`d4568a30`）与 U1（`b2fa7c15`）含义保持。正式轻 N3 保持 21 字段与八个全局身份，不重新引入私有构造或额外 Task 前提。
5. 最终目标仍需全部任务无占位、完整原目标公理合格及全项目门禁通过。Whole-project 的规定 skipped 不等于通过；在此之前 PR31 保持 draft / [不合并]。
