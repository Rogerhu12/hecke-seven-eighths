# MOM_ENGINE_STEP_V2：24 项蓝图任务与分组计划

## 交付边界与当前状态

目标保持原陈述：

```lean
EngineInduction.Source.PairedStepHypothesis (WithLp 2 (ℝ × ℝ)) c
```

全部代码位于 `HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2/`。下列公开名字省略共同前缀 `HeckeSkeleton.Moments.EngineStepV2.Blueprint.`；文件名省略 `.lean`。每个任务的量词、同一 source/family 的绑定和数值条件以对应纯合同为准，不能把已完成的 output 或 analytic bound 补成新前提。

**24 项公开任务入口现已全部落入源码。** N4 的同文件兼容入口 `originalCapacityTask` 继续保留，完整组装消费的是 `originalCapacityTask_uniform`；该兼容入口不另算一项论文任务。N9 的最终入口为 `N9OriginalWindowMass` 中的 `Tasks.originalWindowKernelMass`，不以较弱的中间 `TasksKernelMass` 代替。

**完整条件组装已在真实 B `393f72f125fdc1b28a5b36dadb7f346edc994528` 验收。** [专用CI41513480717](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41513480717)自然success：115/115模块、16,336 Lake jobs；fresh g0审计2,849个唯一声明（含8个private及generated），仅三标准公理。两个完整组装theorem与U1的required root检查全部通过，115源码+9配置固定HEAD哈希及前后完整性通过，300s/15s watchdog两阶段均0kill/0error。汇总结构 `TaskProofs c p` 恰有24项原任务命题；组装只导入纯合同及已证辅助。

本批继续第一组S1/S2：采用PR36固定 `4fe26b9b1fe34c7d8c0848289bd459428cd234a1` 的11个原blob、1,825行实际证明，公开定理头和共享合同保持。两任务从g1移入严格证明组，全部九个helper登记；本批自身仍须经B full/fresh CI，不以旧任务分支绿色代替。当前登记 **124模块 / 12,741物理Lean行**。

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

## 完整条件组装与当前编译分组

`Assembly.pairedStepHypothesis_of_blueprint` 使用 `canonicalSourceParameters c`，从 `TaskProofs` 推出上述原目标。`pairedStepHypothesis_of_taskProofs` 保留一般 `SourceParameters c`。三种内部证书（source、terminal、normalization）都在组装证明内由任务前提构造。

先处理原 paired rows 为空的情况；非空时沿同一 source trace、同一 residual refinement、同一 N3 calibration、同一 N6 capacity、同一 normalized family 和 kernels 支付四类 terminal cost 与两类质量。N4 demand、N6 analytic choices、各 orders 的 N5b 窗口与 N9 cost 均在 moving call 之前选择。N8 和 N9 的输入是同一 `LeafNormalization` 的两个投影。N5a 保留为显式任务字段；最终组装直接消费 N5b 已提供的窗口。

| manifest 组 | 模块数 | 内容与验收方式 |
|---|---:|---|
| g0 | 91 | 真实数据、纯合同、共用辅助、U1 和完整条件组装；禁止占位，fresh Lean 递归审计所有已加载 V2 声明。 |
| s1_s2_helpers | 9 | S1原始源与精确界、S2实际Cauchy族/成本/物理截断/行列和retained窗口；全部strict、fresh递归审计。 |
| s1 | 1 | TasksFirstTransform；required theorem为 `Tasks.firstTransform`，检查来源root。 |
| s2 | 1 | TasksFirstAllowance；required theorem为 `Tasks.firstAllowance`，检查来源root。 |
| g1 | 21 | 其余独立待证任务文件；仅这里保留蓝图证明占位。 |
| g2 | 1 | Interface 聚合入口；明确会导入待证任务，不作为纯组装审计 root。 |

每组上限 100 模块。证明接入时，将该项任务文件移出 g1，并与其私有 helper 登记在独立已证明组；不把新增文件藏在 manifest 以外。g0 的 required theorem roots 包括 `TasksUniform` 与 `BlueprintAssembly`，检查 theorem 种类、来源模块及递归公理。白名单仅 `propext`、`Classical.choice`、`Quot.sound`，覆盖 private/generated 声明；保留完整源码/配置哈希、HEAD 前后完整性和 300 秒逐进程 watchdog。

当前分发单位为 S1/S2、S3/S5、S4/T4、S6/N1、N2/N3、N4/N6、N5a/N5b、N7a/N7b、N8a/N8b/N9、T1/T2、T3a/T3b 和 U1。每个任务仍有自己不变的公开陈述，组合分发不允许相互改陈述。B 在骨架验收后继续第一组证明与逐组接入。

## 已报告实现规模与总预算

下表是已完成源码的固定候选规模；除 U1 已在 B 的真实基线验收外，候选仍须在 B 的真实祖先上重新构建和 fresh 审计后才算接入。任务分支的旧成功 CI 不替代该次复验。

| 单元 | 模块数 | 实际物理行数 | 固定候选 / 状态 |
|---|---:|---:|---|
| S1/S2 | 11 | 1,825 | PR36 `4fe26b9b` 原blobs已在本批接入；本次B full/fresh待验收。 |
| S3/S5 | 17 | 2,448 | PR35 `cecf781c`，待真基线复验。 |
| S4/T4 | 30 | 6,192 | PR33 `fab1ee06`，待真基线复验。 |
| N5a/N5b | 7 | 1,149 | PR38 `f61cc2ac`，待真基线复验。 |
| T1/T2 | 28 | 7,176 | PR37 `4df84d85`，待真基线复验。 |
| U1 | 5 | 674 | B `bff9840c` 已完整验收。 |

这 11 项任务的候选实现合计 **19,464 行**。其余 13 项沿用原区间，论文任务当前滚动估计为 **57,464–71,464 行**，公共数据与组装另计；有重叠的公开合同仍保守计数，最终按整个 V2 目录实际源码去重。公共数据/骨架/组装当前约 11k 行，仍保留到最终 **100,000 行以内**的预算空间；后续增长需公开记录。

历史总表逐项重算为 **65,000–93,500 行**；早期说明的上限 92,500 少加了 1,000，本次明确纠正。上述滚动估计来自已有实现规模的替换，不是删去论文任务或把 helper 移出统计。完整条件组装的11个文件经实际编译修复后合计 **1,584 行**。

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
