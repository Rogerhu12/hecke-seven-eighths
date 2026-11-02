# MOM_ENGINE_STEP_V2 独立证明任务

## 并行证明任务总表（先发布清单；逐项冻结）

落实 [协调要求](https://github.com/Rogerhu12/hecke-seven-eighths/pull/31#issuecomment-6575522721)。下表是完整预计分工，**不是声称全部陈述已定稿或已编通**。每项预计证明规模包含该项私有 helper；统一计入最终 <100k 行预算。论文行号以仓库当前 §4.8 的 TeX 行号为准。

**已冻结：N5a**，提交 `d4568a300b454bb11365a64e6da8183e5fa2580b` 的 `ProfileFormula.lean` / `ProfileFormulaTask.lean`。该两模块在本轮 CI 已编过；全批 CI 因另外三个模块报错而未绿。独立证明会话可立即只改 `ProfileFormulaTask.lean` 及相邻新建私有 helper，保持公开陈述与其类型含义不变。若必须变更，先在本 PR 提议。

**U1 已冻结**于 `b2fa7c15d8b5648c95f879ff2e560ff7d65680d6`，见 [冻结公告](https://github.com/Rogerhu12/hecke-seven-eighths/pull/31#issuecomment-6575873444)。Call.Regular 的 Hp 非负与 minimum Cp 条件已纳入并编过；修改公开陈述或其依赖类型含义须先在 PR 提议。

| 编号 | 状态 / 预计陈述 | 依赖 | 论文行号 | 预计证明行数 |
|---|---|---|---|---|
| S1 | 草案：原始整体中心化系数的第一次变换；固定原 chart、原 source、实际零频与真实截断差；仅实际 parent rows 非空时调用 | 原输入与 SourceParameters | 2800–2828 | 2,500–4,000 |
| S2 | 草案：第一次 Cauchy 的实际共同 support、lognorm allowance、有限索引双射、系数/点/权重；左右 divisor 独立 | S1 实现证书、原 profiles | 2827–2850 | 2,500–4,000 |
| S3 | 草案：所有物理分支共用一个素数池；direct/main/error 1,6,7 的真实分解及只支付一次的密度 | S2、原 mesh/window | 2852–2881 | 3,000–4,000 |
| S4 | 草案：第二次 Poisson 的完整非 primitive correlation；真实零频、截断差及 nonzero 分支 | S3、同一 canonical source | 2883–2894，3004–3010 | 3,000–4,000 |
| S5 | 草案：名义 m′/q′/M′/Δ；原 gcd、nonunit radical、M′≤M−σ 及 loss | S2–S4 | 2895–2906 | 1,500–3,000 |
| S6 | 草案：左右独立 divisor allocation/cover 及无重复 live raw leaves；区分 fullDeletion 与 paidSupport，保留同一 kernels | S4、S5 | 2908–2925 | 2,500–4,000 |
| N1 | 草案：原 raw leaf 的四个 comparison rectangle 与原点、原系数字典；全局 formula 与 OrdinaryBinding | S6 | 2800–2820，2908–2925 | 3,000–4,000 |
| N2 | 草案：恢复真实 smooth support，保留 fixed/paid masks，只展开 residual coprimality；唯一 occurrence/divisor labels 与精确逐项恒等式 | N1、S6 原 profiles | 2908–2925 | 4,000–5,000 |
| N3 | 草案：同一实际 frame 的 Calibration、CompleteMovingRowRecipe、NormProfileRecipe；全局 profile 公式与实际有限 cost maxima | N2、原 profiles | 2908–2946 | 3,000–4,000 |
| N4 | 草案：原 sixth-power pattern 与 OriginalSixthLengthBinding、row/window/unit/mesh；复用 base 的容量及 strict drop | S5、N3 | 2883–2946 | 3,000–4,000 |
| N5a | **已冻结：profile_formula_control**；原 Schwartz profile 经正 dilation、实幂、共轭、标量与 log-Fourier phase 后的全局 Schwartz/control 证书 | ProfileFormula 与 base CanonicalLogProfiles | 3043–3073 | 2,000–3,000 |
| N5b | 草案：原 raw/clipped profile 的统一窗口及实际多项式半径；使用全局原 profile 字典 | N3、N4、N5a | 2927–2946，3043–3073 | 2,500–4,000 |
| N6 | 草案：同一 frame 的 FullKappaProfileInput；原 FullJointBudget、固定 contour 与 analytic provider；由 base 构造 normalization | N3、N4、N5b | 2927–2946，3043–3073 | 2,500–4,000 |
| N7a | 草案：同一 normalized children 的 CompleteSourceBudgetPrimitive 和 reflectionArithmeticPrimitive | N3、N4、N6 | 2908–2925，3011–3018 | 3,000–4,000 |
| N7b | 草案：同一 children 的 rankedAnnulusProfilePrimitive；最小 Cp、非负 Hp、rank drop 与原 annulus/Euler controls | N4、N5b、N6 | 3011–3018，3043–3073 | 2,000–3,000 |
| N8a | 草案：实际 raw key 的两 common radicals、两 Möbius 因子、独立第二 divisor 与单 pool prefactor 的 indexMass；只含原 physical fibres 与 harmonic sum | S1–S6 原 trace/geometry/raw | 2842–2850，2852–2881，2895–2906 | 3,000–4,000 |
| N8b | 草案：实际 passive/active labels 的 outer × normalized weight 归约到同一 indexMass；固定原 scalar/profile、无重复标签、whole-slot loss | N2–N7、N8a ledger | 2908–2946 | 3,000–4,000 |
| N9 | 草案：同一实际两个 Schwartz kernels 的共同 Fourier envelope、质量与可积性 | S1、S4、N5b、N6 | 3043–3073 | 2,000–3,000 |
| T1 | 草案：实际 FirstPresentation.normalizedZero 的统一数值 cost | S1 实现证书、原 ProfileInput/Ready | 2822–2850 | 2,000–3,500 |
| T2 | 草案：实际第二次零频的完整 Euler/diagonal 界 | S2–S4、windows | 3004–3007 | 2,500–4,000 |
| T3a | 草案：原 exceptional predicate 的有限 Theta sectors、sixth-power base、unit/fibre 数目、非单位 multiplicity 与 radical 下界 | S4–S6、N1 | 2948–2965 | 3,000–4,000 |
| T3b | 草案：同一整体中心化 exceptional 体积界；divisor loss、短长度非正的 absolute 分支、先抵消 residues 再取绝对值 | T3a、N8a、N1、N2、N5b、原几何 | 2967–3002 | 4,000–5,000 |
| T4 | 草案：第一次与第二次真实 masked truncation 差的频率尾；使用正 cutoff 指数和原 kernels | S1、S3、S4、windows | 3004–3010 | 3,000–4,000 |
| U1 | **已冻结：uniformPreparation**；有限 costs/demands 后选择 schedule、最小 Cp、原 Mellin windows、Ready 与实际 terminal/mass/outer funding | 纯输入类型、已提供的数值 costs/demands | 3043–3073 | 2,500–4,000 |

N5a 的冻结陈述是：
```lean
theorem profile_formula_control (shape : ProfileShape) (lower upper : ℝ)
    (lower_pos : 0 < lower) (interval : lower ≤ upper)
    (orders : Finset (ℕ × ℕ)) :
    Nonempty (ProfileFormulaCertificate shape lower upper orders)
```

证明依赖图按“数据/纯命题类型 → 显式假设的无 sorry 完整组装 → 各独立 Tasks”分开。组装会先精确处理空 parent rows，再对非空情况沿同一 source trace、同一 refinement、同一 normalized family 消费这些假设，最终得到原始 `PairedStepHypothesis (WithLp 2 (ℝ × ℝ)) c`。

当前表给出的证明预算比早先不完整的估计更高；不能通过改名或移入 helper 隐藏增长。后续每个陈述冻结时会同时给出确切文件、依赖、CI 证据和实际规模。若预测连同公共组装将超过 100k，会在继续扩大代码之前报告并重新划分或简化。


### 任务草案调整：N8 拆成 N8a / N8b（其余冻结陈述不变）

源端与规范化端交叉审核后，原 N8 同时承担两套不同的有限纤维计数：原始 physical/source 索引，以及后续 passive/allocation/capacity 标签。合在一项中预计超过单项 5,000 行目标，因此在冻结前拆分，完整计划由 23 项变为 **24 项**：

| 编号 | 候选陈述与界限 | 依赖 | 论文行号 | 预计证明规模 |
|---|---|---|---|---|
| N8a | 对实际 raw key 的两个 common radical、两个 Möbius 因子、独立第二 divisor 和同一个 pool prefactor 定义 indexWeight/indexMass；统一估计原 physical fibres 与 harmonic sum，不涉及 normalized children 或 kernel | S1–S6 原 trace/geometry/raw，实现关系 | 2842–2850，2852–2881，2895–2906 | 3,000–4,000 行 |
| N8b | 同一实际 refined/active 标签的 outer × normalized weight 归约到 N8a 的原 indexMass；支付真实被动分配、profile/scalar 与 whole-slot removal，禁止重新选择任意 normalizer 或重复标签 | N2–N7、同一 N8a ledger | 2908–2946 | 暂估 3,000–4,000 行 |

T3b 也显式复用 **同一个 N8a**，不再独立复制原索引求和。N8a 当前纯定义/命题文件为 `SourceIndexContracts.lean`，独立证明文件为 `TasksSourceIndex.lean`；下一批推送后仍需 CI 与陈述审核，**尚未冻结**。

这是实际预算增加：相较上一表，预计数学证明总量由 **63,000–89,500** 调整为 **65,000–92,500 行**，公共数据和组装另计。上限已接近 100k：公共蓝图与组装需要控制在约 7k 行内，后续任何超额预测会先公开处理，不能靠把代码移入 helper 或改任务名字隐藏。

另外，在冻结源端前发现并修正了精确零项问题：base 的 leaf.Live 不保证非零 correlation class，因此 S6 的 carrier 改为实际 Live 与实际 class.Active 的交集；略去项的原始 whole correlation cost 必须证明等于零。原 physical rows 为空已由实际 fiber=0 自动处理，保持原 canonical Fourier profile/kernel，无须新增替代核。


### 已冻结：U1 / uniformPreparation

冻结提交：`b2fa7c15d8b5648c95f879ff2e560ff7d65680d6`。

```lean
theorem Blueprint.Tasks.uniformPreparation (c : TargetContext K) :
    Blueprint.UniformChoiceTask c
```

文件为 `TasksUniform.lean`；纯陈述/数据在 `UniformContracts.lean`、`UniformData.lean`、`EstimateData.lean`、`InputDemands.lean`，原始调用层由 `SourceFrame.lean` / `PreparedCall.lean` / `CallData.lean` 提供。先前公开提出的两个最终数值条件——`0 ≤ Hp` 和 `strictChildProfileMinimum ≤ Cp`——已经落在本提交的 `Call.Regular` 中。

本轮 [专用 CI](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41435228054) 已完成。这些 U1 模块编译通过；整批失败仅有两个上游根错误：SourceData 的 rowBall 命名空间/import 与 CalibrationData 的 NNReal 记号，正在修复。**冻结依据是该独立陈述及其依赖已经通过编译，不宣称全批为绿。**

独立会话可以立即证明 U1，只改 `TasksUniform.lean` 与相邻新建私有 helper。预计 2,500–4,000 行，论文 3043–3073。其内容是：六类固定数值 costs/demands 给定后，构造原始 backward schedule、minimum Cp、Mellin 原 profile windows、具体 Ready、terminal/mass funding 与外层 Mellin budget。不能把 source expansion、normalized children、实际 terminal 估计或完成的 EngineOutput 作为输入。

公开陈述以及依赖类型的含义从此冻结；任何必要变更先在本 PR 提议。当前可立即分发的两项为 **N5a、U1**；其余保持草案并继续组装验证。

