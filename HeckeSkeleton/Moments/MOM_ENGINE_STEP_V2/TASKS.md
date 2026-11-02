# MOM_ENGINE_STEP_V2 独立证明任务

## 并行证明任务总表（先发布清单；逐项冻结）

落实 [协调要求](https://github.com/Rogerhu12/hecke-seven-eighths/pull/31#issuecomment-6575522721)。下表是完整预计分工，**不是声称全部陈述已定稿或已编通**。每项预计证明规模包含该项私有 helper；统一计入最终 <100k 行预算。论文行号以仓库当前 §4.8 的 TeX 行号为准。

**已冻结：N5a**，提交 `d4568a300b454bb11365a64e6da8183e5fa2580b` 的 `ProfileFormula.lean` / `ProfileFormulaTask.lean`。该两模块在本轮 CI 已编过；全批 CI 因另外三个模块报错而未绿。独立证明会话可立即只改 `ProfileFormulaTask.lean` 及相邻新建私有 helper，保持公开陈述与其类型含义不变。若必须变更，先在本 PR 提议。

**U1 尚未冻结**：下一批会先补足 `Call.Regular` 的原问题已允许的两个具体数值条件：`0 ≤ Hp` 与 `strictChildProfileMinimum ≤ Cp`；完成这次公开修订并核对 CI 后单独宣布冻结。没有加入任意“可证明性”谓词。

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
| N8 | 草案：实际 outer × family.weight 的有限总和；direct/main/1,6,7 与 passive labels 恰计一次并支付 slot-removal loss | S2、S3、S5、N2、N4、N6 | 2822–2946 | 4,000–5,000 |
| N9 | 草案：同一实际两个 Schwartz kernels 的共同 Fourier envelope、质量与可积性 | S1、S4、N5b、N6 | 3043–3073 | 2,000–3,000 |
| T1 | 草案：实际 FirstPresentation.normalizedZero 的统一数值 cost | S1 实现证书、原 ProfileInput/Ready | 2822–2850 | 2,000–3,500 |
| T2 | 草案：实际第二次零频的完整 Euler/diagonal 界 | S2–S4、windows | 3004–3007 | 2,500–4,000 |
| T3a | 草案：原 exceptional predicate 的有限 Theta sectors、sixth-power base、unit/fibre 数目、非单位 multiplicity 与 radical 下界 | S4–S6、N1 | 2948–2965 | 3,000–4,000 |
| T3b | 草案：同一整体中心化 exceptional 体积界；divisor loss、短长度非正的 absolute 分支、先抵消 residues 再取绝对值 | T3a、N1、N2、N5b、原几何 | 2967–3002 | 4,000–5,000 |
| T4 | 草案：第一次与第二次真实 masked truncation 差的频率尾；使用正 cutoff 指数和原 kernels | S1、S3、S4、windows | 3004–3010 | 3,000–4,000 |
| U1 | 草案，待下一批冻结：uniformPreparation；有限 costs/demands 后选择 schedule、最小 Cp、原 Mellin windows、Ready 与实际 terminal/mass/outer funding | 纯输入类型、已提供的数值 costs/demands | 3043–3073 | 2,500–4,000 |

N5a 的冻结陈述是：
```lean
theorem profile_formula_control (shape : ProfileShape) (lower upper : ℝ)
    (lower_pos : 0 < lower) (interval : lower ≤ upper)
    (orders : Finset (ℕ × ℕ)) :
    Nonempty (ProfileFormulaCertificate shape lower upper orders)
```

证明依赖图按“数据/纯命题类型 → 显式假设的无 sorry 完整组装 → 各独立 Tasks”分开。组装会先精确处理空 parent rows，再对非空情况沿同一 source trace、同一 refinement、同一 normalized family 消费这些假设，最终得到原始 `PairedStepHypothesis (WithLp 2 (ℝ × ℝ)) c`。

当前表给出的证明预算比早先不完整的估计更高；不能通过改名或移入 helper 隐藏增长。后续每个陈述冻结时会同时给出确切文件、依赖、CI 证据和实际规模。若预测连同公共组装将超过 100k，会在继续扩大代码之前报告并重新划分或简化。
