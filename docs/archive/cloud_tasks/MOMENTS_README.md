# Moments 任务组（7 个）

论文第 4 章"Canonical moments"和第 5 章"Sixth-power amplification"，`weil_seven_eighths_revised.tex` 第 1505–3273 行。骨架目标在 `HeckeSkeleton/Moments.lean`，带 `-- OBLIGATION MI-*` 的定理就是要证的。通用规矩见 [README.md](README.md)。

| 任务 | 论文 | 骨架义务 |
|---|---|---|
| [MOM_BASE](MOM_BASE.md) | §4.2 有限系数与背景 | 共享底座；`HeckePort/Moments` 的显式假设 |
| [MOM_INV_STEP](MOM_INV_STEP.md) | §4.5 前半 | 规范逆归纳的单步 |
| [MOM_INV_INDUCTION](MOM_INV_INDUCTION.md) | §4.5 后半与定理 4.1 | MI-I-CANONICAL-RECURSION |
| [MOM_PRIME](MOM_PRIME.md) | §4.6–4.7 | MI-P-PRIME-ABSOLUTE-ENDPOINT，引理 4.11 |
| [MOM_ENGINE_STEP](MOM_ENGINE_STEP.md) | §4.8 前半 | 四阶矩归纳的单步 |
| [MOM_ENGINE_INDUCTION](MOM_ENGINE_INDUCTION.md) | §4.8 后半与定理 4.2 | MI-P-ZERO-SLOT，MI-P-POSITIVE-SLOTS-BELOW-ONE，MI-P-POSITIVE-SLOTS-ENDPOINT |
| [MOM_UNIFORM_AMPLIFY](MOM_UNIFORM_AMPLIFY.md) | §4.9，第 5 章 | MI-M-PROFILE-UNIFORMITY，MI-M-FIBER-ELIGIBILITY，MI-M-FINITE-SECTOR-REINDEX，MI-I-SIXTH-POWER-ZEROS，MI-I-INDEPENDENT-AMPLIFICATION，MI-I-AMPLIFIED-WITNESS-CALIBRATION |

**不在本组**：
- MI-M-ROW-CHARACTER、MI-M-MODELS、MI-M-POLYNOMIAL-CALIBRATION 由 EXPANSION（PR #5）的共享配方负责。
- MI-P-PRIME-CANCELLATION-BELOW-ONE 由 [MOM_PRIME_BELOW_ONE](MOM_PRIME_BELOW_ONE.md) 负责（PR #14 已合入对任意模型的版本，剩下对实际模型的 `PrimeSlotModelControl`）。
- 两个大筛已经证明。
- LOW-REFLECTED-ENERGY（引理 4.8）在 PR #3。

**并行规则**
1. 每个任务的新代码放在自己的目录 `HeckeSkeleton/Moments/<任务名>/` 下。
2. 只在最后一步改 `HeckeSkeleton/Moments.lean`，而且只把自己负责的 `sorry` 换成调用。
3. 依赖关系：`MOM_INV_INDUCTION` 用到 `MOM_INV_STEP` 的单步结论，`MOM_ENGINE_INDUCTION` 用到 `MOM_ENGINE_STEP` 的单步结论。各对在开工时都按论文写出单步结论的 Lean 陈述，放在自己目录的 `Interface.lean` 里：做单步的一方证明它，做归纳的一方把它当作假设。两边陈述不一致时，以单步一方为准，合并时再对齐。其余任务若需要别的任务的结论，同样以显式假设的形式接入。
4. 已知的骨架缺陷：`WholeMomentProfileControl` 没有覆盖素数窗口（见 `cloud_tasks/WIRE_PRIME_CANCELLATION_REPORT.md`）。如果这影响你的任务，就在 PR 里给出修正后的陈述。

**参考**：openai 的 `lean/OAI/NumberTheory/DirichletL/` 下 `Moments/`（约 8.3 万行）、`Inversion/`（约 2.4 万行）、`Energy/`（约 2.7 万行）、`Dictionary/`、`PrimeRows/`，是 ℚ(ω) 上的同一套证明。已经移植到一般数域的部分在本仓库的 `HeckePort/Moments/` 和 `HeckePort/CenteredMoment/`。
