# 移植试点：openai `Moments` 的中心矩底层

2026-10-30 14:00–14:41。把 openai/math（`fd4aeeb2`）`DirichletL/Moments` 中中心矩的底层 7 个模块，从 ℤ[ω] 推广到一般数域，放在新库 `HeckePort`（`HeckePort/CenteredMoment/`）。生成元一侧用的是外部理想和允许生成元。目的是为剩余行数的估计拿到第一个实测样本。审计背景见 [OPENAI_REUSE_AUDIT.md](OPENAI_REUSE_AUDIT.md)。

## 选了哪条链

- openai `Moments` 的模块单看都很小，但几乎每个都间接导入整个 Hecke 族底座，约 19 万行。
- HANDOFF 原来建议的 `AllocatedChildCapacity` 只有 320 行，可它在 `Moments` 内部的依赖链有 207 个模块、2.8 万行，不适合做试点。
- 选的是 `Basic → Lattice/Mask → Primary → MaskedVolume → Cancellation → Counting`。它在 `Moments` 内部只依赖这 7 个模块，共 1,025 行。这条链同时有三类代码：
  - 与域无关的代数；
  - Dedekind 整环通用的 Möbius 展开；
  - 依赖域的格点 Poisson 和 primary 生成元。
- `Mask` 用到 openai `Arithmetic/IdealMobius.lean` 中的 Möbius 除数和一节（126 行），一并移植。

## 对应关系

| openai（ℤ[ω]） | 一般域 | 来源 |
|---|---|---|
| `Ideal O`，O = ℤ[ω] | `Ideal (𝓞 K)` | — |
| 与 3 互素的理想及其 primary 生成元 | 外部理想（不被 S 中素理想整除）及其允许生成元 `D.generator`，模 Γ = (R^×)^6 唯一 | HeckeGeneral 的 `ExteriorIdeal`、`ThetaArithmeticData`、`AllowedGeneratorInput`（AR 义务，已关） |
| `primaryIdealCharacter c χ` | `generatorIdealHom`：χ 作用在允许生成元上，χ 须在 S-单位的六次幂上平凡，非外部理想处取 0 | 新写 |
| `idealDivisors` 与除数界 | 上游的 `idealDivisors` 与 `ideal_divisor_count_le_rpow` | Axiom |
| 范数不超过 H 的理想至多 128H 个 | 至多 C_K·H 个（`idealCountConstant K`） | 上游 `exists_ideal_count_bound` |
| `primary_ideal_volume_error_all`（格点 Poisson 加 `pv_lattice_bound`） | 假设结构 `IdealVolumeInput`：主项为 X·v(W)，误差对 X 一致 | 一般域里需要对偶轨道级数在所有半径上的界，属于尚未关闭的 Gram 义务 |

## 结果

`lake build HeckePort` 通过，共 9 个模块，没有 sorry。HeckePort 自身没有警告，只有项目里普遍存在的"直接导入 Mathlib"提示。10 个主要定理的 `#print axioms` 都只有 `propext, Classical.choice, Quot.sound`，例如 `sum_moebius_divisors`、`masked_rectangle_saving`、`maskedSum_absolute`、`generatorIdealHom`、`generator_masked_rectangle_saving`。

下表行数为物理行。"代码行的去向"一列只看代码行（去掉空行、注释和文档）：

| 类别 | 模块 | openai | 移植 | 比 | 代码行的去向 |
|---|---|---|---|---|---|
| 与域无关 | `Basic` | 261 | 268 | 1.03 | 98% 原样，只改命名空间 |
| Dedekind 通用 | `IdealMobius`（Möbius 一节）、`Mask` | 262 | 285 | 1.09 | 69% 原样，19% 机械改名（O → 𝓞 K、0 → ⊥），其余换成上游的除数集合与除数界 |
| 下游 | `MaskedVolume`、`Cancellation`、`Counting` | 292 | 288 | 0.99 | Ψ 和体积估计改成假设后，陈述变短；`Counting` 的常数 128 换成依赖 K 的常数 |
| 依赖域：生成元 | `Primary` 的特征部分 → `Generator`、`GeneratorCounting` | 71（另有 openai 的 primary 生成元构造约 120 行） | 220 | — | 重写，原样保留的只有 2 行 |
| 依赖域：解析输入 | `Lattice` 与 `Primary` 的格点字典 | 264 | 39 | 未移植 | 只写了假设结构 |
| 合计 | | 1,151 | 1,100 | | |

- 真正移植的部分（不含解析输入）是 887 行 → 1,061 行，比为 1.20。
- 若把 openai 的 primary 生成元构造（约 120 行）也算进源码一侧，比约为 1.05。这部分在本项目里对应已关闭的 AR 义务。

## 工作量

- **耗时**：墙钟 41 分钟。前 18 分钟用来选链、找一般域的对应物；后 23 分钟写代码，共构建 9 次，每次 1–1.5 分钟。
- **输出量**：输出 14.4 万 token，其中思考占 62%。平均每行最终代码约 130 token；D-TESTS 的桥接约为 300 token/行。
- **编译错误 5 处，都不是数学问题**：
  - 漏抄了 openai 原文的一行 `all_goals rfl`；
  - HeckeGeneral 引理的 K、S、D 是显式参数，不能用点记号调用；
  - `tsum_eq` 要显式给出被求和函数；
  - 一处要用 `False.elim`；
  - `omit … in` 要写在 docstring 前面。
- **其他修改**：7 处加 `omit` 消除"未用节变量"提示；`dif_pos`/`dif_neg` 在这个工具链里已弃用，改成 `dite_eq_left`/`dite_eq_right`。
- **API 漂移**：原样照抄的 openai 证明在 4.35 的 Mathlib 下全部通过，没有遇到。

## 对"依赖域的输入"的检验

论文第 3030 行附近列出了这段归纳中依赖域的输入：完整局部相关、带公共核的轨道 Poisson、理想素数池、带掩码的 Mellin 消去。在这条链里，域只从三处进入：

1. 体积估计，即轨道 Poisson 加上对偶级数的界；
2. 允许生成元特征；
3. 依赖 K 的算术常数（理想计数、除数界），上游已有。

其余代码不改数学，只改类型。这与论文的转移主张一致，但只覆盖了矩递推最底层的一小段。

## 对行数估计的影响

剩余 60 个 sorry 的估计：中间值约 40 万行，区间 28–54 万。分块如下：

| 部分 | 剩余 sorry | 模板（openai） | 模板行数 | 估计 |
|---|---|---|---|---|
| 第 6–8 步与矩模型 | 15 | `Moments`、`Descent`、`Inversion`、`Energy` | 17.6 万 | 14–22 万 |
| 第 9 步 | 21 | `Detector`、`PrimeRows`、`RowCompletion`、`MeanSquare` | 8.1 万 | 6–11 万 |
| 第 4–5 步（theta、标记反射、反射能量） | 9 | `Reflection`，另有 Axiom 的一般域 theta | 2.3 万 | 4–10 万 |
| 两条大筛 | 2 | `CubicSieve` | 3.7 万 | 2.5–6 万 |
| 第 3 步 Gram | 9 | Axiom 的一般域 Poisson 与 Gram | — | 1–3 万 |
| 阿贝尔下降 DE-* | 4 | 无 | — | 0.5–1.5 万 |

试点对估计的影响：

- 与域无关和 Dedekind 通用的代码，推广系数实测约 1.0–1.1，落在估计所用区间 0.7–1.3 的中间。
- 依赖域的生成元部分要重写，但它建立在已关闭的 AR 义务上，量不大。
- 解析输入这次没有移植。它的工作量算在 Gram 一块里，不在矩递推一块。
- 每行 130 token 是这类浅层代码的速度。照此计算，40 万行约 5,200 万 token，约 250 小时连续输出。账本递推的证明更长，实际会慢一些。

所以估计不改，这一个样本只说明推广系数大概不在区间两端。

## 没有覆盖的

- `Moments` 的主体是账本递推，其中的行是 O 的元素，并对有限单位群求和；这次没有碰。下一个试点应选这样的模块，连同它实际用到的定义一起移植。可选的有 `CommonMaskChildCapacity`（102 行，只用到理想上的 Dirichlet 多项式），或某个带行 `a : α → O` 的子节点账本。
- `IdealVolumeInput` 没有证明。证明它需要两样东西：
  - HeckeGeneral 的 `sIntegerPeriodicOrbitalPoisson`；
  - 对偶轨道级数在所有半径上一致的界。这个界与 GR-11（小半径）有关，大半径一侧已经有证明（`large_radius_profile`）。
