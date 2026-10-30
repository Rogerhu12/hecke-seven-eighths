# openai/math 中 Q 的形式化：复用审计

2026-10-30。只读源码，没有编译，也没有运行 `#print axioms`。

检出位置是旧仓库的 `.cache/openai-math-fd4aeeb2/`：部分克隆 https://github.com/openai/math ，只稀疏检出 `lean/OAI/NumberTheory/DirichletL` 和 `lean/docs`。检出的是 main 上的提交 `4eaee875`（2026-10-29）。与旧仓库钉住的 `fd4aeeb2` 相比，DirichletL 的 2,926 个文件没有任何改动。统计脚本只读文件，不在克隆目录里运行任何东西。

Q 指 OpenAI 的 quasi-Riemann 预印本（2026-09-30），论文指 [weil_seven_eighths_revised.tex](weil_seven_eighths_revised.tex)，路线图见 [ROADMAP_7_8.md](ROADMAP_7_8.md)。

## 结论

1. **Q 的形式化是完整的。** 终点给出 ℚ(ω) 上有限阶 Hecke 特征在 Re s > 7/8 无零点（主特征的 s = 1 除外），另有 Dirichlet L 和 ζ 的版本，三者都登记为 comparator 挑战。源码中没有 sorry、没有 axiom 声明。
2. **它覆盖了骨架最难部分的 ℚ(ω) 版本。** 带标记的反射与反射能量、逆矩和四阶矩的递推、零点检测器、三次大筛都在里面。上游 Axiom 没有这些，它形式化的是 P 的策略。
3. **它不是对域参数化的。** 93% 的行直接用到 ℤ[ω]（`Ideal O`、`O ⧸ M`、`ActualEisensteinCubic.O` 等），矩递推部分是 96%。递推里的"行"就是 O 的元素，依赖 O 是 PID、单位群有限。所以在 Lean 里，复用方式是沿着同一个证明结构把类型推广，而不是只替换论文附录列出的三个输入。
4. **这条路有先例。** 上游 Axiom 有 49 个文件标注 `Repository: openai/math`，其中 Goldmakher–Louvel 二次大筛就是从 openai 的 ℤ[ω] 版本推广到一般数域的。
5. **theta 的自守性不必从 openai 搬。** Axiom 已经有一般域上的度量 Eisenstein 级数与 theta 构造（`Eisenstein/` 693 个文件、`Metaplectic/` 427 个、`Theta/` 510 个）。openai 的 `Eisenstein/` 目录是 ℚ(ω)（双曲 3-空间）上的对应物。

## 1. 完整性

| 项 | 结果 |
|---|---|
| 终点 | `OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re`（`Hecke/Nonvanishing.lean`），`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` 和 `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`（`Nonvanishing.lean`）；`lean/formalization.yaml` 中分别配有 comparator 配置 `HeckeSevenEighths.json`、`DirichletSevenEighths.json`、`QuasiRiemannHypothesis.json` |
| 无条件性 | Hecke 终点调用 `ProbeFinalAssemblyUnconditional.detector_certified_bands`，矩估计由 `Energy/CertifiedExistence.terminal_certificate` 给出 |
| 源码扫描 | `sorry`、`admit`、`axiom`、`opaque`、`native_decide`、`implemented_by`、`@[extern]`、`unsafe`：全部为 0 |
| 依赖闭包 | 两个终点的 import 闭包覆盖全部 2,926 个模块（489,484 行），没有游离文件 |
| 外部依赖 | Mathlib，另有 PrimeNumberTheoremAnd（2 处 import）、rellich-kondrachov（1 处） |
| 工具链 | Lean v4.34.1、Mathlib `d13f23b7`，与旧仓库相同。参照：旧仓库的 HeckeGeneral 迁到 4.35 时零改动，FLT 的 318 个文件改了 12 处 |

## 2. 结构与耦合

"不直接用 ℤ[ω]"是文本判据：模块自身的源码不出现 Eisenstein 环（`Ideal O`、`O ⧸`、`Oˣ`、`ActualEisensteinCubic`、`CyclotomicField 3`、`primaryGenerator`、`cubicChar` 等）。它会低估可复用的部分，因为一个用到 `Ideal O` 的引理，证明里可能只用到 Dedekind 整环的一般性质。"内容"和"对应义务"两列是按模块名推断的，没有逐个读证明。

| 目录 | 文件 | 行数 | 不直接用 ℤ[ω] 的行 | 内容（按名字推断） | 对应的骨架义务 |
|---|---|---|---|---|---|
| `Moments` | 679 | 83,304 | 4% | 两次变换、子节点容量、放大、例外行（Q §§17–18） | MI-I-*、MI-P-*、MI-M-* |
| `Eisenstein` | 82 | 53,451 | 0% | ℚ(ω) 上的度量 Eisenstein 级数、尖点、常数项、Fredholm | 不需要：Axiom 已有一般域版本 |
| `Detector` | 414 | 42,514 | 14% | 零点检测器与饱和见证（Q §8）、终点总装 | EX-DETECTOR-WITNESSES、EX-*、HB-* |
| `Descent` | 419 | 41,920 | 9% | 带标记的规范递推（rank、子节点状态、宽度） | MI-I-CANONICAL-RECURSION |
| `CubicSieve` | 91 | 37,108 | 3% | ℤ[ω] 上 Heath-Brown 式三次大筛，指数自举 `HasSieveExponent.improve` | MI-M-CUBIC-SIEVE（BGL n = 3 的模板） |
| `Energy` | 208 | 27,602 | 6% | 能量带、宽度归纳、终端证书 | MI-P-POSITIVE-SLOTS-*、MI-P-ZERO-SLOT |
| `Inversion` | 155 | 24,412 | 16% | 逆变换的初始化与父子上限 | MI-I-* |
| `QuadraticSieve` | 36 | 24,010 | 0% | ℤ[ω] 上二次大筛 | 不需要：Axiom 已有 GL |
| `Reflection` | 266 | 23,469 | 5% | 完整与带标记的反射、立方完整能量（Q §§5、14） | TH-MARKED-REFLECTION、LOW-REFLECTED-ENERGY |
| `GaussSum` | 34 | 23,396 | 0% | 三次、六次 Gauss 和 | 不需要：本项目算术层已有 |
| `Hecke` | 182 | 21,609 | 15% | ℚ(ω) 上 Hecke 族与 L 函数 | PR-* 的一部分 |
| `PrimeRows` | 182 | 18,265 | 3% | 素数行与行计数（Q §§9、19） | HB-*、EX-* |
| 其余 11 个目录与根目录 | 178 | 68,424 | 11% | Mellin、Poisson、互反律、延拓、终点数值 | 分散 |
| 合计 | 2,926 | 489,484 | 7% | | |

两个样例说明耦合的形态：

- 矩估计的总接口 `terminal_certificate` 对 `M : Ideal O`、`H : Subgroup (O ⧸ M)ˣ` 陈述，参数 κ ≥ 3/4 且 κ ≥ 2β − 1，与论文的 κ = 2B − 1 一致。
- `Moments/ChildAssembly.lean` 里的行是 `a : α → O`，即 O 的元素。在一般域上，对应物是外部理想的允许生成元（在 Γ = (R^×)^6 意义下唯一）。对有限单位群的求和要改成对有限个扇区求和。

## 3. 对路线的影响

剩余工作的分工因此清楚了：

- **Axiom 提供**：一般域上的算术（本项目已接上）、度量 theta 的自守性与无标记反射、GL 二次大筛、一般域上的 Poisson 与 Gram。
- **openai 提供**：ℚ(ω) 上带标记的反射、矩递推、检测器、三次大筛、行计数的完整证明结构。
- **本项目要做**：把 openai 的这些层推广到 Axiom 的一般域对象上，再加上固定无穷型。openai 只有有限阶剩余特征，没有 (m_v, τ_v)；论文命题 3.2 的高 K-型向量和配对素数系数是两边都没有的新内容。

与读论文时的估计相比：

- 第 6、8 步不需要先在纸上把 Q §§17–18 推广到一般数域。有一份经过机器检验的 ℚ(ω) 证明可以照着推广，数学上的风险只剩论文的转移主张本身。
- 工程量很大，但现在可以量化。`Moments`、`Descent`、`Inversion`、`Energy` 合计约 17.7 万行，`Reflection` 和 `CubicSieve` 约 6.1 万行，`Detector` 和 `PrimeRows` 约 6.1 万行。这约 30 万行中，约 93% 直接用到 ℤ[ω]。

建议的顺序：

1. D-TESTS 簇，不受影响。
2. 先做一个试点：从 `Moments` 里挑一个小而自洽的账本模块（例如子节点容量 `AllocatedChildCapacity` 或 `CommonMaskChildCapacity`），在 4.35 项目里推广到外部理想与允许生成元，记录每千行的耗时和改动类型。这能给出旧文档说缺少的工期样本，也能检验论文附录"只有三个输入依赖域"的主张。（第一个试点已做，选的是中心矩底层而不是这两个模块，见 [PORT_PILOT.md](PORT_PILOT.md)。）
3. theta 评估改为对照三方：Axiom 的一般域 theta（`Theta/`、`Metaplectic/`），openai 的带标记反射（`Reflection/`），论文的命题 3.2 与定理 3.5。
4. 三次大筛：按 Axiom 推广 GL 的做法推广 openai 的 `CubicSieve/`，目标是论文引理 `lem:exterior-cubic-sieve`（BGL 定理 1.3，n = 3）。

## 4. 未审计的内容

- 没有编译，没有逐个检查公理；完整性结论来自源码扫描和官方 comparator 登记。
- 没有读 openai 递推的证明正文，只看了接口和模块名。第 2 节的"内容"和"对应义务"是推断。
- openai/math 中还有几个可能相关的项目没有看：`NumberTheory/CubicMoment`（3,549 个文件）、`RepresentationTheory/Theta`（1,495 个）、`NumberTheory/CubicGram`（45 个）、`NumberTheory/CubicGauss`（30 个，其中有 `LargeSieve.lean`）。它们不在 DirichletL 的依赖闭包里。
