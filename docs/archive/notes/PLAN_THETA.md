# Theta 簇与 LOW-REFLECTED-ENERGY：体量估计与拆分

2026-10-30，只读规划代理的结论（没有编译）。估计行数指最终 Lean 行数。

## 先要修的结构问题

1. **TH-KP-DATA 必须先变成真正的构造。** `finiteMellinData` 目前是 `by sorry` 的不透明定义（`HeckeSkeleton/Theta.lean:102`），它上面的性质都没法独立证明。构造时要带上规格字段：系数等于壳层积分。
2. **三个 TH-KERNEL 改成对一般数据陈述。** 加上假设 `(hF : FiniteMellinAdmissible K S F)`，就与 TH-KP-DATA 无关，可以并行做。它们还需要 `Finite (SixthLocalClasses K S)`，可参考 Axiom 的 `V_finite`，约 500 行。
3. **`completedMarkedEnergy` 要显式加上两个大筛假设。** 加 `QuadraticSieveBound K c` 和 `CubicSieveBound K c`，做法同 `canonical_inverse_models`；否则它暗中依赖 MI-M-QUADRATIC-SIEVE 和 MI-M-CUBIC-SIEVE。

## 现有义务

| 义务 | 估计 |
|---|---|
| TH-KP-DATA | 1.2 万 |
| TH-FINITE-VALUATION-CUTOFF | 0.15 万 |
| TH-FINITE-VALUATION-DECAY | 0.3 万 |
| TH-KERNEL-INTEGRABLE | 0.15 万 |
| TH-KERNEL-LINE-INDEPENDENT | 0.2 万 |
| TH-KERNEL-DERIVATIVE-BOUND | 0.4 万 |
| TH-MARKED-REFLECTED-ABSOLUTE | 0.4 万 |
| TH-MARKED-REFLECTION | 3.9 万 |
| LOW-REFLECTED-ENERGY | 2.8 万 |
| **合计** | **约 9.5 万**（7.5–13 万） |

全新内容约 3.9 万行：固定无穷型、可能无穷阶的周期特征、高 K-型向量、标记与刺孔、一般环形测试函数、任意 S_f 上的有限旋转表。其余是对 Axiom 或 openai 现有代码的移植和推广。

## 拆分（每块约 0.4–0.8 万行）

| 新单位 | 内容 | 估计 | 主要来源 |
|---|---|---|---|
| TH-KP-DATA-1 | 在本项目的 `ArithmeticChoice` 上实例化 Axiom 的 packet，证明 `R.probe.allowed.generator = D.generator` | 0.55 万 | `AX/Moments/Reflected/RankOneExpansion`、`SignedDigitExpansion`、`HeckeAxiom/AllowedGeneratorAdapter` |
| TH-KP-DATA-2 | 有限旋转表：壳层积分、`1_B` 的特征展开、θ_p 扭曲 | 0.65 万 | Axiom `normalizedLocalWeylValue`；旧缓存 `SLocalTwistedCharacter` |
| TH-FINITE-VALUATION | 截断与衰减合为一块 | 0.45 万 | `localWeyl_support`、`actual_small_norm_decay_canonical` |
| TH-KERNEL | 三个核义务合为一块，公共引理 `kernel_strip_bound` | 0.75 万 | HG `ArchimedeanGammaVertical`、`GaussianStripShift`；AX `EulerIntegrationByParts`；openai `Mellin/UniformKernelBounds` |
| TH-MARKED-REFLECTED-ABSOLUTE | 反射项绝对可和 | 0.4 万 | AX `SexticReflectedLocalModel` |
| TH-REFL-ARCH | 阿基米德侧：高 K-型向量与 Mellin 对 | 0.55 万 | AX `ComplexRootDerivativeVectors`、`ThirdBesselMellinTransform`；旧仓库 `AngularThirdBesselMellin`（4.35 原生通过） |
| TH-REFL-EXTERIOR-DIGITS | 标记数字表（引理 3.2）与普通表 | 0.5 万 | AX `Digits/*`；openai `Descent/Marked*` |
| TH-REFL-AUTOMORPHIC | 数字平均 D⁺ = D⁻、Γ 下降、常数项消去 | 0.75 万 | AX `DigitsDescent`、`ResidualConstantTerm` |
| TH-REFL-DIRECT-UNFOLD | 正向轨道展开 | 0.65 万 | AX `Theta/Unfolding/*` |
| TH-REFL-REFLECTED-UNFOLD | 反射侧展开、CRT 分离、混合因子表 | 0.8 万 | `HeckeAxiom/SexticSymbolDictionary`；openai `Cusp/*`（只作样板） |
| TH-REFL-MELLIN | 解析延拓、带状增长（Phragmén–Lindelöf）、Mellin 反演，得出 `marked_reflection` | 0.65 万 | AX `HarmonicAnalysis/Mellin/*`；HG `MellinInverseLine` |
| LOW-HYBRID | 引理 4.6–4.7：从两个大筛得混合能量 | 0.45 万 | openai `Descent/Hybrid*`；旧笔记 `low-hybrid-complete-paper-reduction.md` |
| LOW-FROZEN-CUBE | 行分解、冻结立方 | 0.65 万 | openai `Reflection/{Frozen*,Cube*,…}` |
| LOW-COMMON-PROFILE | 公共 Fourier 测度与尾项 | 0.6 万 | openai `Reflection/Kernel*`、`Uniform*` |
| LOW-ROWCOUNT | 强力行计数与账本 | 0.5 万 | openai `Reflection/{PowerfulBudget,Norms,CanonicalCaps}` |
| LOW-PHYSICAL-ASSEMBLY | 式 (6.22) 的组装 | 0.6 万 | 旧缓存 `actual-gram-amplitude-20261012` 中 8 个模块（约 2,200 行，有原生成功回执）；openai `Reflection/LowOriginalEnergy` |

共 16 个单位。

## 依赖

- 先做：`Finite (SixthLocalClasses)` 和 TH-REFL-ARCH（C₀、A₀ 来自阿基米德计算）。
- 数据链：TH-KP-DATA-1 → TH-KP-DATA-2 → TH-FINITE-VALUATION → TH-KERNEL。
- 反射链：TH-KERNEL → TH-MARKED-REFLECTED-ABSOLUTE；它和 TH-REFL-MELLIN 一起推出 TH-MARKED-REFLECTION，再推出 LOW-REFLECTED-ENERGY。
- TH-MARKED-REFLECTION 还为 MI-I-CANONICAL-RECURSION 提供输入。
- LOW 需要两个大筛。Theta 簇不依赖 D-MESH，也不依赖 Gram。

## 风险

- **最高**：TH-REFL-AUTOMORPHIC、两个 UNFOLD、TH-KP-DATA-1。Axiom 的 packet 是一个存在性定理，不是开放接口。可能要把 Axiom 的 `Theta/Unfolding`、`Digits`、`Profiles` 中二三十个文件复制到 `HeckeAxiom/`，并把分支特征参数化为 L_υ。
- **较低**：TH-KERNEL、TH-FINITE-VALUATION、LOW-HYBRID，提供者都已存在。
