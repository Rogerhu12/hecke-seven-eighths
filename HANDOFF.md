# 交接：2026-10-30 下午

这一轮做了三件事：判断剩余距离、审计 openai/math 中 Q 的形式化、开始做 D-TESTS 簇。骨架仍是 64 个直接 sorry，没有关闭新的义务，也没有提交任何东西。项目背景、已关闭的义务和构建方法见 [HECKE_PORT.md](HECKE_PORT.md)，这里只写接下来做什么。

## 先读

1. [HECKE_PORT.md](HECKE_PORT.md)：项目来源、本项目已关闭的 16 项、构建方法。
2. [ROADMAP_7_8.md](ROADMAP_7_8.md)：论文附录的十步与骨架义务的对应。
3. [OPENAI_REUSE_AUDIT.md](OPENAI_REUSE_AUDIT.md)：Q 的完整 Lean 形式化（openai/math）的规模、完整性和能复用什么。
4. 旧仓库 `skeleton/OBLIGATIONS.md`、`skeleton/HARD_STATUS.md`、`skeleton/hard-frontiers.json`：义务清单（4.34.1 基线 80 项），以及 10 个困难父项拆成的 54 个数学子目标。

## 剩余 64 个 sorry 的分布

| 步骤（论文附录） | 状态 | 剩余 |
|---|---|---|
| 1–2 算术与 Gauss 校准 | 已关 | 0 |
| 3 轨道 Poisson 与 Gram | GR-01/02/06 已证 | 9（GR-03…GR-12） |
| 4 theta 与标记反射 | 缺 | 8（TH-*） |
| 5 反射能量与两条数域大筛 | 缺 | 3 |
| 6 两次逆变换递推 | 缺 | 4（MI-I-*） |
| 7 素数前提 | 部分 | 2（MI-P-PRIME-*） |
| 8 四阶矩递推 | 缺，最难 | 3 |
| 9 物理估计、高频与 Euler 补偿 | 部分 | 21（EX 9、HB 6、PR/LOW 4、D-EXPANSION、D-SUPPORT） |
| 10 指数比较与闭合 | 条件形式已有 | 0 |
| 矩模型与网格 | — | 6（MI-M 模型类 5、D-MESH） |
| 阿贝尔下降 | 经典类域论，与分析核心无关 | 4（DE-*） |
| D-TESTS 簇 | 正在做，见下 | 4 |

困难的部分集中在 10 个困难父项：GR-12、HB-NORMFORM、TH-KP-DATA、TH-MARKED-REFLECTION、LOW-REFLECTED-ENERGY、EX-DETECTOR-WITNESSES、MI-I-CANONICAL-RECURSION、MI-P-POSITIVE-SLOTS 两项和 MI-P-ZERO-SLOT。D-MESH 不能单独关：它要在几何和目标之前选定，主库现有来源只到 5/6，要等第 8 步推到端点 1 才能确定。

## 正在做：D-TESTS 簇

目标是四个 sorry：

- `HeckeSkeleton/Base.lean` 的 `probeTests`（D-TESTS）；
- `HeckeSkeleton/Principal.lean` 的 `principal_fourier_zero`、`principal_normalization_real`、`principal_normalization_positive`。

数学上要的是两件事：

- 一个 `AdditiveProbeTest` W，满足 `additiveFourierAtZero μ W = 0`；
- `physicalResidueNormalizer = (1/6) · deletedZetaResidue² · additiveMellin μ W (1/6) · mellin W1 1` 是正实数。

这里 μ 是 `(probeMeasures K c).haar`，也就是 Axiom 的 `localNormalizedHaar`；可测结构都是 borel。

### 做法

下面用到的 Axiom 与 Mathlib 声明都已核对存在且公开。和 HECKE_PORT.md 原先的"三块字典"相比，第三块（乘法测度）已经由 Axiom 现成给出。

1. **单位群字典**（草稿已写，见下一小节）。目标声明：
   - `toG : sLocalMultiplicativeGroup K ↑A.Sf ≃* A.G`，用 `InfiniteAdeleRing.ringEquiv_mixedSpace` 和 `MulEquiv.piUnits`；
   - `norm_toG`：`A.norm ∘ toG = sLocalProductNorm`，因为所有无穷位都是复位（`A.complex_place`）；
   - `toG_section`：骨架的 `sLocalNormSection` 对应 Axiom 的 `A.radialSection`；
   - `normOneEquiv : sLocalNormOneGroup ≃ₜ* A.G1`；
   - `sheetPoint_normOneEquiv`：`ProbeSheet.sheetPoint A T (normOneEquiv t) = toUnits (t · section T)`。

   连续性用 `DedekindZetaZeroFree.sArchModel_comparison`。
2. **选定 Axiom 的输入**：
   - `A := (axiomChoice K c).A`。`ArithmeticChoice` 自带 `hS : A.ContainsTraceBadPlaces`，而且 `places = A.Sf`。
   - 局部特征取 `e := fun v => ResidueTrace.localTraceCharacter v.val`：
     - 连续性和 `TraceCompatible` 来自 `PrincipalProbeConstruction.canonical_trace_contract A hS`；
     - 非平凡性来自 `localTraceCharacter_exists_ne_one`。
   - 加法测度取 `μ := NormalizedProbe.poissonAdditiveMeasure A μskel`，其中 `μskel p = localNormalizedHaar K p.val`。它是加法 Haar 测度，照抄 `exists_trace_normalized_haar` 的最后一段（`TraceHaarCoordinates.lean` 约 296–305 行）：先 `Measure.prod.instIsAddHaarMeasure`，再 `AddEquiv.isAddHaarMeasure_map`。
   - 范数一群上的测度取 `dt := Measure.map (normOneEquiv A) sUnitHaarMeasure`，它是 Haar 测度（`ContinuousMulEquiv.isHaarMeasure_map`）。
   - 单位群上的测度取 `ν := Measure.map (fun p => ProbeSheet.sheetPoint A p.1 p.2) (ProbeSheet.radialMeasure.prod dt)`。这样 `ProbeSheet.HaarDisintegration A ν dt` 按定义成立（`rfl`），ν 是 Haar 测度由 `ProbeSheet.sheet_map_isHaar` 给出。
3. **Axiom 的探针**：`RadialCancellingProfile.probe_fixed_weight_construction K A e he htrace μ ν hμ hν` 给出 W1 和 W0，满足：
   - W0 是环形张量（`IsAnnularTensor`），紧支撑，支撑在单位里，非零；
   - `fourier W0 0 = 0`，`fourierMellin W0 (1/6) ≠ 0`。
4. **径向 Mellin 恒等式**：`probe_sheet_mellin_estimates_of_disintegration K A e he htrace hne μ ν dt hμ hν hdt rfl w W0 W1 …` 给出 `MellinEstimates`。它的第三个分量在 Re z > 0 时给出
   `∫_{T>0} envelope(T) T^z / T = fourierMellin W0 z`，其中 `envelope(T) = ∫ t, fourier W0 (sheetPoint A T t) ∂dt`。

   可积性 Axiom 已经证了（`ProbeSheetFourierMellinBounds.fourier_mellin_integrable`）。
5. **Fourier 字典（待写，主要工作量在这里）**：
   - W0 的形式：`W0 x = (∏_复位 fComplex v ((R x.1).2 v)) · ∏_v fFinite v (x.2 v)`，实位的乘积是空积。
   - 要证的恒等式：`ProbeWeight.fourier e μ W0 y = haarScalar · Arch(R y.1) · ∏_v Loc_v(y.2 v)`。这里 `Arch` 就是骨架用的 `fourierIntegral (standardMixedAddCharacter K) volume g`，`Loc_v = fourierIntegral (psiLocal K v) μskel_v (fFinite v)`。
   - 用到的工具：
     - 沿 `poissonLocalEquiv` 做 `integral_map`；
     - `integral_prod_mul`；
     - `integral_fintype_prod_eq_prod`（`Measure.pi` 版本）；
     - `mixedEmbedding.euclidean.volumePreserving_toMixed`；
     - `TraceDictionary.psiLocal_eq_localTraceCharacter`。
   - 还要补一条引理：`archPhase (R⁻¹ m) = standardMixedAddCharacter m`。思路：`standardMixedAddCharacter_apply` 把右边写成 `fourierChar (trace)`；左边按定义是 `exp(2πi Σ 2 Re(extensionEmbedding …))`；所有位都是复位，而 ℂ 对 ℝ 的迹是 2 Re，两边相等。
   - 推论：`additiveFourier μskel W x = κ · fourier W0 (toUnits x)`，`additiveFourierAtZero μskel W = κ · fourier W0 0 = 0`。常数 `κ = haarScalar⁻¹ · ∏ μskel_v(O_v)⁻¹ > 0`，其中 `μskel_v(O_v) = N(𝔇_v)^{-1/2}`（`selfDualProbeMeasures_integers`）。
6. **由 W0 的分量构造骨架的测试函数**：
   - `infiniteTest` 取 `g ∘ traceToMixed K` 的 `HasCompactSupport.toSchwartzMap`，其中 `g m = ∏ fReal · ∏_复位 fComplex v (m.2 v)`；
   - `finiteTest p := fFinite p`；
   - `tensor_compactSupport`：先证 `sLocalTensorTestFunction = W0 ∘ Units.val ∘ toUnits`，再用 `ProbeSheet.units_val_isEmbedding A`、`Topology.IsInducing.isCompact_preimage'` 和 `tsupport_comp_subset_preimage`；
   - `lowerNorm` 取 `continuous_sLocalProductNorm` 在这个紧支撑上的最小值（`IsCompact.exists_isMinOn`），`norm_support` 由此得到。
7. **Mellin**：
   - 对 u > 0，`∫_{t ∈ N1} additiveFourier W (t · σ(u)) ∂sUnitHaar = κ · envelope(u)`。证法：沿 `normOneEquiv` 做 `integral_map_equiv`（把它看成 `MeasurableEquiv`），再用 `sheetPoint_normOneEquiv`。
   - 因此 Re z > 0 时 `additiveMellin μskel W z = κ · fourierMellin W0 z`，在 1/6 处不为零。
8. **调成正实数**：取 `W := (conj M / ‖M‖) • W_raw`，即只缩放 `infiniteTest`，其中 `M = additiveMellin W_raw (1/6)`。`additiveMellin` 对 `infiniteTest` 是线性的（`integral_mul_left`），Fourier 零点不受影响。于是 `additiveMellin W (1/6) = ‖M‖ > 0`。
9. **残数**：`deletedZetaResidue = dedekindPoleCleared K 1 · heckeEulerDeletionPolynomial K 1 (exceptionalPrimes K S) 1`。
   - `dedekindPoleCleared` 的性质见 `vendor/flt/FLTReuse/M5808d10d83f2fccd.lean`：它可微，并且在 Re s > 1 上等于 (s−1)ζ_K(s)。由连续性加 Mathlib 的 `tendsto_sub_one_mul_dedekindZeta_nhdsGT` 和极限唯一性，它在 1 处的值是 `dedekindZeta_residue K`，而这个残数为正（`dedekindZeta_residue_pos`）。
   - 删除多项式：`eulerPolynomial q a s = 1 − a q^{−s}`，再用 `primeCoefficient_trivial`（`HeckeGeneral/Analysis/HeckeNormPole.lean:25`），得到它等于 ∏(1 − N𝔭⁻¹) > 0。
10. **分母**：`HeckeAxiom.denominatorTest probeRealBumpWeight`（`DenominatorAdapter.lean`）。`mellin toFun 1 = ∫ W1 > 0`，参照 `probeRealWeightMellin_one` 和 `probeRealWeightMellin_one_ne_zero` 证明里的正性。
11. **接线与验收**：
    - 在 HeckeAxiom 里写一个存在定理，用 `selfDualProbeMeasures` 表述；`Base.lean` 的 `probeTests` 取它的 `Classical.choose`，配上分母测试；`Principal.lean` 的三个定理由它的性质得到。
    - 新模块加进 `HeckeAxiom.lean`。
    - 跑 `LEAN_NUM_THREADS=4 lake build HeckeAxiom HeckeSkeleton SkeletonInputs`，`Audit` 应报告 60 个直接 sorry。
    - 叶子的 `#print axioms` 只能有标准三公理。
    - 更新 HECKE_PORT.md 的计数和模块表。

### 当前进度

- [HeckeAxiom/ProbeUnits.lean](HeckeAxiom/ProbeUnits.lean) 是第 1 步的草稿，**从未编译**，也没有被任何模块导入，所以不影响现有构建。预计要修，容易出问题的地方有：
  - `val_*` 引理里的 `rfl`；
  - `prodCongr … (MulEquiv.refl _)` 依赖 `↥(↑A.Sf : Set _)` 和 `{v // v ∈ A.Sf}` 定义相等；
  - `arch_norm` 里重排乘积的部分。
- 单文件检查不写 `.lake`，可以用 `lake env lean HeckeAxiom/ProbeUnits.lean`，或者 `python -I tools/run_lean435.py <scratch 目录> HeckeAxiom/ProbeUnits.lean`。
- 下游文件需要它的 olean 时，用 `lake build HeckeAxiom.ProbeUnits`。
- 第 2–11 步还没开始。估计把它们分成 `ProbeFourierDictionary` 和 `ProbeTestChoice` 两个文件比较合适。

## D-TESTS 之后的顺序（建议）

1. **移植试点**：从 openai 的 `Moments/` 挑一个小账本模块（例如 `AllocatedChildCapacity` 或 `CommonMaskChildCapacity`），在本项目里推广到外部理想和允许生成元，记录耗时和改动类型。这能给出工期样本，也能检验论文附录"只有三个输入依赖域"的主张。
2. **theta 评估**：三方对照 Axiom 的 `Theta/`、`Metaplectic/`（一般域、无标记），openai 的 `Reflection/`（有标记、ℚ(ω)），以及论文命题 3.2 与定理 3.5。核心问题是：Axiom 的 theta 反射能不能在复位上换成 K-型为 m 的向量（论文用升算子取 φ_m = E^m φ°）。
3. **三次大筛（MI-M-CUBIC-SIEVE）**：照 Axiom 把 openai 的 `QuadraticSieve/` 推广成 `goldmakherLouvel` 的做法，推广 openai 的 `CubicSieve/`（ℤ[ω] 上 Heath-Brown 式，`HasSieveExponent.improve`）。目标是论文引理 `lem:exterior-cubic-sieve`（BGL 定理 1.3，n = 3）。这项不依赖骨架的其他部分，可以并行做，只在新目录 `CubicSieve/` 下工作。
4. **阿贝尔下降 DE-*（4 项）**：经典类域论，独立于分析核心，随时可以做。

二次大筛那条（MI-M-QUADRATIC-SIEVE）上游已经有 `rm_hgl_oriented`，剩下的是论文 §4.3 第一段的族识别，即构造一个 `QuadraticHeckeFamily`。上游是否已有这个构造还没查。

## 论文与外部材料

- 论文修订稿 [weil_seven_eighths_revised.tex](weil_seven_eighths_revised.tex)（作者本人提供，未入库）。骨架义务引用的节号和它对得上。
- 稿中有一处与上游不一致：第 146–149 行说 Cureton–Thorner 证明的是 Re s > 1 − 1/6000，但上游 Lean（`Challenge/DedekindZetaChallenge.lean:32`）和 README 写的都是 31/32。待作者核对。
- 附录 A 末段说第 6、8 步按位置引用 Q §§17–18。这两节的 TeX 有 3,268 + 2,508 行，比整篇论文还长；不过它们在 openai 里已经有 ℚ(ω) 上的 Lean 证明。
- Q 和 P 的 TeX：旧仓库 `.cache/upstream/papers/quasi-riemann.tex`，以及同目录下的 `primitive-*.tex`。
- openai/math 的克隆：旧仓库 `.cache/openai-math-fd4aeeb2/`。这是部分克隆，只稀疏检出了 `lean/OAI/NumberTheory/DirichletL` 和 `lean/docs`，检出的是最新提交 `4eaee875`，其中 DirichletL 与钉住的 `fd4aeeb2` 完全相同。这是外部数据：只读，不要在里面运行构建或脚本。
- 用户还有一份 AI 生成的结构简化稿 `C:\Users\Boyang\Downloads\weil_structural_simplification.tex`。它对形式化剩余的影响很小：没有 sorry 因此消失，大约省掉 1 个困难子目标（TH-MARKED-REFLECTION 的 UNFOLDING）。它关于闭合只需固定 B 的说法，骨架早已采用（`TIPInput` 先量化 B，以及 `tipFinalSaving`）。它对论文修订有用。

## 注意事项

- 构建命令是 `LEAN_NUM_THREADS=4 lake build HeckeAxiom HeckeSkeleton SkeletonInputs`。每个 lean 进程约占 3 GB 内存；内存紧张时偶尔报 "failed to read file …olean"，重跑即可。不要同时跑两个大构建。
- `HeckeSkeleton` 的 `Base`、`Theta`、`Principal.lean` 和旧仓库不同，从旧仓库同步时不能覆盖。
- 旧仓库的 `.cache` 不能删：本项目 `.lake/packages` 里有 9 个包是指向它的链接，openai 的克隆也在那里。
- 未提交的文件：`HANDOFF.md`、`OPENAI_REUSE_AUDIT.md`、`HeckeAxiom/ProbeUnits.lean`、`weil_seven_eighths_revised.tex`，以及 HECKE_PORT.md 中指向本文件的一行。
