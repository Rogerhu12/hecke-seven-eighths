# 独立任务：κ < 1 时素数槽的消去界（MI-P-PRIME-CANCELLATION-BELOW-ONE）

本文件自成一体，不需要先读项目的其他文档。下文用到的 Lean 定义都原样抄在第 3 节。

## 1. 它在整个证明里是什么

论文要证明：任意数域上的单位 Hecke L 函数在 Re s > 7/8 无零点。证明的 Euler 侧要用一个**配对四阶矩**的归纳：对一族"行"u，估计若干个短 Dirichlet 多项式乘积的均方。

这些多项式里有一类叫**素数槽**：
  Q_{u,i} = P_i^{-1/2} · Σ_{p 素理想, N(p) ≍ P_i} χ_{u,i}(p) · W_i(N(p)/P_i)，P_i = Z^{z_i}
每个槽只在素理想上取值，是带光滑窗口 W_i 的有限特征素数和。

**本任务就是论文的式 (4.38)**（`weil_seven_eighths_revised.tex` 第 2664–2683 行，§"Ordinary reflection and prime factors"）：设 κ = 2B − 1 < 1，其中 B 是零点上界参数，即假设族中的 L 函数在 Re s > B 无零点。那么对每个允许的行，整个槽乘积满足

  |∏_i Q_{u,i}|² ≪ Z^{κ z + ε} · p_J(W)^b · (1 + |t|)^A，z = Σ z_i。

平凡的估计（逐项取绝对值）只能给出 Z^{z}，也就是 κ = 1 的情形，那是另一个义务 MI-P-PRIME-ABSOLUTE-ENDPOINT，不在本任务内。κ < 1 时要省出 Z^{(1−κ)z}，这必须用零点信息。

**论文的证明思路**
1. **对数导数界。** 由零点自由假设，在 Re s = (1+κ)/2 + e 这条线上有 L'/L(s, χ) 的界，与 Q 的式 (18.11) 相同。证明用完整 Hecke L 函数及其零点；数域的次数只贡献高度对数的一个固定倍数。
2. **光滑素数和。** 对光滑化的 von Mangoldt 和做 Mellin 反演，积分线移到上面那条线上，再去掉素理想幂，得到有限特征的素数估计：
   Σ_p χ(p) W(N p / P) ≪ P^{(1+κ)/2 + e + ε}，因而 |Q| ≪ P^{κ/2 + ε'}。
   这里要用到：在允许的行上，每个 χ_{u,i} 都不是主特征。
3. **乘积。** 对所有槽相乘，再取平方，就得到 Z^{κ z}；2ez 这一项并入 ε。
4. **一致性。** 上面所有界对 3/4 ≤ κ ≤ 1 一致，对 Euler 型的范数幂导数也一致。

## 2. Lean 目标

文件 `HeckeSkeleton/Moments.lean`，`namespace HeckeSkeleton`，上下文为 `variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)`：

```lean
-- OBLIGATION MI-P-PRIME-CANCELLATION-BELOW-ONE | §4.6,(4.38),p29.
theorem paired_primes_below_one
    (hB : c.family.B < 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c)) :
    PairedPrimeProductBound K c (momentModels K c) (2 * c.family.B - 1) := by
  sorry
```

其中：

```lean
def PairedPrimeProductBound (M : SourceMomentModels K c) (κ : ℝ) : Prop :=
  UniformMomentBound
    (fun _ _ i => ∑ s : SixthUnitClasses K (places K c),
      ∑ u ∈ pairedRows (pairedModel M i s) (pairedParameters i) (momentBase i),
        ‖slotProduct (pairedModel M i s) u (momentBase i) 0‖ ^ 2)
    (fun _ _ i => 1 + κ * selectedLength i)
    (fun _ _ i => pairedCapacity i)
```

**一个重要的阻塞点**：`momentModels K c` 现在本身还是 `sorry`（数据义务 MI-M-MODELS）。所以这个定理暂时不能对实际模型证明。正确的做法是**先证一个与模型无关的一般定理**：对任意 `MomentData d`，只要满足下面第 4 节列出的假设，就有槽乘积的界。等 MI-M-MODELS 填好后，主代理再把实际模型的这些假设接上。

## 3. 用到的定义（原文）

`HeckeGeneral/Analysis/MomentInputs.lean`（namespace `HeckeGeneral.Analysis.ConditionalMoments`）：

```lean
structure PrimeWindow where
  length : ℝ
  length_pos : 0 < length
  profile : ℝ → ℝ → ℂ
  support : ℝ → ℝ → Finset (HeightOneSpectrum (𝓞 K))
  support_spec : ∀ t P p,
    p ∈ support t P ↔ profile t ((Ideal.absNorm p.asIdeal : ℝ) / P) ≠ 0

structure SlotGeometry where
  slotCount : ℕ
  slots : Fin slotCount → PrimeWindow K

structure MomentData (ω ψ : HeckeCharacter K) where
  -- （只列与本任务有关的字段）
  theta : Finset (HeckeCharacter K)
  theta_finite : ∀ θ ∈ theta, FiniteOrder θ
  rowCharacter : NonzeroIdeal K → HeckeCharacter K
  rowCharacter_finite : ∀ u, FiniteOrder (rowCharacter u)
  allowedRow : NonzeroIdeal K → Prop
  rows : ℝ → Finset (NonzeroIdeal K)
  rows_spec : ∀ U u, u ∈ rows U ↔ allowedRow u ∧ idealNorm K u ≤ U
  commonMask : NonzeroIdeal K → Ideal (𝓞 K) → Bool
  geometry : SlotGeometry K
  slotCoefficient : Fin geometry.slotCount → HeckeCharacter K
  -- 另有 inverse/plain 测试与背景字段，本任务不用

def maskValue (d) (u) (I) : ℂ := if d.commonMask u I then 1 else 0

def primePolynomial (d : MomentData K ω ψ) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z t : ℝ) : ℂ :=
  let P := Z ^ (d.geometry.slots i).length
  (Real.sqrt P : ℂ)⁻¹ * ∑ p ∈ (d.geometry.slots i).support t P,
    primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
      (d.geometry.slots i).profile t ((Ideal.absNorm p.asIdeal : ℝ) / P) *
      maskValue d u p.asIdeal

def slotProduct (d : MomentData K ω ψ) (u : NonzeroIdeal K) (Z t : ℝ) : ℂ :=
  ∏ i, primePolynomial d i u Z t

def pairedRows (d : MomentData K ω ψ) (a : RealParameters) (Z : ℝ) :
    Finset (NonzeroIdeal K) :=
  (d.rows (Z ^ (a.m + a.q))).filter fun u =>
    if a.z = 0 then d.plainBackground * d.rowCharacter u ≠ 1
    else d.rowCharacter u ∉ d.theta
```

`HeckeSkeleton/Moments.lean`：

```lean
def momentBase (i : SourceMomentIndex K c Z T) : ℝ := Z ^ (momentBlock i).shell
def selectedLength (i) : ℝ :=
  ∑ _j ∈ i.selected, HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots (momentBlock i).shell
def pairedParameters (i) : RealParameters :=
  ⟨1, 0, selectedLength i, 0, (momentWitness i).plainLength,
    (momentWitness i).plainLength, 2 * c.family.B - 1⟩   -- 字段 m r z q n₁ n₂ κ
def pairedCapacity (i) : Prop :=
  (∀ j ∈ i.selected, slotLength … ≤ (momentMesh K c.family).val) ∧
  2 * (momentWitness i).plainLength + 6 * (2 * c.family.B - 1) * selectedLength i ≤ 1

def UniformMomentBound (E power eligible) : Prop :=
  ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k, 1 ≤ Z₀ ∧ 0 ≤ k ∧
      ∀ Z, Z₀ ≤ Z → ∀ i : SourceMomentIndex K c Z (Z ^ τ),
        51 / 100 < (momentBlock i).bin → eligible Z (Z ^ τ) i →
          E Z (Z ^ τ) i ≤ k * (momentBase i) ^ (power Z (Z ^ τ) i + c.family.lamA) * (1 + Z ^ τ) ^ A
```

**零点假设在哪里**：`c.family.B` 与 `c.family.boundary`，后者断言族中每个特征的零点在 1/2 ≤ Re ≤ 1 时实部都 ≤ B。`c.family.lamA` 是允许的损失，在 (0, 1/1000] 之间。

## 4. 建议的一般定理

在新模块里（例如 `HeckeSkeleton/PrimeCancellation.lean`），先证与模型无关的核心：

**素数和的消去。** 设 χ 是有限阶、非主的 Hecke 特征，导子范数 ≤ Z^{O(1)}；L(s, χ) 在 Re s > β 无零点，β ≥ 1/2。设 W 光滑、支撑在 (1, 2) 内。则对任意 ε > 0，
  |Σ_p χ(p) W(N p / P)| ≤ C · P^{β + ε} · (1 + 高度)^A，
其中常数只依赖 K、ε 和 W 的有限个半范数。

**乘积。** 把上式用于每个槽的特征 `rowCharacter u * slotCoefficient i`，再相乘，就得到 `‖slotProduct d u Z 0‖² ≤ C · Z^{κ·总长度 + ε}`。

**行数。** 行数 ≤ `idealCountConstant`·Z^{m+q}，所以对行求和再乘 Z^{1}，与 `power = 1 + κ · selectedLength` 相符。

有两点要注意：
- `primePolynomial` 里还有 `maskValue`（公共掩码）。按论文，先用除数恒等式 (eq:can-mask-delete) 去掉多余的掩码，只损失 Z^ε；不要假设掩码不存在。
- **掩码必须加条件。** `commonMask` 在定义里是任意的布尔函数，任意删掉素数项会破坏消去。一般定理应假设：被掩码删掉的素理想都整除某个范数 ≤ Z^{O(1)} 的理想（误差由除数恒等式控制，代价 Z^ε）。实际模型用的 `originalMomentMask` 只删除 S 中的素位和 2、3 上方的素位，满足这个条件。此条由云端代理发现。
- 零点自由假设要以显式参数给出，而不要直接用 `c.family.boundary`。
- 非主性要求每个槽特征 `rowCharacter u * slotCoefficient i` 非主（允许行上的条件 `rowCharacter u ∉ theta`），作为一般定理的假设。

## 5. 可用的现有工具

- `HeckeGeneral/Analysis/IdealDerivative*`：约 2,700 行，处理理想上的对数导数与光滑和，目前只针对 Gaussian 光滑化。
- `HeckeSkeleton/HeckeBufferedReciprocal.lean`、`HeckeStripPolynomial.lean`、`HeckeUniformStripGrowth.lean`：L 函数在竖带中的多项式增长，以及 1/L 的缓冲控制，均已证。
- `HeckeGeneral/Analysis/HeckeContinuation.lean`：Hecke L 函数的延拓。
- Axiom `DedekindZetaZeroFree/HarmonicAnalysis/Mellin/*`：Mellin 反演与竖线移动。
- openai 的 ℚ(ω) 版本（只读）：`…\Hecke L\.cache\openai-math-fd4aeeb2\lean\OAI\NumberTheory\DirichletL\` 下的 `Moments/PrimeGlobal.lean`、`Moments/PrimeHeight.lean`、`Hecke/Prime*.lean`、`Hecke/LogDerivative*.lean`，合计约 7,000 行，可照着推广。
- 同项目的 `HeckeSkeleton/PrimeNormalizer.lean` 是同一类问题（窗口里的素理想）的完整推导样例。

## 6. 规模与完成标准

估计 7,000–9,000 行。可以拆成两半：对数导数界一半，Mellin 与素理想幂一半。

**完成标准**
1. 新模块构建通过，没有 `sorry`、`admit`、`axiom`、`native_decide`。
2. 给出与模型无关的一般定理，假设显式列出。
3. `#print axioms` 只有 `propext, Classical.choice, Quot.sound`。
4. 写一页报告：定理陈述、假设清单，以及在实际模型上接线时还缺什么（应只剩 MI-M-MODELS 提供的事实）。

**约束**
- 一次只构建一个模块，不跑全量构建。
- 不提交，不修改现有文件。
- 旧缓存与 openai 目录只读。
