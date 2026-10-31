# EXPANSION 主定理的源码契约

以下代码块摘录对应 `.lean` 文件的源码契约：定理只保留陈述，必要的数据定义保留正文。它们不是额外公理或待 Lean 编译的声明文件。历史核心契约与本批原始接口的验证状态分别注明。验证状态以 [EXPANSION_REPORT.md](EXPANSION_REPORT.md) 的证据为准；源码中写出证明不表示该版本已经通过编译。

每项同时列出所在命名空间和此前的 section 参数，包含数域、有限异常集、真实行数据及物理 slot 输入的类型。Lean 只把实际使用的 section 参数推广到该定理；完整 import、符号解析上下文和证明在各自链接的源文件中。

## `actual_terminal_product_eventually`

真实终端源到有界共同频率乘积；该源码已在 checkpoint2 的 CI 编译并检查打印公理。

源码：[Expansion/TerminalFourierTail.lean](../Expansion/TerminalFourierTail.lean)。命名空间：`Expansion.Dyadic`。

Section 参数：

```lean
variable {K : Type*} [Field K] [NumberField K]
```

定理陈述：

```lean
theorem actual_terminal_product_eventually
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (τ : ℝ) (hτ : 0 < τ) (CZ : ℝ) (hCZ : 0 ≤ CZ)
    (hzeta : Summable (fun I : NonzeroIntegralIdeal (K := K) =>
      nonzeroIdealNorm I ^ (-2 : ℝ)))
    (hCZsum : (∑' I : NonzeroIntegralIdeal (K := K),
      nonzeroIdealNorm I ^ (-2 : ℝ)) ≤ CZ) :
    ∃ C U₀ : ℝ, 0 < C ∧ 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ (w : Ideal (𝓞 K) →*₀ ℂ), (∀ I, ‖w I‖ ≤ 1) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ D : ℝ, 0 < D →
      ∀ s : ℂ, 0 ≤ s.re →
      (1 / 4 : ℝ) ≤ ‖∑ I ∈ terminalIdealSet (U ^ (21 : ℕ)),
        terminalTerm w V V D (U ^ (21 : ℕ))
          (fun n => (n : ℂ) ^ (-s) *
            (Real.exp (-(n : ℝ) / U ^ (20 : ℕ)) : ℂ)) I‖ →
      let n := dyadicCap (3 * U ^ (21 : ℕ))
      ∃ j ≤ n, ∃ k ≤ n,
        ((2 : ℝ) ^ j < 4 * D ∧ D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
          (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * U ^ (21 : ℕ)) ∧
      ∃ t : ℝ,
        ‖t‖ ≤ U ^ τ / (8 * Real.pi + 8) ∧
        (1 / 8 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (n + 1 : ℕ) * C *
          ((2 : ℝ) ^ j) ^ (1 / 2 - s.re) *
          ((2 : ℝ) ^ k) ^ (1 / 2 - s.re) *
          ‖normalizedPolynomial (nonzeroTerminalSet (6 * U ^ (21 : ℕ)))
              (inverseRawCoefficient w V D) idealNorm annularProfile
              ((2 : ℝ) ^ j) s.re (2 * Real.pi * t - s.im) *
            normalizedPolynomial (nonzeroTerminalSet (6 * U ^ (21 : ℕ))) w
              idealNorm annularProfile ((2 : ℝ) ^ k) s.re
              (2 * Real.pi * t - s.im)‖
```

## `exists_original_masked_product`

普通 Hecke 零点到原始掩码乘积；不把终端源下界作为输入。实际项目依赖链待完成核验。

源码：[Expansion/ActualHeckeWitness.lean](../Expansion/ActualHeckeWitness.lean)。命名空间：`Expansion.Project`。

Section 参数：

```lean
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
```

定理陈述：

```lean
theorem exists_original_masked_product
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (radial : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R θ τ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hτ : 0 < τ)
    (hbudget : heightDegree K * θ ≤ 1)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hVnorm : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (hVcomp : ∀ x : ℝ, 0 ≤ x → ‖1 - V x‖ ≤ 1) :
    ∃ C U₀ : ℝ, 0 < C ∧ 2 ≤ U₀ ∧
      ∀ (χ : HeckeCharacter K) (u : NonzeroIdeal K) (U D : ℝ),
      U₀ ≤ U →
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = radial →
      heckeArchWeight K χ = weight →
      heckeConductorScale K χ ≤ R * U → HeckeGeneral.Analysis.idealNorm K u ≤ 2 * U →
      2 ≤ D → D ≤ U ^ (3 / 2 : ℝ) →
      ∀ ρ : ℂ, heckeContinuation K χ ρ = 0 →
      51 / 100 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ U ^ θ →
      let n := dyadicCap (3 * U ^ (21 : ℕ))
      ∃ j ≤ n, ∃ k ≤ n,
        (((2 : ℝ) ^ j < 4 * D) ∧
          D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
          (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * U ^ (21 : ℕ)) ∧
        ∃ t : ℝ,
        ‖t‖ ≤ U ^ τ / (8 * Real.pi + 8) ∧
        (1 / 8 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (n + 1 : ℕ) * C *
          ((2 : ℝ) ^ j) ^ (1 / 2 - ρ.re) *
          ((2 : ℝ) ^ k) ^ (1 / 2 - ρ.re) *
          ‖normalizedPolynomial (nonzeroTerminalSet (6 * U ^ (21 : ℕ)))
              (inverseRawCoefficient (originalMaskedCoefficientHom K S χ u) V D)
              Expansion.Dyadic.idealNorm annularProfile
              ((2 : ℝ) ^ j) ρ.re (2 * Real.pi * t - ρ.im) *
            normalizedPolynomial (nonzeroTerminalSet (6 * U ^ (21 : ℕ)))
              (originalMaskedCoefficientHom K S χ u)
              Expansion.Dyadic.idealNorm annularProfile
              ((2 : ℝ) ^ k) ρ.re (2 * Real.pi * t - ρ.im)‖
```

## `exists_actual_terminal_saturation`

在实际终端源下界下推出两因子的饱和与长度界；实际项目依赖链待完成核验。

源码：[Expansion/ActualTerminalSaturation.lean](../Expansion/ActualTerminalSaturation.lean)。命名空间：`Expansion.ActualTerminalSaturation`。

Section 参数：

```lean
variable (K : Type) [Field K] [NumberField K]
```

定理陈述：

```lean
theorem exists_actual_terminal_saturation
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hVnorm : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (R θ τ η : ℝ) (hR : 1 ≤ R) (hθ : 0 ≤ θ) (hτ : 0 < τ) (hη : 0 < η)
    (hforward : 132 * e + 2 * ε + heightDegree K * ε * θ ≤ η / 4)
    (hreflected : 12 * e + 2 * ε + heightDegree K * θ * (1 + ε) ≤ η / 4)
    (CZ : ℝ) (hCZ : 0 ≤ CZ)
    (hzeta : Summable (fun I : NonzeroIntegralIdeal (K := K) =>
      nonzeroIdealNorm I ^ (-2 : ℝ)))
    (hCZsum : (∑' I : NonzeroIntegralIdeal (K := K),
      nonzeroIdealNorm I ^ (-2 : ℝ)) ≤ CZ) :
    ∃ U₀ : ℝ, 6 ≤ U₀ ∧ ∀ (χ : HeckeCharacter K)
      (I : Ideal (𝓞 K)) (E : Finset (HeightOneSpectrum (𝓞 K)))
      (U a H Hupper D : ℝ) (s : ℂ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = arch → heckeArchWeight K χ = weight →
      I ≠ 0 → (∀ p ∈ E, p.asIdeal ∣ I) →
      U₀ ≤ U → 51 / 100 ≤ a → a ≤ s.re → s.re ≤ 1 → 0 < D →
      (Ideal.absNorm I : ℝ) ≤ R * U → heckeConductorScale K χ ≤ R * U →
      2 + Hupper ≤ R * U ^ θ → U ^ τ ≤ H →
      |s.im| + 2 * Real.pi * (U ^ τ / (8 * Real.pi + 8)) + H + 3 / 2 ≤ Hupper →
      ZeroUpperBound K χ Hupper (a + 2 * e) →
      (1 / 4 : ℝ) ≤ ‖∑ J ∈ terminalIdealSet (U ^ (21 : ℕ)),
        terminalTerm (idealCoefficientHom (deletePrimes K E (primeCoefficient K χ)))
          V V D (U ^ (21 : ℕ))
          (fun n => (n : ℂ) ^ (-s) *
            (Real.exp (-(n : ℝ) / U ^ (20 : ℕ)) : ℂ)) J‖ →
      let n := Expansion.Dyadic.dyadicCap (3 * U ^ (21 : ℕ))
      ∃ j ≤ n, ∃ k ≤ n, ∃ ξ : ℝ,
        ‖ξ‖ ≤ U ^ τ / (8 * Real.pi + 8) ∧
        ((2 : ℝ) ^ j < 4 * D ∧ D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
          (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * U ^ (21 : ℕ)) ∧
        let r := Expansion.Dyadic.dyadicLength U j
        let m := Expansion.Dyadic.dyadicLength U k
        let ν := 2 * Real.pi * ξ - s.im
        let M := inverseDetectorValue K χ E V D U j s.re ν
        let S := plainDetectorValue K χ E U k s.re ν
        U ^ ((2 * a - 1) * (r + m) - η) ≤ ‖M * S‖ ^ 2 ∧
        ‖M‖ ^ 2 ≤ U ^ ((2 * a - 1) * r + η) ∧
        ‖S‖ ^ 2 ≤ U ^ ((2 * a - 1) * min m (1 - m) + η) ∧
        U ^ ((2 * a - 1) * r - 2 * η) ≤ ‖M‖ ^ 2 ∧
        U ^ ((2 * a - 1) * m - 2 * η) ≤ ‖S‖ ^ 2 ∧
        m ≤ 1 / 2 + 75 * η ∧
        Real.log D / Real.log U - 1 / 2 - 75 * η - Real.log 8 / Real.log U ≤ r
```

## `exists_original_masked_saturation`

普通 Hecke 零点和缓冲上零点界直接给出饱和；终端源、Mellin 多项式界均由证明供应。实际项目依赖链待完成核验。

源码：[Expansion/ActualHeckeSaturation.lean](../Expansion/ActualHeckeSaturation.lean)。命名空间：`Expansion.Project`。

Section 参数：

```lean
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
```

定理陈述：

```lean
theorem exists_original_masked_saturation
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hVnorm : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (hVcomp : ∀ x : ℝ, 0 ≤ x → ‖1 - V x‖ ≤ 1)
    (R θzero θ τ η : ℝ) (hR : 1 ≤ R)
    (hθzero : 0 ≤ θzero) (hθ : 0 ≤ θ) (hτ : 0 < τ) (hη : 0 < η)
    (hzeroBudget : heightDegree K * θzero ≤ 1)
    (hforward : 132 * e + 2 * ε + heightDegree K * ε * θ ≤ η / 4)
    (hreflected : 12 * e + 2 * ε + heightDegree K * θ * (1 + ε) ≤ η / 4) :
    ∃ U₀ : ℝ, 6 ≤ U₀ ∧ ∀ (χ : HeckeCharacter K) (u : NonzeroIdeal K)
      (U a H Hupper D : ℝ) (ρ : ℂ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = arch → heckeArchWeight K χ = weight →
      U₀ ≤ U → HeckeGeneral.Analysis.idealNorm K u ≤ 2 * U →
      heckeConductorScale K χ ≤ R * U → 2 ≤ D → D ≤ U ^ (3 / 2 : ℝ) →
      51 / 100 ≤ a → a ≤ ρ.re → ρ.re ≤ 1 →
      0 < meromorphicOrderAt (heckeContinuation K χ) ρ → |ρ.im| ≤ U ^ θzero →
      2 + Hupper ≤ R * U ^ θ → U ^ τ ≤ H →
      |ρ.im| + 2 * Real.pi * (U ^ τ / (8 * Real.pi + 8)) + H + 3 / 2 ≤ Hupper →
      ZeroUpperBound K χ Hupper (a + 2 * e) →
      let n := Expansion.Dyadic.dyadicCap (3 * U ^ (21 : ℕ))
      ∃ j ≤ n, ∃ k ≤ n, ∃ ξ : ℝ,
        ‖ξ‖ ≤ U ^ τ / (8 * Real.pi + 8) ∧
        ((2 : ℝ) ^ j < 4 * D ∧ D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
          (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * U ^ (21 : ℕ)) ∧
        let r := Expansion.Dyadic.dyadicLength U j
        let m := Expansion.Dyadic.dyadicLength U k
        let ν := 2 * Real.pi * ξ - ρ.im
        let M := inverseDetectorValue K χ (originalDeletedPrimes K S u) V D U j ρ.re ν
        let P := plainDetectorValue K χ (originalDeletedPrimes K S u) U k ρ.re ν
        U ^ ((2 * a - 1) * (r + m) - η) ≤ ‖M * P‖ ^ 2 ∧
        ‖M‖ ^ 2 ≤ U ^ ((2 * a - 1) * r + η) ∧
        ‖P‖ ^ 2 ≤ U ^ ((2 * a - 1) * min m (1 - m) + η) ∧
        U ^ ((2 * a - 1) * r - 2 * η) ≤ ‖M‖ ^ 2 ∧
        U ^ ((2 * a - 1) * m - 2 * η) ≤ ‖P‖ ^ 2 ∧
        m ≤ 1 / 2 + 75 * η ∧
        Real.log D / Real.log U - 1 / 2 - 75 * η - Real.log 8 / Real.log U ≤ r
```

## `exists_canonical_row_saturation`

实际物理行自动供应算术参数、统一导子界与非范数角色条件；实际项目依赖链待完成核验。

源码：[Expansion/CanonicalRowSaturation.lean](../Expansion/CanonicalRowSaturation.lean)。命名空间：`Expansion.Project`。

Section 参数：

```lean
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (E : RowEulerData K S P) (ψ : HeckeCharacter K)
```

定理陈述：

```lean
theorem exists_canonical_row_saturation
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hVnorm : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (hVcomp : ∀ x : ℝ, 0 ≤ x → ‖1 - V x‖ ≤ 1)
    (Cheight θzero θ τ η : ℝ)
    (hθzero : 0 ≤ θzero) (hθ : 0 ≤ θ) (hτ : 0 < τ) (hη : 0 < η)
    (hzeroBudget : heightDegree K * θzero ≤ 1)
    (hforward : 132 * e + 2 * ε + heightDegree K * ε * θ ≤ η / 4)
    (hreflected : 12 * e + 2 * ε + heightDegree K * θ * (1 + ε) ≤ η / 4) :
    ∃ U₀ : ℝ, 6 ≤ U₀ ∧ ∀ (u : FrequencyRow K S)
      (U a height H Hupper D : ℝ),
      U₀ ≤ U → U < frequencyRowNorm K S u → frequencyRowNorm K S u ≤ 2 * U →
      2 ≤ D → D ≤ U ^ (3 / 2 : ℝ) → 51 / 100 ≤ a →
      rowZeroAbove K S ψ {1} P E u height a → height ≤ U ^ θzero →
      2 + Hupper ≤ Cheight * U ^ θ → U ^ τ ≤ H →
      height + 2 * Real.pi * (U ^ τ / (8 * Real.pi + 8)) + H + 3 / 2 ≤ Hupper →
      rowZeroBelow K S ψ {1} P E u Hupper (a + 2 * e) →
      ∃ i : Fin 2, ∃ ρ : ℂ,
        0 < meromorphicOrderAt
          (heckeContinuation K (canonicalDetectorCharacter K ψ S P E i u)) ρ ∧
        a ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ height ∧
        let n := Expansion.Dyadic.dyadicCap (3 * U ^ (21 : ℕ))
        ∃ j ≤ n, ∃ k ≤ n, ∃ ξ : ℝ,
          ‖ξ‖ ≤ U ^ τ / (8 * Real.pi + 8) ∧
          ((2 : ℝ) ^ j < 4 * D ∧ D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
            (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * U ^ (21 : ℕ)) ∧
          let r := Expansion.Dyadic.dyadicLength U j
          let m := Expansion.Dyadic.dyadicLength U k
          let ν := 2 * Real.pi * ξ - ρ.im
          let χ := canonicalDetectorCharacter K ψ S P E i u
          let M := inverseDetectorValue K χ (originalDeletedPrimes K S u.ideal.val)
            V D U j ρ.re ν
          let Q := plainDetectorValue K χ (originalDeletedPrimes K S u.ideal.val) U k ρ.re ν
          U ^ ((2 * a - 1) * (r + m) - η) ≤ ‖M * Q‖ ^ 2 ∧
          ‖M‖ ^ 2 ≤ U ^ ((2 * a - 1) * r + η) ∧
          ‖Q‖ ^ 2 ≤ U ^ ((2 * a - 1) * min m (1 - m) + η) ∧
          U ^ ((2 * a - 1) * r - 2 * η) ≤ ‖M‖ ^ 2 ∧
          U ^ ((2 * a - 1) * m - 2 * η) ≤ ‖Q‖ ^ 2 ∧
          m ≤ 1 / 2 + 75 * η ∧
          Real.log D / Real.log U - 1 / 2 - 75 * η - Real.log 8 / Real.log U ≤ r
```

## `exists_physical_row_detection`

选择显式内部损失和高度上限后，对所有有限高度数和足够大物理尺度统一检测；实际项目依赖链待完成核验。

源码：[Expansion/PhysicalRowDetection.lean](../Expansion/PhysicalRowDetection.lean)。命名空间：`Expansion.Project`。

Section 参数：

```lean
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (E : RowEulerData K S P) (ψ : HeckeCharacter K)
```

定理陈述：

```lean
theorem exists_physical_row_detection
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (η : ℝ) (hη : 0 < η) :
    ∃ e ε ceiling : ℝ,
      0 < e ∧ e < 1 / 1000 ∧ e ≤ η ∧ 0 < ε ∧ 0 < ceiling ∧
      ∀ N : ℕ, ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
          ∀ d t a : ℝ, 1 / 16 ≤ d → d ≤ 1 → 1 ≤ t → t ≤ 3 / 2 → 51 / 100 ≤ a →
          ∀ h : ℕ, h ≤ N → ∀ u : FrequencyRow K S,
            Z ^ d < frequencyRowNorm K S u → frequencyRowNorm K S u ≤ 2 * Z ^ d →
            rowZeroAbove K S ψ {1} P E u (ExpansionInterfaces.selectedHeight h (Z ^ τ)) a →
            rowZeroBelow K S ψ {1} P E u (ExpansionInterfaces.upperHeight h (Z ^ τ)) (a + 2 * e) →
            Nonempty (CanonicalDyadicDetection K S P E ψ u (Z ^ d) a t η τ (Z ^ τ) N)
```

## `exists_physical_witness_cover`

实际零点 bin 到原有 WitnessCover 及六维参数盒；这是下述全尺度实际 recipe 的局部 detector 契约。完整全局积分与实际分量已在本批原始接口源码中接线，当前项目依赖链仍待原生 CI 核验。

源码：[Expansion/PhysicalWitnessCover.lean](../Expansion/PhysicalWitnessCover.lean)。命名空间：`Expansion.Project`。

Section 参数：

```lean
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (E : RowEulerData K S P) (ω ψ : HeckeCharacter K)
variable (g : PrimeWindowGeometry)
variable (slotTime : Fin g.slots → (Fin 3 → ℝ) → ℝ)
variable (slotPower : Fin g.slots → (Fin 3 → ℝ) → ℂ)
variable (slotCoefficient : Fin g.slots → HeckeCharacter K)
```

定理陈述：

```lean
theorem exists_physical_witness_cover
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ e ε ceiling k : ℝ,
      0 < e ∧ e < 1 / 1000 ∧ e ≤ lam / 1000 ∧ 0 < ε ∧ 0 < ceiling ∧ 0 < k ∧
      ∀ N : ℕ, ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
          ∀ d a : ℝ, 1 / 16 ≤ d → d ≤ 1 → 51 / 100 ≤ a →
          ∀ h : ℕ, h ≤ N → ∀ sector : SixthUnitClasses K S,
          ∀ rows : Finset (FrequencyRow K S),
            (∀ u ∈ rows, Z ^ d < frequencyRowNorm K S u) →
            (∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * Z ^ d) →
            (∀ u ∈ rows, u.sector = sector) →
            (∀ u ∈ rows, rowZeroAbove K S ψ {1} P E u
              (ExpansionInterfaces.selectedHeight h (Z ^ τ)) a) →
            (∀ u ∈ rows, rowZeroBelow K S ψ {1} P E u
              (ExpansionInterfaces.upperHeight h (Z ^ τ)) (a + 2 * e)) →
            ∀ p : Fin 3 → ℝ, ‖p‖ ≤ Z ^ τ → ∀ amplitude : Fin g.slots → ℝ,
            ∃ A : RecipeAmplitudeData K S ψ g
              (scaledCanonicalRecipeFamily K ψ g cutoffProfile slotTime slotPower slotCoefficient
                (3 * ((N : ℝ) + 1))),
              A.candidates = rows ∧ A.sector = sector ∧ A.physical = p ∧
              A.amplitude = amplitude ∧ A.rows (Z ^ d) = rows ∧
              ∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 →
                WitnessCover (A.toAmplitude (P := P) (R := E.rows) (ω := ω)
                  Z (Z ^ τ) (Z ^ d)) t (2 * a - 1) (Z ^ d) lam k ∧
                ∀ j : Fin (A.witnessCount t),
                  ‖(A.witness t j).heights p t (Z ^ τ)‖ = Z ^ τ ∧
                  (∀ I : NonzeroIdeal K, ‖(A.witness t j).realShifts I‖ ≤ 8) ∧
                  (∀ I : NonzeroIdeal K, ‖(A.witness t j).imagShifts I‖ ≤
                    1 + ‖(A.witness t j).heights p t (Z ^ τ)‖)
```

## `exists_actual_finite_height_logDeriv_bound`

真实 Hecke 函数在有限零点缓冲内的对数导数界。常数先于字符、尺度、零点边界和评价点选择；没有全高度无零点假设或待证对数导数界作为前提。当前源码待实际项目编译核验；素数窗口的有限矩形积分、补偿及尾项由后述契约和本批实际接口分别接线，不属于本条局部对数导数结论。

源码：[Expansion/PhysicalLogDerivative.lean](../Expansion/PhysicalLogDerivative.lean)。命名空间：`Expansion.Project`。

Section 参数：

```lean
variable (K : Type) [Field K] [NumberField K]
```

定理陈述：

```lean
theorem exists_actual_finite_height_logDeriv_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ (χ : HeckeCharacter K) (U β δ σ t Hupper : ℝ),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        β + δ ≤ σ → σ ≤ 2 → |t| + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        ‖deriv (heckeContinuation K χ) (verticalPoint σ t) /
          heckeContinuation K χ (verticalPoint σ t)‖ ≤
          48 * (1 + Real.log C + (5 / 8) * Real.log U +
            heightDegree K * Real.log (4 + |t|) + A) / δ ^ 2
```

## `exists_actual_annular_primePower_bound`

实际有限素数幂和的有限矩形估计，保留左右直线与横边尾项；当前版本尚待编译核验。

源码：[Expansion/ActualPrimeContour.lean](../Expansion/ActualPrimeContour.lean)。命名空间：`Expansion.Project`。

Section 参数：

```lean
variable (K : Type) [Field K] [NumberField K]
```

定理陈述：

```lean
theorem exists_actual_annular_primePower_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ (χ : HeckeCharacter K) (W : AnnularProfile) (order : ℕ)
        (U β δ ν H X Hupper : ℝ),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        0 < H → 1 ≤ X → |ν| + H + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        let CW := W.contourConstant (1 / 2) 2 order
        let M := actualPrimeLogRectangleBound K C A U δ ν H
        ‖actualAnnularPrimePowerSum K χ W X ν‖ ≤ (1 / (2 * Real.pi)) *
          ((M * X ^ (β + δ)) * CW +
            2 * (CW / (1 + H) ^ order) * M * X ^ (2 : ℝ) * (2 - (β + δ)) +
            (actualPrimeLogMass K 2 * X ^ (2 : ℝ)) * (CW / H ^ order))
```

## `exists_actual_logDivided_primePower_bound`

原始固定窗口的实际去对数权素数幂有限矩形估计，常数先于尺度选择；当前版本尚待编译核验。

源码：[Expansion/ActualLogDividedContour.lean](../Expansion/ActualLogDividedContour.lean)。命名空间：`Expansion.Project`。

Section 参数：

```lean
variable (K : Type) [Field K] [NumberField K]
```

定理陈述：

```lean
theorem exists_actual_logDivided_primePower_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (order : ℕ) :
    ∃ C A P₀ CW : ℝ, 1 ≤ C ∧ 1 ≤ A ∧ 2 ≤ P₀ ∧ 0 ≤ CW ∧
      ∀ (χ : HeckeCharacter K) (U β δ H P Hupper : ℝ),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        0 < H → P₀ ≤ P → H + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        let M := actualPrimeLogRectangleBound K C A U δ 0 H
        ‖actualLogDividedPrimePowerSum K χ W P‖ ≤ (1 / (2 * Real.pi)) *
          ((M * P ^ (β + δ)) * CW +
            2 * (CW / (1 + H) ^ order) * M * P ^ (2 : ℝ) * (2 - (β + δ)) +
            (actualPrimeLogMass K 2 * P ^ (2 : ℝ)) * (CW / H ^ order))
```

## `exists_actual_finite_height_prime_bound`

真实去对数权素数和的有限缓冲估计，加统一平方根素数幂尾项；当前版本尚待编译核验。

源码：[Expansion/ActualPrimeCancellation.lean](../Expansion/ActualPrimeCancellation.lean)。命名空间：`Expansion.Project`。

Section 参数与显式三项 envelope：

```lean
variable (K : Type) [Field K] [NumberField K]

def actualPrimeCancellationEnvelope (C A CW : ℝ) (order : ℕ)
    (U β δ H P : ℝ) : ℝ :=
  let M := actualPrimeLogRectangleBound K C A U δ 0 H
  (1 / (2 * Real.pi)) *
    ((M * P ^ (β + δ)) * CW +
      2 * (CW / (1 + H) ^ order) * M * P ^ (2 : ℝ) * (2 - (β + δ)) +
      (actualPrimeLogMass K 2 * P ^ (2 : ℝ)) * (CW / H ^ order))
```

定理陈述：

```lean
theorem exists_actual_finite_height_prime_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (order : ℕ) :
    ∃ C A P₀ CW B : ℝ, 1 ≤ C ∧ 1 ≤ A ∧ 2 ≤ P₀ ∧ 0 ≤ CW ∧ 0 < B ∧
      ∀ (χ : HeckeCharacter K) (U β δ H P Hupper : ℝ),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        0 < H → P₀ ≤ P → H + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        ‖primeSum (actualPrimeNorm K) (primeCoefficient K χ) W P‖ ≤
          actualPrimeCancellationEnvelope K C A CW order U β δ H P + B * Real.sqrt P
```

## 原始接口：19 个指定目标及实际配套契约（原 15 项及新增 4 项）

**状态：proof-written, pending native CI（证明和数据构造已写，等待原生 CI）。**
原 15 项按源码基线 63fb331c54b3b12b00a5b9a55fc963e30f7a6c93 摘录，新增 4 项取自其后的当前工作树，列在总表末尾和本节追加部分。63fb 的 pure 组已通过，余四组在本次更新时仍运行；新增 4 项等待下一批 CI。指定目标集合整体仍未获得通过结论。前文保留的 checkpoint2 等历史证据只适用于其对应提交和声明。

当前 expansionRecipeRaw 已由 actualPhysicalRecipe 构造，actualHighPresentation 也已有原始行与积分的识别实现；不再将二者描述为 raw admitted 占位。是否整个依赖闭包已经排除非标准公理，必须由本轮原生编译和下述独立检查确认，不能从源码中存在证明正文推出。

### 指定目标与审计口径

下表顺序逐字对应 [scripts/expansion_verify.py](../scripts/expansion_verify.py) 的 NAMED_EXPANSION_TARGETS。检查读取声明本身及其依赖，包括类型依赖；唯一允许的公理是 propext、Classical.choice、Quot.sound。通用 skeleton 组记录历史继承公理的日志，不能替代这 19 个目标的严格检查。STRICT_SOURCE_MODULES 同时全量严格审计 HeckeSkeleton.SourceData、HeckeSkeleton.ExpansionModels.SourceData 和新增 HeckeSkeleton.ExpansionModels.ActualRowEligibility；新增 leaf 不通过反向导入 Moments 取得行资格结论。

| 序号 | 完整声明名 | 源文件 | 接口作用 |
| --- | --- | --- | --- |
| 1 | HeckeSkeleton.expansionPhysicalParameters | [HeckeSkeleton/Base.lean](../HeckeSkeleton/Base.lean) | 原始上下文的单次 detector 参数选择 |
| 2 | HeckeSkeleton.expansionRecipeRaw | [HeckeSkeleton/Base.lean](../HeckeSkeleton/Base.lean) | 同一全尺度实际展开数据 |
| 3 | HeckeSkeleton.expansionRecipeRaw_geometry | [HeckeSkeleton/Base.lean](../HeckeSkeleton/Base.lean) | 原始 raw 数据的统一长度与参数盒 |
| 4 | HeckeSkeleton.actualHighPresentation | [HeckeSkeleton/HighBin.lean](../HeckeSkeleton/HighBin.lean) | 原始块的实际行、标签和移线积分识别 |
| 5 | HeckeSkeleton.expansionBudget | [HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean) | 先于 τ 的共同高度次数与上限 |
| 6 | HeckeSkeleton.expansionCutoffsRaw | [HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean) | 同一源阈值与 retained 阈值的数值选择 |
| 7 | HeckeSkeleton.expansionCutoffs | [HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean) | 供所有分量使用的公共阈值及常数 |
| 8 | HeckeSkeleton.expansion_identity | [HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean) | 原 probe 减 signal 的完整分解 |
| 9 | HeckeSkeleton.expansion_principal | [HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean) | 三个原主行节省的和 |
| 10 | HeckeSkeleton.expansion_small | [HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean) | 原小行节省 1/50 |
| 11 | HeckeSkeleton.expansion_large | [HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean) | 原大行节省 63/800 |
| 12 | HeckeSkeleton.expansion_blockCount | [HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean) | 无高度因子的块数界 |
| 13 | HeckeSkeleton.expansion_blocks | [HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean) | 每个原块的 BlockSource |
| 14 | HeckeSkeleton.expansion_tail | [HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean) | 在原 HighBoundaryControl 前提下的任意阶尾界 |
| 15 | HeckeSkeleton.expansionSource | [HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean) | 固定高度预算后统一组装 ExpansionSource |
| 16 | HeckeSkeleton.actualRecipeRowEligibility | [HeckeSkeleton/ExpansionModels/ActualRowEligibility.lean](../HeckeSkeleton/ExpansionModels/ActualRowEligibility.lean) | 同一实际 source 的全部行资格；待下一批 CI |
| 17 | HeckeSkeleton.actualRecipeSourceGeometry | [HeckeSkeleton/ExpansionModels/ActualRowEligibility.lean](../HeckeSkeleton/ExpansionModels/ActualRowEligibility.lean) | 同一实际 source 的长度和参数盒；待下一批 CI |
| 18 | HeckeSkeleton.moment_polynomial_calibration | [HeckeSkeleton/Moments.lean](../HeckeSkeleton/Moments.lean) | 原模型的完整多项式 calibration；待下一批 CI |
| 19 | HeckeSkeleton.moment_row_eligibility | [HeckeSkeleton/Moments.lean](../HeckeSkeleton/Moments.lean) | 保留原 hcal 签名的行资格兼容接口；待下一批 CI |

### 原始目标上下文

以下 19 项均处于 HeckeSkeleton 命名空间，使用原来的数域和 TargetContext；没有另建一个满足结论的替代目标。原始上下文的定义为：

源码：[HeckeSkeleton/Base.lean](../HeckeSkeleton/Base.lean)。命名空间：HeckeSkeleton。

```lean
variable (K : Type) [Field K] [NumberField K]

structure FamilyContext where
  root12 : K
  primitive12 : IsPrimitiveRoot root12 12
  omega : HeckeCharacter K
  B : ℝ
  B_lower : 7 / 8 < B
  B_upper : B ≤ 1
  boundary : ∀ χ : HeckePacketIndex K omega, ∀ r ∈ heckePacketZeros K omega χ,
    1 / 2 ≤ r → r ≤ 1 → r ≤ B
  lamA : ℝ
  lamA_pos : 0 < lamA
  lamA_small : lamA ≤ 1 / 1000

structure TargetContext where
  family : FamilyContext K
  geometry : PrimeWindowGeometry
  mesh_fine : (1 / 3 : ℝ) / geometry.slots ≤ (momentMesh K family).val
  lamB : ℝ
  lamB_pos : 0 < lamB
  target : HeckePacketIndex K family.omega
```

这些字段保留 7/8 < B ≤ 1、同一个 packet 零点边界、原几何和两项损失参数。下面出现的原 probe、角色代表、局部测度与测试函数均来自这个 c。实际算术、Fourier 零值和归一化非零事实由 ActualProbeContext 对同一个 axiomChoice 提供；没有再次独立选择一个测试函数。

### 目标 1–3：固定参数、实际 raw 构造与全尺度几何

源码：[HeckeSkeleton/Base.lean](../HeckeSkeleton/Base.lean)。命名空间：HeckeSkeleton。

```lean
def expansionPhysicalParameters (c : TargetContext K) :
    Expansion.Project.PhysicalRecipeParameters K (places K c) (probeData K c)
      c.family.omega (targetCharacter K c) c.geometry
      (HighBinActualEuler.arithmeticHighEulerData K (places K c) (probeData K c)
        (targetCharacter K c))
      (representative K c).val.property (expansionBoundary_lower K c) c.family.B_upper
      c.family.boundary (probeMeasures K c).haar ∅ c.family.lamA
      (expansionShellAllowance K c) (expansionInternalCap K c) :=
  Expansion.Project.choosePhysicalRecipeParameters K (places K c) (probeData K c)
    c.family.omega (targetCharacter K c) c.geometry
    (HighBinActualEuler.arithmeticHighEulerData K (places K c) (probeData K c)
      (targetCharacter K c))
    (representative K c).val.property (expansionBoundary_lower K c) c.family.B_upper
    c.family.boundary (probeMeasures K c).haar ∅ (isComplex_of_family K c)
    c.family.lamA (expansionShellAllowance K c) (expansionInternalCap K c)
    c.family.lamA_pos (by linarith [c.family.lamA_small])
    (ExpansionInterfaces.shellAllowance_spec c.family.lamA_pos).2.2
    (expansionInternalCap_pos K c)

def expansionRecipeRaw (c : TargetContext K) :
    ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c) :=
  Expansion.Project.actualPhysicalRecipe K (excludedPlaces K c)
    (Expansion.ActualProbeContext.allLocalMeasures K) (probeData K c)
    c.family.omega (targetCharacter K c) c.geometry (representative K c).val.property
    (expansionBoundary_lower K c) c.family.B_upper c.family.boundary c.family.lamA
    (expansionShellAllowance K c) (expansionInternalCap K c) (expansionPhysicalParameters K c)

theorem expansionRecipeRaw_geometry (c : TargetContext K) :
    (expansionRecipeRaw K c).MomentGeometry 22
```

expansionPhysicalParameters 的类型固定同一个 P、算术 E、原目标角色、prime-window 几何和局部测度族。其 e、width、k、ceiling 在 τ、Z、T 和外部尾阶之前选定。内部 eCap 在 Base 中是 min lamA lamB / 1000；shell allowance 仍取自 lamA。raw 构造不接收目标估计或展开恒等式作为参数。

MomentGeometry 22 是当前原始声明的结论：对该 recipe 的所有 active 尺度、所有块、所有振幅标签及各细分，控制真实长度和六维参数盒。它也覆盖标签的空行纤维；其精确量词见后面的通用几何定义。本节仅记录这一源码契约，编译状态仍为 pending native CI。

### 目标 4：实际高行 presentation

源码：[HeckeSkeleton/HighBin.lean](../HeckeSkeleton/HighBin.lean)。命名空间：HeckeSkeleton。

```lean
variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)

def actualHighPresentation : ActualHighPresentation K c
```

该定义从 expansionPhysicalParameters 和 expansionRecipeRaw 读取同一个 e、算术 Euler 数据、固定行、有限标签及移线后的实际积分。它的返回类型 ActualHighPresentation 包含 bin/support 条件及 block_identification、shifted_identification，解析范数界仍由各自的接口表达。原始 whole-bin 差分在振幅划分之前定义，且在同一 raw tail 中出现；后面的边界桥明确识别这两个量。

### 目标 5–7：高度预算与同一个公共 cutoff

以下定义正文保留，以明确数值选择和依赖顺序。

源码：[HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean)。命名空间：HeckeSkeleton。

```lean
variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)

def expansionBudget (c : TargetContext K) : {b : ℝ × ℝ // 0 ≤ b.1 ∧ 0 < b.2} := by
  exact ⟨((expansionRetainedData K c).2.2, (expansionPhysicalParameters K c).ceiling),
    (expansionRetainedData_spec K c).2.2.1, (expansionPhysicalParameters K c).ceiling_pos⟩

def expansionCutoffsRaw (c : TargetContext K) (τ : ℝ) :
    {b : ℝ × ℝ // 2 ≤ b.1 ∧ 0 ≤ b.2} := by
  exact ⟨(max (expansionSourceCutoff K c τ) (expansionRetainedData K c).2.1,
      max (expansionRetainedData K c).1 (expansionPhysicalParameters K c).k),
    (expansionSourceCutoff_ge_two K c τ).trans (le_max_left _ _),
    (expansionRetainedData_spec K c).1.le.trans (le_max_left _ _)⟩

def expansionCutoffs (c : TargetContext K) (τ : ℝ) :
    {b : ℝ × ℝ // 2 ≤ b.1 ∧ 0 ≤ b.2} :=
  ⟨(max (expansionCutoffsRaw K c τ).val.1 ((2 : ℝ) ^ 16),
      max (expansionCutoffsRaw K c τ).val.2 (expansionBlockCountConstant K c)),
    (expansionCutoffsRaw K c τ).property.1.trans (le_max_left _ _),
    (expansionCutoffsRaw K c τ).property.2.trans (le_max_left _ _)⟩
```

expansionBudget 只依赖 c：A 来自已写出的实际 retained 估计，ceiling 来自同一个 detector 参数选择。τ 选定以后，expansionSourceCutoff 才选择检测阈值；公共 Z₀ 还吸收 retained 阈值和 2^16 的既有 active guard，公共 k 同时吸收 retained 常数、源常数和高度无关的块数常数。所有分量使用这个公共 pair；不会针对某个尺度、标签或分量重新选择。

共同 retained 常数的来源保留原始量词；C、Z₀、A 在 Z、H 之前选定：

源码：[HeckeSkeleton/ExpansionModels/ActualRecipeEstimates.lean](../HeckeSkeleton/ExpansionModels/ActualRecipeEstimates.lean)。命名空间：HeckeSkeleton。

```lean
variable (K : Type) [Field K] [NumberField K]

def ActualRetainedEstimates (c : TargetContext K) (C Z0 A : ℝ) : Prop :=
  0 < C ∧ 1 ≤ Z0 ∧ 0 ≤ A ∧ ∀ Z H : ℝ, Z0 ≤ Z → 1 ≤ H →
    (‖(highExpansion K c Z H).principal‖ ≤
      C * (Z ^ (c.family.B - 11 / 16 - 23 / 960 + c.lamB) +
        Z ^ (c.family.B - 11 / 16 - 13 / 9600 + c.lamB) +
        Z ^ (c.family.B - 11 / 16 - principalSlotSaving c.geometry + c.lamB)) *
        (1 + H) ^ A) ∧
    (‖(highExpansion K c Z H).small‖ ≤
      C * Z ^ (c.family.B - 11 / 16 - 1 / 50 + c.lamB) * (1 + H) ^ A) ∧
    (‖(highExpansion K c Z H).large‖ ≤
      C * Z ^ (c.family.B - 11 / 16 - 63 / 800 + c.lamB) * (1 + H) ^ A)

theorem exists_actualRetainedEstimates (c : TargetContext K) :
    ∃ b : ℝ × ℝ × ℝ, ActualRetainedEstimates K c b.1 b.2.1 b.2.2
```

### 目标 8–13：原恒等式、三个估计、块数和检测源

源码：[HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean)。命名空间：HeckeSkeleton。

```lean
variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)

theorem expansion_identity (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    (targetData K c).probeFunction (targetCharacter K c) Z -
      (targetData K c).signal (targetCharacter K c) Z =
    (highExpansion K c Z (Z ^ τ)).principal + (highExpansion K c Z (Z ^ τ)).small +
      (highExpansion K c Z (Z ^ τ)).large +
      (∑ b, ((highExpansion K c Z (Z ^ τ)).block b).value) +
      (highExpansion K c Z (Z ^ τ)).tail

theorem expansion_principal (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ‖(highExpansion K c Z (Z ^ τ)).principal‖ ≤
    (expansionCutoffs K c τ).val.2 *
      (Z ^ (c.family.B - 11 / 16 - 23 / 960 + c.lamB) +
       Z ^ (c.family.B - 11 / 16 - 13 / 9600 + c.lamB) +
       Z ^ (c.family.B - 11 / 16 - principalSlotSaving c.geometry + c.lamB)) *
      (1 + Z ^ τ) ^ (expansionBudget K c).val.1

theorem expansion_small (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ‖(highExpansion K c Z (Z ^ τ)).small‖ ≤
    (expansionCutoffs K c τ).val.2 * Z ^ (c.family.B - 11 / 16 - 1 / 50 + c.lamB) *
      (1 + Z ^ τ) ^ (expansionBudget K c).val.1

theorem expansion_large (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ‖(highExpansion K c Z (Z ^ τ)).large‖ ≤
    (expansionCutoffs K c τ).val.2 * Z ^ (c.family.B - 11 / 16 - 63 / 800 + c.lamB) *
      (1 + Z ^ τ) ^ (expansionBudget K c).val.1

theorem expansion_blockCount (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ((highExpansion K c Z (Z ^ τ)).blockCount : ℝ) ≤
    (expansionCutoffs K c τ).val.2 * Z ^ c.lamB

theorem expansion_blocks (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ∀ b, BlockSource c.geometry ((highExpansion K c Z (Z ^ τ)).block b)
    c.family.B c.family.lamA (expansionCutoffs K c τ).val.2 Z
```

所有结论中的 highExpansion 都是同一个 expansionRecipeRaw 的 toHigh 投影；参数、行系数、块值和 tail 不因估计而替换。三个主行幂分别保留 23/960、13/9600 和 principalSlotSaving；小行保留 1/50，大行保留 63/800。块数界是 k·Z^lamB，未乘高度损失。BlockSource 对该 raw recipe 的每个原块量化，k 和阈值先于块、标签、t 和见证细分。

### 目标 14–15：原尾界消费者与源的统一组装

源码：[HeckeSkeleton/Expansion.lean](../HeckeSkeleton/Expansion.lean)。命名空间：HeckeSkeleton。

```lean
variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)

theorem expansion_tail
    (hmove : HighBoundaryControl K c (actualHighPresentation K c)) :
    PowerHeightTailBound (fun Z T₁ => (highExpansion K c Z T₁).tail)

theorem expansionSource :
    ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k : ℝ, 2 ≤ Z₀ ∧ 0 ≤ k ∧
        ∀ Z : ℝ, Z₀ ≤ Z → ExpansionSource c.geometry (targetCharacter K c)
          (targetData K c) c.family.B c.family.lamA c.lamB k A Z (Z ^ τ)
```

EX-TAIL 精确保留原接口的 hmove : HighBoundaryControl K c (actualHighPresentation K c)。该消费者不调用独立的 highBoundaryControl / wholeBoundaryTail 生产者来掩盖此输入。ExpansionSource 则组装恒等式、principal/small/large 三个界、块数和 BlockSource 六项；其本身不包含 PowerHeightTailBound，因而 expansionSource 没有 hmove 参数。

### 通用实际数据：固定一个 q，保留原分量和六项 tail

源码：[Expansion/ActualRecipeData.lean](../Expansion/ActualRecipeData.lean)。命名空间：Expansion.Project。

以下 section 参数和局部记号也从该文件抽取：

```lean
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable (P : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K)))) (omega psi : HeckeCharacter K)
variable (g : PrimeWindowGeometry)
variable {B e : ℝ} (hpsi : psi ∈ HeckePacket K omega)
variable (hB0 : 51 / 100 ≤ B) (hB : B ≤ 1)
variable (hbound : ∀ chi r, r ∈ heckePacketZeros K omega chi →
  1 / 2 ≤ r → r ≤ 1 → r ≤ B)
local notation "E" => arithmeticHighEulerData K Sset P psi
local notation "muS" => (fun p : Sset => mu p.val)
```

实际 tail 的定义是：

```lean
def actualPhysicalExpansionTail (he : 0 < e) (zeta Z H : ℝ) : ℂ :=
  actualPrincipalTail K S mu P psi g Z H B e +
    actualNonprincipalInitialTailSum K S mu P psi g Z H +
    actualSmallRowHorizontalFaces K S mu P psi g ∅ Z H B e +
    actualLargeHorizontalFaces K S mu P psi g Z H zeta +
    physicalScheduledModerateFaces K S mu P E omega psi hpsi hB0 hB he hbound
      g zeta Z H +
    physicalScheduledWholeBoundary K S mu P E omega psi hpsi hB0 hB he hbound
      g zeta Z H
```

六项依次为主行尾、非主行初始截断尾、小行横边、大行横边、中等行调度横边、完整固定 bin 的原线减终线。主行初始积分的盒外补集已经包含在 actualPrincipalTail 中；第二项只含非主行，因此未重复计入主行初始尾。这里的 tail 由这些实际积分和差分构成，没有用“目标左边减其他项”定义。

同一个 q 给出全尺度 recipe 及其源和几何：

```lean
variable (lam zeta eCap : ℝ)
variable (q : PhysicalRecipeParameters K (S : Set (HeightOneSpectrum (𝓞 K))) P omega psi g
  (arithmeticHighEulerData K (S : Set (HeightOneSpectrum (𝓞 K))) P psi)
  hpsi hB0 hB hbound (fun p : (S : Set (HeightOneSpectrum (𝓞 K))) => mu p.val)
  ∅ lam zeta eCap)

def actualPhysicalRecipe : RecipeExpansion K Sset psi g zeta :=
  physicalRecipeExpansion K Sset P omega psi g E hpsi hB0 hB q.e_pos hbound muS ∅
    lam zeta q.width q.k q.width_pos
    (fun Z H => actualPrincipalRetained K S mu P psi g Z H B q.e)
    (fun Z H => actualSmallRetained K S mu P psi g Z H B q.e)
    (fun Z H => actualLargeRetained K S mu P psi g Z H zeta)
    (actualPhysicalExpansionTail K S mu P omega psi g hpsi hB0 hB hbound q.e_pos zeta)

theorem actualPhysicalRecipe_geometry :
    (actualPhysicalRecipe K S mu P omega psi g hpsi hB0 hB hbound lam zeta eCap q).MomentGeometry
      22

theorem actualPhysicalRecipe_source_at_power_height (tau : ℝ)
    (htau : 0 < tau) (hceiling : tau ≤ q.ceiling) :
    ∃ Z0 : ℝ, 2 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ b : Fin ((actualPhysicalRecipe K S mu P omega psi g hpsi hB0 hB hbound
        lam zeta eCap q).activeCount Z (Z ^ tau)),
        BlockSource g (((actualPhysicalRecipe K S mu P omega psi g hpsi hB0 hB hbound
          lam zeta eCap q).toHigh (P := P) (R := E.rows) (ω := omega) Z (Z ^ tau)).block b)
          B lam q.k Z
```

q 的 source 字段来自 physicalRecipeParameters_nonempty / choosePhysicalRecipeParameters 调用的真实 detector 定理；它要求先固定 q，再对每个允许的 τ 选择阈值。actualPhysicalRecipe 在达到 source 阈值之前仍保留相同调度块的真实积分值。toHigh 的 active guard 为 Z ≥ 2^16、T ≥ 1；geometry 对全部 active blocks 量化，source 的渐近阈值是另一项量词。

### 通用实际恒等式：原初始积分到同一个 raw recipe

源码：[Expansion/ActualRecipeIdentity.lean](../Expansion/ActualRecipeIdentity.lean)。命名空间：Expansion.Project。

完整 section 上下文（包括证明专用的有限与完整 adelic Haar 测度）为：

```lean
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

local instance actualIdentity_sectorFintype : Fintype (SixthUnitClasses K Sset) :=
  Fintype.ofFinite _

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)]
variable [BorelSpace (AdeleRing (𝓞 K) K)]
variable (muA : Measure (AdeleRing (𝓞 K) K)) [muA.IsAddHaarMeasure]

variable (P : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (omega psi : HeckeCharacter K) (g : PrimeWindowGeometry)
variable {B : ℝ} (hpsi : psi ∈ HeckePacket K omega)
variable (hB0 : 51 / 100 ≤ B) (hB1 : B ≤ 1)
variable (hboundary : ∀ chi : HeckePacketIndex K omega,
  ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
local notation "E" => arithmeticHighEulerData K Sset P psi
local notation "muS" => (fun p : Sset => mu p.val)
variable (lam zeta eCap : ℝ)
variable (q : PhysicalRecipeParameters K (S : Set (HeightOneSpectrum (𝓞 K))) P omega psi g
  (arithmeticHighEulerData K (S : Set (HeightOneSpectrum (𝓞 K))) P psi) hpsi hB0 hB1 hboundary
  (fun p : (S : Set (HeightOneSpectrum (𝓞 K))) => mu p.val) ∅ lam zeta eCap)
local notation "X" => actualPhysicalRecipe K S mu P omega psi g hpsi hB0 hB1 hboundary
  lam zeta eCap q
```

有限块重排及恒等式的源码陈述为：

```lean
theorem actualPhysicalRecipe_block_sum (Z H : ℝ)
    (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hH : 1 ≤ H) :
    (∑ b, (((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).block b).value) =
      ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
        ∑ c : PhysicalRecipeChoice K Sset B q.e,
          physicalRecipeBlockValue K Sset P E omega psi hpsi hB0 hB1 q.e_pos hboundary
            muS g ∅ zeta Z H j c

include nu muA in
theorem actualPhysicalRecipe_identity
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (hzero : additiveFourierAtZero K Sset muS P.additive = 0)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (hN : physicalResidueNormalizer K Sset muS P ≠ 0)
    (hB : 7 / 8 < B) (he1 : q.e ≤ 1 / 10000) (hzeta : 0 < zeta)
    (Z H : ℝ) (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hH : 1 ≤ H) :
    normalizedProbe K Sset muS P psi g ∅ Z - principalLineProbe K Sset P psi Z =
      ((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).principal +
      ((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).small +
      ((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).large +
      (∑ b, (((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).block b).value) +
      ((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).tail
```

这里的 hzero、hAllowed、hcal、hunram、hN 是原算术和测度背景的具体性质；展开恒等式是结论。原名 specialization 用 ActualProbeContext 和 Base 中已选对象供应这些事实，调用者不再额外提供它们。原始 active guard 只控制这条全尺度积分恒等式的使用范围：

源码：[HeckeSkeleton/ExpansionModels/ActualRecipeEstimates.lean](../HeckeSkeleton/ExpansionModels/ActualRecipeEstimates.lean)。命名空间：HeckeSkeleton。

```lean
variable (K : Type) [Field K] [NumberField K]

theorem expansionRecipeRaw_identity (c : TargetContext K) (Z H : ℝ)
    (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hH : 1 ≤ H) :
    (targetData K c).probeFunction (targetCharacter K c) Z -
      (targetData K c).signal (targetCharacter K c) Z =
      (highExpansion K c Z H).principal + (highExpansion K c Z H).small +
      (highExpansion K c Z H).large +
      (∑ b, ((highExpansion K c Z H).block b).value) +
      (highExpansion K c Z H).tail

theorem expansionRecipeRaw_source (c : TargetContext K) (tau : ℝ)
    (htau : 0 < tau) (hceiling : tau ≤ (expansionPhysicalParameters K c).ceiling) :
    ∃ Z0 : ℝ, 2 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ b : Fin (highExpansion K c Z (Z ^ tau)).blockCount,
        BlockSource c.geometry ((highExpansion K c Z (Z ^ tau)).block b)
          c.family.B c.family.lamA (expansionPhysicalParameters K c).k Z
```

### 通用实际尾界：固定预算后允许任意外部尾阶

PowerHeightTailBound 使用原定义的量词次序：

源码：[HeckeGeneral/Analysis/PowerHeightComparison.lean](../HeckeGeneral/Analysis/PowerHeightComparison.lean)。命名空间：HeckeGeneral.Analysis。

```lean
def PowerHeightTailBound (E : ℝ → ℝ → ℂ) : Prop :=
  ∃ A R ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∀ N : ℕ, ∃ k Z₀ : ℝ, 0 < k ∧ 1 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        ‖E Z (Z ^ τ)‖ ≤ k * Z ^ R * (1 + Z ^ τ) ^ A * (Z ^ τ) ^ (-(N : ℝ))
```

A、R、ceiling 在 τ 和 N 之前固定；k、Z₀ 可以在 τ、N 之后选取。这一顺序禁止把外部尾阶增加的代价转移到尺度幂 R 或高度多项式次数 A。

实际六项 tail 的通用接口如下；section 测度参数仍是实际局部 Haar、有限 adeles Haar 和原 norm-one Borel 结构：

源码：[Expansion/ActualRecipeTailBounds.lean](../Expansion/ActualRecipeTailBounds.lean)。命名空间：Expansion.Project。

```lean
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

include nu in
theorem actualPhysicalExpansionTail_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e zeta : ℝ}
    (hB0 : 51 / 100 ≤ B) (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000) (hzeta : 0 < zeta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (hmove : PowerHeightTailBound
      (physicalScheduledWholeBoundary K S mu P (arithmeticHighEulerData K Sset P psi)
        omega psi hpsi hB0 hB1 he hboundary g zeta)) :
    PowerHeightTailBound
      (actualPhysicalExpansionTail K S mu P omega psi g hpsi hB0 hB1 hboundary he zeta)
```

hmove 是六项中的完整固定 bin 差分的 PowerHeightTailBound。其余五项使用实际解析估计；通用定理没有 retained 分量目标界或整个 tail 的目标界作为输入。

原边界接口及其实际识别保持为：

源码：[HeckeSkeleton/HighBin.lean](../HeckeSkeleton/HighBin.lean)。命名空间：HeckeSkeleton。

```lean
variable (K : Type) [Field K] [NumberField K]

def wholeBinBoundary (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) : ℂ :=
  ∑ b : HighBlockIndex K c Z T,
    ((∑ u ∈ P.fixedRows Z T b,
      rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
        (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u
        Z (P.contourHeight Z T b) (c.family.B + 20 * P.e)
        (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50)) -
    (∑ u ∈ P.fixedRows Z T b,
      rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
        (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u
        Z (P.contourHeight Z T b)
        ((((targetData K c).expansion Z T).block b).bin + 16 * P.e)
        (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50)))

def HighBoundaryControl (c : TargetContext K) (P : ActualHighPresentation K c) : Prop :=
  PowerHeightTailBound (wholeBinBoundary K c P)
```

源码：[HeckeSkeleton/ExpansionModels/ActualPresentationBoundary.lean](../HeckeSkeleton/ExpansionModels/ActualPresentationBoundary.lean)。命名空间：HeckeSkeleton。

```lean
variable (c : TargetContext K)
local notation "q" => expansionPhysicalParameters K c
local notation "Eactual" => arithmeticHighEulerData K (places K c)
  (probeData K c) (targetCharacter K c)
local notation "X" => expansionRecipeRaw K c

theorem wholeBinBoundary_eq_physicalScheduled (Z H : ℝ)
    (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hH : 1 ≤ H) :
    wholeBinBoundary K c (actualHighPresentation K c) Z H =
      physicalScheduledWholeBoundary K (excludedPlaces K c)
        (Expansion.ActualProbeContext.allLocalMeasures K) (probeData K c) Eactual
        c.family.omega (targetCharacter K c) (representative K c).val.property
        (expansionBoundary_lower K c) c.family.B_upper q.e_pos c.family.boundary
        c.geometry (expansionShellAllowance K c) Z H

theorem physicalScheduledWholeBoundary_tail_of_highBoundaryControl
    (hmove : HighBoundaryControl K c (actualHighPresentation K c)) :
    PowerHeightTailBound
      (physicalScheduledWholeBoundary K (excludedPlaces K c)
        (Expansion.ActualProbeContext.allLocalMeasures K) (probeData K c) Eactual
        c.family.omega (targetCharacter K c) (representative K c).val.property
        (expansionBoundary_lower K c) c.family.B_upper q.e_pos c.family.boundary
        c.geometry (expansionShellAllowance K c))
```

最后的原名 specialization 仅保留同一个 hmove：

源码：[HeckeSkeleton/ExpansionModels/ActualRecipeEstimates.lean](../HeckeSkeleton/ExpansionModels/ActualRecipeEstimates.lean)。命名空间：HeckeSkeleton。

```lean
theorem expansionRecipeRaw_tail (c : TargetContext K)
    (hmove : HighBoundaryControl K c (actualHighPresentation K c)) :
    PowerHeightTailBound (fun Z H => (highExpansion K c Z H).tail)
```

### 通用几何与显式 E：所有模型读取同一个全尺度源

几何是原 recipe 数据的性质，没有把结论作为 raw recipe 的待供应字段。以下谓词固定 R 和 L，再量化全部尺度、active block、振幅标签、t 和见证细分：

源码：[HeckeSkeleton/ExpansionModels/SourceGeometry.lean](../HeckeSkeleton/ExpansionModels/SourceGeometry.lean)。命名空间：HeckeGeneral.Analysis.ExpansionRecipe。

```lean
variable {K : Type} [Field K] [NumberField K]
variable {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
variable {ψ : HeckeCharacter K} {g : PrimeWindowGeometry}
variable {F : RecipeFamily K ψ g}

def RecipeWitnessData.ParameterBox (w : RecipeWitnessData K ψ g F)
    (p : Fin 3 → ℝ) (t T : ℝ) : Prop :=
  ‖w.heights p t T‖ ≤ T ∧
    (∀ I : NonzeroIdeal K, ‖w.realShifts I‖ ≤ 8) ∧
    (∀ I : NonzeroIdeal K, ‖w.imagShifts I‖ ≤ 1 + ‖w.heights p t T‖)

def RecipeAmplitudeData.MomentGeometry (A : RecipeAmplitudeData K S ψ g F)
    (T L : ℝ) : Prop :=
  ∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 → ∀ j : Fin (A.witnessCount t),
    0 ≤ (A.witness t j).inverseLength ∧
    0 ≤ (A.witness t j).plainLength ∧
    (A.witness t j).plainLength ≤ L ∧
    (A.witness t j).ParameterBox A.physical t T

def RecipeExpansion.MomentGeometry {ζ : ℝ}
    (R : RecipeExpansion K S ψ g ζ) (L : ℝ) : Prop :=
  ∀ Z T : ℝ, ∀ b : Fin (R.activeCount Z T), ∀ l : Fin R.labelCount,
    ((R.blocks Z T (R.rawBlockIndex Z T b)).amplitude l).MomentGeometry T L
```

因此 MomentGeometry 22 对原见证给出 inverseLength ≥ 0、0 ≤ plainLength ≤ 22、真实高度范数不超过 T、逐行实位移范数不超过 8，以及逐行虚位移范数不超过 1 + 真实高度范数。没有把 inverseLength ≤ t 加入这个契约。

共享索引和模型类型显式固定同一个 E；它们没有以原始 raw choice 作为默认参数：

源码：[HeckeSkeleton/SourceData.lean](../HeckeSkeleton/SourceData.lean)。命名空间：HeckeSkeleton。

```lean
variable (K : Type) [Field K] [NumberField K]

structure MomentSourceData (c : TargetContext K) : Type 1 where
  expansion : ℝ → ℝ → HighExpansion (FrequencyRow K (places K c)) c.geometry.slots
  rowExponent : ℝ → ℝ

structure SourceMomentIndexFor (c : TargetContext K)
    (E : MomentSourceData K c) (Z T : ℝ) : Type 1 where
  block : Fin (E.expansion Z T).blockCount
  label : ((E.expansion Z T).block block).Label
  t : ℝ
  t_lower : 1 ≤ t
  t_upper : t ≤ 3 / 2
  subdivision : Fin
    ((((E.expansion Z T).block block).amplitudeSet label).subdivisionCount t)
  selected : Finset (Fin c.geometry.slots)

structure SourceMomentModelsFor (c : TargetContext K) (E : MomentSourceData K c) where
  dimension : ℕ
  inverse : ∀ Z T, SourceMomentIndexFor K c E Z T →
    SixthUnitClasses K (places K c) → (Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
      MomentData K c.family.omega (targetCharacter K c)
  paired : ∀ Z T, SourceMomentIndexFor K c E Z T →
    SixthUnitClasses K (places K c) → (Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
      MomentData K c.family.omega (targetCharacter K c)
  unmarked : ℝ → ℝ → SixthUnitClasses K (places K c) →
    (Fin dimension → ℝ) → (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
      MomentData K c.family.omega (targetCharacter K c)
  heights : ∀ Z T, SourceMomentIndexFor K c E Z T → Fin dimension → ℝ
  realShifts : ∀ Z T, SourceMomentIndexFor K c E Z T → NonzeroIdeal K → Fin dimension → ℝ
  imagShifts : ∀ Z T, SourceMomentIndexFor K c E Z T → NonzeroIdeal K → Fin dimension → ℝ
```

任意显式 R 的对应桥保留相同尺度、行包络和原 witness：

源码：[HeckeSkeleton/ExpansionModels/SourceData.lean](../HeckeSkeleton/ExpansionModels/SourceData.lean)。命名空间：HeckeSkeleton。

```lean
variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

def recipeMomentSourceData
    (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c)) : MomentSourceData K c where
  expansion := R.toHigh (P := probeData K c) (R := momentRowCharacters K c)
    (ω := c.family.omega)
  rowExponent := momentRowExponent

variable {K c}
variable {R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c)} {Z T : ℝ}

variable (K c R)

theorem recipeMomentModels_geometry {L : ℝ} (h : R.MomentGeometry L) :
    SourceWitnessLengthBoundFor (recipeMomentSourceData K c R) L ∧
      SourceMomentParameterControlFor (recipeMomentModels K c R)
```

SourceMomentModelsFor 的能量估计不是结构字段；此处的 geometry 桥只把同一个 R 的几何传给该 R 的长度及参数控制。source、模型、calibration 的实例不能分别换成不同的全尺度展开。上述两个 SourceData 模块及新增 ActualRowEligibility leaf 的全量严格声明检查独立于 19 项指定目标检查；本节不将历史 generic 检查通过推断为当前 raw specialization 已通过。

### 量词与审核边界汇总

| 对象或结论 | 先固定 | 后量化或后选择 | 当前源码限制 |
| --- | --- | --- | --- |
| 原 raw recipe / presentation | c、原 probe 与测度、q、family、标签系统和 buffer multiplicity | 所有 Z、T 和实际块 | 不接收最终展开或范数估计作为构造输入 |
| MomentGeometry | 同一个 R、L = 22 | Z、T、active b、每个 label、1 ≤ t ≤ 3/2、每个 subdivision | 包括空行纤维；不是只对最终选中标签 |
| retained 估计 | 原物理背景，C、Z₀、A | 所有 Z ≥ Z₀、H ≥ 1 | exists_actualRetainedEstimates 先固定三项共同常数 |
| ExpansionSource | A、ceiling | 每个允许的 τ，然后 Z₀、k，然后所有 Z、块与源标签 | 同一个公共 cutoff 和同一个 raw recipe |
| PowerHeightTailBound | A、R、ceiling | 每个允许的 τ、任意 N，然后 k、Z₀ 和所有 Z | R、A 不依赖 τ 或 N；EX-TAIL 保留原 hmove |
| 原始严格公理检查 | 19 个完整声明名和标准三公理白名单 | 原生编译后检查每个声明及其依赖 | 当前仅 proof-written, pending native CI；不能标为 passed |

历史核心契约描述的是各个 detector、饱和或局部积分步骤；原始接口部分记录本批对实际数据、全局恒等式、保留分量和 tail 消费者的接线。后续 CI 若要求修改声明，必须重新从对应源码更新本节；本节没有执行或替代 Lean 验证。

### 新追加目标 16–19：同一实际 source 的行资格与 calibration

**这四项是 63fb331 之后新增到 named gate 的目标，状态为 proof-written, pending next native CI；不属于已通过的 pure 组结论。** 总表保留原 15 项顺序，并按脚本顺序追加下列四项。ActualRowEligibility leaf 同时纳入 STRICT_SOURCE_MODULES 的模块全量审计；该文件只导入共享 SourceData、实际行来源及角色排除等依赖，不反向导入 Moments。

#### 目标 16–17：实际行资格 leaf 与实际几何

源码：[HeckeSkeleton/ExpansionModels/ActualRowEligibility.lean](../HeckeSkeleton/ExpansionModels/ActualRowEligibility.lean)。命名空间：HeckeSkeleton。

section 参数、原始对象记号及两个新增声明为：

```lean
variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "Raw" => expansionRecipeRaw K c
local notation "Source" => recipeMomentSourceData K c (expansionRecipeRaw K c)
local notation "Models" => recipeMomentModels K c (expansionRecipeRaw K c)

theorem actualRecipeRowEligibility : SourceRowEligibilityFor Models

theorem actualRecipeSourceGeometry :
    SourceWitnessLengthBoundFor Source 22 ∧ SourceMomentParameterControlFor Models
```

actualRecipeRowEligibility 没有 calibration、行资格或渐近检测结论作为输入。它固定原 c 及其同一个 raw/source/models，然后按 SourceRowEligibilityFor 的原量词，对所有 Z、T、原 source index i 和真实见证行 u 给出以下字段：

- inverse_region 在原 inverseCapacityFor 条件下给出 MIRegion；paired_region 在原 pairedCapacityFor 条件下给出 ExtendedPRegionFor，保留 κ ≤ 1 及不受额外限制的 z = 0 分支。
- inverse_rows、paired_rows 和 unmarked_rows 保留同一实际基理想、sector 及完整 common mask；unmarked_rows 的行范围仍是 2U，并同时提供 SixthPowerFreeIdeal。
- fiber 是原频率行到“基理想、sector”对的单射；geometry 识别两个 marked 模型的总槽长；paired_finite_slots 对所有 sector 和槽给出有限阶。

这里没有“Z 足够大”前提，也没有在 τ 或尾阶之后重新选择行集合。原 source index 已包含原块、原标签、1 ≤ t ≤ 3/2、见证 subdivision 和 selected slots；所有这些索引都受同一个资格结论覆盖，包括复制的 padding 标签及默认 witness。证明源码先从实际严格 dyadic shell 排除单位基理想，再用真实分歧性排除 canonical theta family。

actualRecipeSourceGeometry 同样不增加阈值或新的数据选择。它把 expansionRecipeRaw_geometry 的 L = 22 传给同一个 Source 和 Models；它的两个结论分别展开为：

源码：[HeckeSkeleton/SourceData.lean](../HeckeSkeleton/SourceData.lean)。以下沿用前文显式 E 的 section 参数。

```lean
def SourceWitnessLengthBoundFor (E : MomentSourceData K c) (L : ℝ) : Prop :=
  ∀ Z T (i : SourceMomentIndexFor K c E Z T),
    0 ≤ (momentWitnessFor i).inverseLength ∧
      0 ≤ (momentWitnessFor i).plainLength ∧ (momentWitnessFor i).plainLength ≤ L

def SourceMomentParameterControlFor (M : SourceMomentModelsFor K c E) : Prop :=
  ∀ Z T (i : SourceMomentIndexFor K c E Z T),
    ‖M.heights Z T i‖ ≤ T ∧
      (∀ u, ‖M.realShifts Z T i u‖ ≤ 8) ∧
      (∀ u, ‖M.imagShifts Z T i u‖ ≤ 1 + ‖M.heights Z T i‖)
```

因此该声明覆盖所有 Z、T、i 的非负 inverse/plain 长度、plainLength ≤ 22 及原高度/实位移/虚位移参数盒；它没有增加 inverseLength ≤ t 这样的条件。

#### 目标 18–19：Moments 的原名兼容接口

源码：[HeckeSkeleton/Moments.lean](../HeckeSkeleton/Moments.lean)。命名空间：HeckeSkeleton。

```lean
variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)

theorem moment_polynomial_calibration :
    SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c)

theorem moment_row_eligibility
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c)) :
    SourceRowEligibility (momentModels K c)
```

momentModels 与 actualMomentSourceData 仍分别是 recipeMomentModels K c (expansionRecipeRaw K c) 和 recipeMomentSourceData K c (expansionRecipeRaw K c) 的兼容名字。SourcePolynomialCalibration / SourceRowEligibility 也保持为对应 For 谓词的别名。

moment_polynomial_calibration 的结论按原 SourcePolynomialCalibrationFor 量词，对所有 Z、T、原 index 和相关 sector/见证行，识别实际角色、完整共同掩码、inverse、两个 plain 因子、选中 prime-slot 乘积及 unmarked inverse。它是原始多项式的等式校准，不是能量界或最终矩估计。

moment_row_eligibility 保留原来的 hcal 参数和返回类型；当前实现直接使用 actualRecipeRowEligibility K c。新增 leaf 自身不以 hcal 为前提，也没有把行资格结论反过来当作假设。此追加不宣称 Moments 的 profile uniformity 或其他独立矩估计已经完成。

### 63fb331 的已核实 pure 结果与尚未完成的检查

63fb331c54b3b12b00a5b9a55fc963e30f7a6c93 的 pure 组已成功完成。其 pure-axioms.log 原文为：

```text
EXPANSION audit: 2042 declarations; 0 nonstandard dependencies
```

该运行的 pure-sources.json 包含 112 个源码文件；本次文档更新逐一核对 SHA-256，112/112 与当前工作树完全相同。编译环境记录为 Lean 4.35.0-rc3。

| 证据文件 | SHA-256 |
| --- | --- |
| pure-sources.json | dae3d944b89897dc1e9b75dc28d3800b4e5bb0061377ab8ecc69e3c1b63b75af |
| pure-axioms.log | 585bb43aacca843c3788b566ea08a37a13cf3d4d7e1bf7988e76cce3fc55e267 |

这项通过记录只覆盖该 pure manifest。actual-arithmetic、actual-physical、actual-contours 和 skeleton 四组在本次更新时仍运行；19 项 named gate、三个共享模块的严格检查以及本节新增四项，均不能据此标为通过。新增 leaf 和兼容接线属于待下一批 CI 的工作树变更。
