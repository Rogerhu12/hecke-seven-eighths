# EXPANSION 主定理的源码契约

以下代码块逐字提取当前 `.lean` 文件中对应定理的陈述，不包含证明正文。它们不是额外公理或待 Lean 编译的声明文件。验证状态以 [EXPANSION_REPORT.md](EXPANSION_REPORT.md) 的证据为准；源码中写出证明不表示该版本已经通过编译。

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

实际零点 bin 到原有 WitnessCover 及六维参数盒；完整全局积分、振幅质量与 prime-slot 下界仍是另行义务。实际项目依赖链待完成核验。

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

真实 Hecke 函数在有限零点缓冲内的对数导数界。常数先于字符、尺度、零点边界和评价点选择；没有全高度无零点假设或待证对数导数界作为前提。当前源码待实际项目编译核验；素数窗口的有限矩形积分与尾项仍需另外完成。

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
