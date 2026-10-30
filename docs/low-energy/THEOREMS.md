# 主要定理的精确声明

以下声明逐字摘自本提交的 Lean 源码，省略证明体，不省略声明中的假设或量词。
每段另列其 section 变量/局部记号；符号的实际定义和 namespace opens 由链接源码给出。
声明存在与编译通过是两件事，状态见 STATUS 和 source_manifest。

## `completedMarkedEnergy`

[源码](../../HeckeSkeleton/Principal.lean)

**环境：** namespace HeckeSkeleton; (K : Type) [Field K] [NumberField K]; (c : TargetContext K).
S := places K c; P := probeData K c; ψ := targetCharacter K c.

```lean
theorem completedMarkedEnergy
    {F : FiniteMellinData K S}
    (hreflection : MarkedCoefficientReflectionInput K S (probeData K c).arithmetic
      F (thetaPeriod K S P ψ))
    (hquadratic : QuadraticSieveBound K c)
    (hcubic : CubicSieveBound K c) : CompletedMarkedEnergy K c
```

## `completedMarkedEnergy`

[源码](../../HeckeSkeleton/LowEnergy/ActualCompletedMarkedEnergy.lean)

**环境：** namespace HeckeSkeleton.LowEnergy.ActualCompletedMarkedEnergy; (K : Type) [Field K] [NumberField K]; (c : HeckeSkeleton.TargetContext K).
Sc := places K c; Pc := probeData K c; ψc := targetCharacter K c; θc := thetaPeriod K Sc Pc ψc.

```lean
theorem completedMarkedEnergy
    (F : FiniteMellinData K Sc)
    (hreflection : MarkedCoefficientReflectionInput K Sc Pc.arithmetic F θc)
    (hquadratic : HeckeSkeleton.QuadraticSieveBound K c)
    (hcubic : HeckeSkeleton.CubicSieveBound K c) :
    HeckeSkeleton.LowCauchy.CompletedMarkedEnergy K c
```

## `actual_finite_complete_ideal_energy`

[源码](../../HeckeSkeleton/LowEnergy/ActualCompleteIdealEnergy.lean)

**环境：** namespace HeckeSkeleton.LowEnergy.ActualCompleteIdealEnergy; 同上 K, c, Sc, Pc, ψc, θc；gc := c.geometry; Tc := rayFilter K c.

```lean
theorem actual_finite_complete_ideal_energy [Finite (SixthLocalClasses K Sc)]
    (F : FiniteMellinData K Sc)
    (hreflection : MarkedCoefficientReflectionInput K Sc Pc.arithmetic F θc)
    (hquadratic : ExteriorQuadraticBound K Sc Pc.arithmetic)
    (hcubic : ExteriorCubicBound K Sc Pc.arithmetic)
    (B eps : ℝ) (hB : 0 < B) (heps : 0 < eps) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z : ℝ, Z0 ≤ Z →
      ∀ p ∈ Fintype.piFinset (fun i => primeWindow K Sc gc Tc Z i),
      ∀ (J : Finset (Fin gc.slots)) (ξ : SixthUnitClasses K Sc)
        (R : Finset (ExteriorIdeal K Sc)),
      (∀ I ∈ R, exteriorNorm K Sc I ≤
        B * Z ^ (5 / 6 : ℝ) / exteriorNorm K Sc (subsetPrimeIdeal K Sc p J) ^ 2) →
      (∑ I ∈ R, ‖HeckeSkeleton.LowCauchy.completedMarkedRow K c Z p J
        (idealSectorElement K Sc Pc.arithmetic (I, ξ))‖ ^ 2) ≤
        C * Z ^ ((5 / 6 : ℝ) + eps) /
          exteriorNorm K Sc (subsetPrimeIdeal K Sc p J) ^ 2
```

## `actual_marked_tuple_energy`

[源码](../../HeckeSkeleton/LowEnergy/ActualMarkedTupleEnergy.lean)

**环境：** namespace HeckeSkeleton.LowEnergy.ActualMarkedTupleEnergy; (K : Type) [Field K] [NumberField K];
(S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]; (D : ThetaArithmeticData K S).

```lean
theorem actual_marked_tuple_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (g : PrimeWindowGeometry) (delta eps C0 rho : ℝ)
    (hdelta : 0 < delta) (hdelta' : delta ≤ 1) (heps : 0 < eps)
    (hC0 : 0 ≤ C0) (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : HeckeCharacter K) (T : Finset (HeckeCharacter K))
      (frozen : ExteriorIdeal K S) (u : S.unit K) (Z Klo q Ccut : ℝ),
      1 < Z → 1 ≤ Klo → 0 < q → 0 < Ccut →
      IdealRows.Powerful frozen.val → Real.log Ccut ≤ C0 →
      Real.log ((2 : ℝ) ^ g.slots) ≤ C0 →
      ∀ J : Finset (Fin g.slots),
      Z ^ ((J.card : ℝ) / (6 * g.slots)) ≤ q →
      exteriorNorm K S frozen * Klo ≤ Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2 →
      ∀ rows : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, IsExterior K S k ∧ Squarefree k ∧ (k.absNorm : ℝ) ≤ 2 * Klo) →
      (∀ k ∈ rows, 1 ≤ safeNorm k / Klo ∧ safeNorm k / Klo ≤ 2) →
      (∑ k ∈ rows, ‖markedFrozenRow K S D frozen u F θ ψ g T Z J k‖ ^ 2) ≤
        C * exteriorNorm K S frozen ^ (-(1 / 2 : ℝ) + rho) *
          Z ^ ((5 / 6 : ℝ) - 2 * ((J.card : ℝ) / (6 * g.slots)) +
            23 * delta + 2 * eps)
```

## `raw_ideal_hybrid_energy`

[源码](../../HeckeSkeleton/LowEnergy/RawIdealHybrid.lean)

**环境：** namespace HeckeSkeleton.LowEnergy.RawIdealHybrid; {K : Type} [Field K] [NumberField K].

```lean
theorem raw_ideal_hybrid_energy
    (hext_ne : ∀ I, Ext I → I ≠ ⊥)
    (hext_mul : ∀ I J, Ext I → Ext J → Ext (I * J))
    (hext_dvd : ∀ I J, Ext I → J ∣ I → Ext J)
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hκ : CubicKernelAxioms Ext cubic)
    (hsquare : ∀ k c m h t, Ext k → Ext c → Ext t →
      quad k ((c * m) * ((c * h) * t ^ 2)) = mask k (c * t) * quad k (m * h))
    (hquadratic : IdealQuadraticInput Ext quad)
    (hcubic : IdealCubicInput Ext cubic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K0 N0 B0 L0 : ℝ,
      1 ≤ K0 → 1 ≤ N0 → 1 ≤ B0 → 1 ≤ L0 →
      ∀ rows nset bset ps : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, Ext k ∧ Squarefree k ∧ (Ideal.absNorm k : ℝ) ≤ K0) →
      (∀ n ∈ nset, Ext n ∧ Squarefree n ∧ (Ideal.absNorm n : ℝ) ≤ N0) →
      (∀ b ∈ bset, Ext b ∧ (Ideal.absNorm b : ℝ) ≤ B0) →
      (∀ P ∈ ps, Ext P ∧ Squarefree P ∧ (Ideal.absNorm P : ℝ) ≤ L0) →
      ∀ a : Ideal (𝓞 K) → ℂ, ∀ beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ,
      (∀ P ∈ ps, ‖a P‖ ≤ 1) →
      (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖hybridRow cubic quad ps nset bset a beta k‖ ^ 2) ≤
        C * (K0 * N0 * B0 * L0) ^ eps * (K0 + N0 * B0) * B0 *
          (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ))
```

## `integrated_hybrid_energy`

[源码](../../HeckeSkeleton/LowEnergy/MellinHybrid.lean)

**环境：** namespace HeckeSkeleton.LowEnergy.MellinHybrid; {K : Type} [Field K] [NumberField K]; 其余形参均列于下方。

```lean
theorem integrated_hybrid_energy
    (Ext : Ideal (𝓞 K) → Prop)
    (hext_ne : ∀ I, Ext I → I ≠ ⊥)
    (hext_mul : ∀ I J, Ext I → Ext J → Ext (I * J))
    (hext_dvd : ∀ I J, Ext I → J ∣ I → Ext J)
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hκ : CubicKernelAxioms Ext cubic)
    (hsquare : ∀ k c m h t, Ext k → Ext c → Ext t →
      quad k ((c * m) * ((c * h) * t ^ 2)) = mask k (c * t) * quad k (m * h))
    (hquadratic : IdealQuadraticInput Ext quad)
    (hcubic : IdealCubicInput Ext cubic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K0 N0 B0 L0 : ℝ,
      1 ≤ K0 → 1 ≤ N0 → 1 ≤ B0 → 1 ≤ L0 →
      ∀ rows ns bs ps : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, Ext k ∧ Squarefree k ∧ (Ideal.absNorm k : ℝ) ≤ K0) →
      (∀ n ∈ ns, Ext n ∧ Squarefree n ∧ (Ideal.absNorm n : ℝ) ≤ N0) →
      (∀ b ∈ bs, Ext b ∧ (Ideal.absNorm b : ℝ) ≤ B0) →
      (∀ P ∈ ps, Ext P ∧ Squarefree P ∧ (Ideal.absNorm P : ℝ) ≤ L0) →
      ∀ (rho : ℝ → ℂ) (a r : ℝ → Ideal (𝓞 K) → ℂ)
        (beta : ℝ → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ),
      Continuous rho → Integrable (fun t => ‖rho t‖) →
      (∀ P, Continuous (fun t => a t P)) →
      (∀ k, Continuous (fun t => r t k)) →
      (∀ n b, Continuous (fun t => beta t n b)) →
      ∀ A B R s : ℝ, 0 < A → 0 < B → 0 ≤ R →
      (∀ t P, P ∈ ps → ‖a t P‖ ≤ A) →
      (∀ t n, n ∈ ns → ∀ b, b ∈ bs → ‖beta t n b‖ ≤ B) →
      (∀ t k, k ∈ rows → ‖r t k‖ ≤ R) →
      (∑ k ∈ rows, ‖(s : ℂ) * ∫ t : ℝ,
        rho t * (r t k * hybridRow cubic quad ps ns bs (a t) (beta t) k)‖ ^ 2) ≤
        s ^ 2 * (∫ t : ℝ, ‖rho t‖) ^ 2 * (R * A * B) ^ 2 *
          C * (K0 * N0 * B0 * L0) ^ eps * (K0 + N0 * B0) * B0 *
          (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ))
```

## `physical_low_polynomial`

[源码](../../HeckeSkeleton/LowEnergy/PhysicalBlockPolynomial.lean)

**环境：** namespace HeckeSkeleton.LowEnergy.PhysicalBlockPolynomial; 所有参数已显式列在下方。

```lean
theorem physical_low_polynomial
    {Z shift inactive active linear cube small K L N B Cf delta F q d eta Ccut Cwin : ℝ}
    (hZ : 1 < Z) (hi : 1 ≤ inactive) (ha : 1 ≤ active)
    (hn : 1 ≤ linear) (hb : 1 ≤ cube) (hs : 1 ≤ small)
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hF : 1 ≤ F) (hq : 0 < q) (hCcut : 0 < Ccut) (hCwin : 0 < Cwin)
    (hd : 0 ≤ d) (hd' : d ≤ (1 / 6 : ℝ))
    (hdelta : 0 ≤ delta) (hdelta' : delta ≤ 1) (heta : 0 ≤ eta)
    (hcharge : Cf ^ 2 ≤ (small * cube)⁻¹)
    (hconductor : active ^ 2 ≤ F) (hlinear : linear ≤ active)
    (hselected : Z ^ d ≤ q)
    (hrow : F * K ≤ Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2)
    (hwindow : inactive * L ≤ Cwin * Z ^ ((1 / 6 : ℝ) - d))
    (hcuterr : scale Z Ccut ≤ eta) (hwinerr : scale Z Cwin ≤ eta)
    (hshift : |shift / Real.log Z| ≤ eta) :
    (Cf ^ 2 / (N * B ^ 2)) *
        sievePolynomial (2 * K) (2 * N) (2 * B) (2 * L) delta *
        scalar (physicalScale Z shift inactive active linear cube K L N B) ^ 2 ≤
      3072 * F ^ (-1 / 2 : ℝ) *
        Z ^ ((5 / 6 : ℝ) - 2 * d + 2 * delta + 21 * eta -
          2 * max (scale Z N + 3 * scale Z B -
            threshold Z shift inactive active linear cube K L) 0)
```

## `powerful_shell_aggregation_at_scale`

[源码](../../HeckeSkeleton/LowEnergy/PowerfulRowAssembly.lean)

**环境：** namespace HeckeSkeleton.LowEnergy.PowerfulRowAssembly; (K : Type) [Field K] [NumberField K].

```lean
theorem powerful_shell_aggregation_at_scale (L eps C0 : ℝ)
    (hL : 0 ≤ L) (heps : 0 < eps) (hC0 : 0 < C0) :
    let delta := eps / (4 * (L + 1))
    ∃ C : ℝ, 0 < C ∧ ∀ {Row : Type*} (R : Finset Row)
      (I : Row → (Ideal (𝓞 K))⁰) (shell : Row → ℕ) (E : Row → ℝ)
      (N : ℕ) (Z B : ℝ),
      1 ≤ Z → 0 ≤ B → (∀ r ∈ R, idealNorm K (I r) ≤ Z ^ L) →
      (∀ r ∈ R, shell r < N) →
      ((N : ℝ) ≤ C0 * (1 + Real.log Z) ^ 2) →
      (∀ A ∈ R.image (fun r => powerfulPart (I r)), ∀ j ∈ Finset.range N,
        (∑ r ∈ R.filter (fun r => powerfulPart (I r) = A ∧ shell r = j), E r) ≤
          B * idealNorm K A ^ (-(1 / 2 : ℝ) + delta)) →
      (∑ r ∈ R, E r) ≤ C * B * Z ^ eps
```
