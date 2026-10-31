import ActualBalancedJointSupportFourier

/-!
UNCOMPILED / native 0. Uniform balanced-profile version of the same
zero-translated periodic sum, with fixed clearing depth H+H. The unsplit
original joint seminorms are retained, not replaced by estimate hypotheses.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HeckeGeneral.Analysis.ActualBalancedJointAllScaleDraft
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open AlgebraicNumberTheory.PowerResidueSymbols
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramCoefficientBoundDraft ActualGramPeriodNormDraft
open ActualMeanZeroProductPoissonDraft ActualFixedDepthAllScaleDraft
open ActualBalancedClearedJointDraft ActualBalancedJointSupportFourierDraft
open scoped Classical BigOperators ContDiff FourierTransform nonZeroDivisors
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "G" => sLocalMultiplicativeGroup K S
local notation "Z" => SFiniteLocalGroup K S
variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "H" => finiteIndexSUnitBoxWidth K S Γ
local notation "N₀" => H + H
local notation:max "F" y:max ν:max z₁:max z₂:max φ:max R:max =>
  balancedClearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport H y ν z₁ z₂ φ R

/-- The constant and finite seminorm set precede all moving ideals, chart
centers, compact divisor coordinates, frequency, finite fibers and scales.
In cleared-divisor transport N here is the already balanced N/q_d. -/
theorem exists_balancedJoint_fixedDepth_allScale_min_bound (A : ℕ) (hA : 2 < A) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (c k : NZ)
      (a₁ a₂ : 𝓞 K ⧸ clearedSModulus K S ζ hζ N₀) (d b₁ b₂ : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ y ∈ sUnitCompactRepresentativeSet K S Γ,
      ∀ (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
        (N : ℝ), 0 < N →
      ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k N₀)
        (fixedChartLatticeWeight K S ζ hζ σ hS6 c k N₀ H a₁ a₂ d b₁ b₂)
        (F y ν z₁ z₂ φ R) N 0‖ ≤
      C * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        s.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
          (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν z₁ z₂ φ R) *
        N ^ 2 * min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) / N) ^ A) := by
  obtain ⟨B, hB, hsupp⟩ := exists_balancedJoint_support_radius K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport H
  obtain ⟨C₀, hC₀, hb⟩ := exists_uniform_fixedDepth_weight_allScale_min_bound
    K S Γ ζ hζ σ hS6 B hB A hA
  obtain ⟨s, D, hD, hd⟩ := exists_balancedJoint_Poisson_seminorm_bound K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport H (Module.finrank ℚ K * A)
  refine ⟨s, C₀ * D, mul_pos hC₀ hD, ?_⟩
  intro c k a₁ a₂ d b₁ b₂ p hpC hpJ y hy ν z₁ z₂ φ R N hN
  have hfirst := hb c k a₁ a₂ d b₁ b₂ p hpC hpJ (F y ν z₁ z₂ φ R) N hN
    (balancedJoint_zero K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport H y ν z₁ z₂ φ R)
    (hsupp y hy ν z₁ z₂ φ R)
  have hsemi := hd y hy ν z₁ z₂ φ R
  have hqC : 0 ≤ (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) := Nat.cast_nonneg _
  have hqJ : 0 ≤ (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ) := Nat.cast_nonneg _
  have hmin : 0 ≤ min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
      (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) / N) ^ A) := by positivity
  calc
    _ ≤ _ := hfirst
    _ ≤ C₀ * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        (D * s.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
          (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν z₁ z₂ φ R)) *
        N ^ 2 * min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) / N) ^ A) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsemi (mul_nonneg hC₀.le hqC)) (sq_nonneg N)) hmin
    _ = _ := by ring
end HeckeGeneral.Analysis.ActualBalancedJointAllScaleDraft
