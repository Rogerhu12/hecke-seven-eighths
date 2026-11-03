import ActualFixedDepthAllScalePoisson
import ActualBalancedJointSupportFourier

/-!
UNCOMPILED / native 0. The literal original chart weight is estimated at any
residue depth chosen before the moving ideals and frequency. This allows the
actual sixth-power choice mask to require a deeper fixed S modulus than 2H.
The depth and clearing order occur before the constants; no periodicity or
mean-zero assertion is assumed. The original CRT theorem supplies mean zero.

No mask is inserted into an orbital test here. The remaining consumer must
prove the actual column mask constant on these finer residue fibers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.Analysis.ActualChosenDepthPoissonDraft

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
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "W" => traceProductSpace K

include Γ in
/-- Fixed residue and clearing depths precede all moving data. -/
theorem exists_uniform_chosenDepth_weight_poisson_bound (depth clearing : ℕ) (A : ℕ) (hA : 2 < A) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (c k : NZ)
      (a₁ a₂ : 𝓞 K ⧸ clearedSModulus K S ζ hζ depth) (d b₁ b₂ : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (F : SchwartzMap (traceProductSpace K) ℂ) (X : ℝ), 0 < X →
      ∀ v : traceProductSpace K,
      ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k depth)
        (fixedChartLatticeWeight K S ζ hζ σ hS6 c k depth clearing a₁ a₂ d b₁ b₂) F X v‖ ≤
      C₀ * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 (𝓕 F) * X ^ 2 *
        (((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) / X) ^ A := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_fixedChartLatticeWeight_bound K S ζ hζ σ hS6 Γ A hA
  obtain ⟨D, hD, hperiod⟩ := exists_fixedChartPeriodIdeal_norm_constant K S ζ hζ depth
  refine ⟨C * D ^ A, mul_pos hC (pow_pos hD _), ?_⟩
  intro c k a₁ a₂ d b₁ b₂ p hpC hpJ F X hX v
  have hbase := hbound c k depth clearing a₁ a₂ d b₁ b₂ p hpC hpJ F X hX v
  let qC : ℝ := Ideal.absNorm (actualFrequencyIdeal K S c)
  let qJ : ℝ := Ideal.absNorm (actualFrequencyIdeal K S k)
  let qI : ℝ := Ideal.absNorm (fixedChartPeriodIdeal K S ζ hζ c k depth).val
  let seminorm : ℝ := SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 (𝓕 F)
  have hquot : qI / X ≤ D * (qC * qJ / X) := by
    calc
      _ ≤ (D * qC * qJ) / X := div_le_div_of_nonneg_right (hperiod c k) hX.le
      _ = _ := by ring
  have hqI : 0 ≤ qI / X := div_nonneg (Nat.cast_nonneg _) hX.le
  have hpow : (qI / X) ^ A ≤ D ^ A * (qC * qJ / X) ^ A := by
    simpa only [mul_pow] using pow_le_pow_left₀ hqI hquot A
  have hfac : 0 ≤ C * qC * seminorm * X ^ 2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg _))
      (apply_nonneg _ _)) (sq_nonneg X)
  change ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k depth)
      (fixedChartLatticeWeight K S ζ hζ σ hS6 c k depth clearing a₁ a₂ d b₁ b₂) F X v‖ ≤
    (C * D ^ A) * qC * seminorm * X ^ 2 * (qC * qJ / X) ^ A
  calc
    _ ≤ C * qC * seminorm * X ^ 2 * (qI / X) ^ A := hbase
    _ ≤ C * qC * seminorm * X ^ 2 * (D ^ A * (qC * qJ / X) ^ A) :=
      mul_le_mul_of_nonneg_left hpow hfac
    _ = _ := by ring

include Γ in
/-- Both all-scale branches concern the same literal lattice sum. -/
theorem exists_uniform_chosenDepth_weight_allScale_min_bound
    (depth clearing : ℕ) (R : ℝ) (hR : 0 < R) (A : ℕ) (hA : 2 < A) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (c k : NZ)
      (a₁ a₂ : 𝓞 K ⧸ clearedSModulus K S ζ hζ depth) (d b₁ b₂ : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (F : SchwartzMap W ℂ) (N : ℝ), 0 < N → F 0 = 0 →
      (∀ x, F x ≠ 0 → ‖x‖ ≤ R) →
      ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k depth)
        (fixedChartLatticeWeight K S ζ hζ σ hS6 c k depth clearing a₁ a₂ d b₁ b₂) F N 0‖ ≤
      C₀ * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        (SchwartzMap.seminorm ℂ 0 0 F +
          SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 (𝓕 F)) * N ^ 2 *
        min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) / N) ^ A) := by
  obtain ⟨Ct, hCt, ht⟩ := exists_productPeriodicSum_allScale_trivial_bound K R hR
  obtain ⟨Cp, hCp, hp⟩ :=
    exists_uniform_chosenDepth_weight_poisson_bound K S Γ ζ hζ σ hS6 depth clearing A hA
  refine ⟨Ct + Cp, add_pos hCt hCp, ?_⟩
  intro c k a₁ a₂ d b₁ b₂ p hpC hpJ F N hN hF0 hFR
  let qC : ℝ := Ideal.absNorm (actualFrequencyIdeal K S c)
  let qJ : ℝ := Ideal.absNorm (actualFrequencyIdeal K S k)
  let s0 : ℝ := SchwartzMap.seminorm ℂ 0 0 F
  let sA : ℝ := SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 (𝓕 F)
  have hqC : 0 ≤ qC := Nat.cast_nonneg _
  have hqJ : 0 ≤ qJ := Nat.cast_nonneg _
  have hs0 : 0 ≤ s0 := apply_nonneg _ _
  have hsA : 0 ≤ sA := apply_nonneg _ _
  have hratio : 0 ≤ (qC * qJ / N) ^ A :=
    pow_nonneg (div_nonneg (mul_nonneg hqC hqJ) hN.le) _
  have hcoefP : Cp * qC * sA ≤ (Ct + Cp) * qC * (s0 + sA) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCt.le) hqC)
      (le_add_of_nonneg_left hs0) hsA (mul_nonneg (add_pos hCt hCp).le hqC)
  have hcoefT : Ct * qC * s0 ≤ (Ct + Cp) * qC * (s0 + sA) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCp.le) hqC)
      (le_add_of_nonneg_right hsA) hs0 (mul_nonneg (add_pos hCt hCp).le hqC)
  have htrivial := ht (fixedChartPeriodIdeal K S ζ hζ c k depth)
    (fixedChartLatticeWeight K S ζ hζ σ hS6 c k depth clearing a₁ a₂ d b₁ b₂)
    F N qC hN hqC
    (norm_fixedChartLatticeWeight_le_absNorm K S ζ hζ σ hS6 c k depth clearing a₁ a₂ d b₁ b₂)
    hF0 hFR
  have hpoisson := hp c k a₁ a₂ d b₁ b₂ p hpC hpJ F N hN 0
  change ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k depth)
    (fixedChartLatticeWeight K S ζ hζ σ hS6 c k depth clearing a₁ a₂ d b₁ b₂) F N 0‖ ≤
    (Ct + Cp) * qC * (s0 + sA) * N ^ 2 * min 1 ((qC * qJ / N) ^ A)
  by_cases hsmall : (qC * qJ / N) ^ A ≤ 1
  · rw [min_eq_right hsmall]
    exact hpoisson.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoefP (sq_nonneg N)) hratio)
  · rw [min_eq_left (le_of_not_ge hsmall), mul_one]
    exact htrivial.trans (mul_le_mul_of_nonneg_right hcoefT (sq_nonneg N))

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Z" => SFiniteLocalGroup K S
variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- The actual balanced profile, with no replacement of its seminorms by
an analytic input. Both fixed depths precede the resulting constants. -/
theorem exists_balancedJoint_chosenDepth_allScale_min_bound (depth clearing : ℕ) (A : ℕ) (hA : 2 < A) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (c k : NZ)
      (a₁ a₂ : 𝓞 K ⧸ clearedSModulus K S ζ hζ depth) (d b₁ b₂ : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ y ∈ sUnitCompactRepresentativeSet K S Γ,
      ∀ (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
        (N : ℝ), 0 < N →
      ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k depth)
        (fixedChartLatticeWeight K S ζ hζ σ hS6 c k depth clearing a₁ a₂ d b₁ b₂)
        (balancedClearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport clearing y ν z₁ z₂ φ R) N 0‖ ≤
      C * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        s.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
          (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν z₁ z₂ φ R) *
        N ^ 2 * min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) / N) ^ A) := by
  obtain ⟨B, hB, hsupp⟩ := exists_balancedJoint_support_radius K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport clearing
  obtain ⟨C₀, hC₀, hb⟩ := exists_uniform_chosenDepth_weight_allScale_min_bound
    K S Γ ζ hζ σ hS6 depth clearing B hB A hA
  obtain ⟨s, D, hD, hd⟩ := exists_balancedJoint_Poisson_seminorm_bound K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport clearing (Module.finrank ℚ K * A)
  refine ⟨s, C₀ * D, mul_pos hC₀ hD, ?_⟩
  intro c k a₁ a₂ d b₁ b₂ p hpC hpJ y hy ν z₁ z₂ φ R N hN
  have hfirst := hb c k a₁ a₂ d b₁ b₂ p hpC hpJ (balancedClearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport clearing y ν z₁ z₂ φ R) N hN
    (balancedJoint_zero K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport clearing y ν z₁ z₂ φ R)
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
end HeckeGeneral.Analysis.ActualChosenDepthPoissonDraft
