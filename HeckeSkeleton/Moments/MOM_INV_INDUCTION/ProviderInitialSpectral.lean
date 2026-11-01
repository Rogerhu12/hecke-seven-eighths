import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialIntegral
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSpectralCost

/-!
# Uniform spectral cost for the original initial profile

The density here is the Mellin transform of the original profile times
its fixed negative half power. Both its Cauchy mass and its polynomial
moment are bounded by a single finite seminorm chosen beforehand. This
is the actual one-pass profile cost; no row-dependent test is inserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialSpectral

open MeasureTheory
open HeckeSkeleton.Moments.MOM_INV_STEP
open CommonKernel FirstCommonEnvelope IteratedFrequencyBudget SecondSpectralCost
open scoped Classical BigOperators

def moment (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (k : ℕ) : ℝ :=
  ∫ t : ℝ, (1 + |t|) ^ k *
    ‖SecondMellinEnergy.mellinDensity (ProviderInitialIntegral.mellinTest W)
      (ProviderInitialIntegral.mellinTest_support W hW) t‖

theorem moment_nonneg (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (k : ℕ) :
    0 ≤ moment W hW k := integral_nonneg fun t => mul_nonneg (by positivity) (norm_nonneg _)

theorem moment_integrable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (k : ℕ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ k *
      ‖SecondMellinEnergy.mellinDensity (ProviderInitialIntegral.mellinTest W)
        (ProviderInitialIntegral.mellinTest_support W hW) t‖) :=
  PositiveIntervalMellin.density_moment_integrable (1 / 8) (21 / 8)
    (by norm_num) (by norm_num) (ProviderInitialIntegral.mellinTest W)
    (ProviderInitialIntegral.mellinTest_support W hW) k

theorem exists_moment_bound (k : ℕ) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2),
      moment W hW k ≤ C * q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, A, hA, ha⟩ := PositiveIntervalMellin.density_moment_bound
    (1 / 8) (21 / 8) (by norm_num) (by norm_num) k
  obtain ⟨q, B, hB, hb⟩ := FinalMellinTests.powerTest_finite_seminorm_bound (-(1 / 2 : ℝ)) s
  refine ⟨q, A * B, mul_nonneg hA hB, ?_⟩
  intro W hW
  exact ((ha (ProviderInitialIntegral.mellinTest W)
    (ProviderInitialIntegral.mellinTest_support W hW)).trans
      (mul_le_mul_of_nonneg_left (hb W) hA)).trans_eq (by ring)

theorem exists_cauchy_moment_bound (k : ℕ) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2),
      moment W hW 0 * moment W hW k ≤
        C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
  obtain ⟨q₀, A₀, hA₀, hb₀⟩ := exists_moment_bound 0
  obtain ⟨q₁, A₁, hA₁, hb₁⟩ := exists_moment_bound k
  refine ⟨q₀ ∪ q₁, A₀ * A₁, mul_nonneg hA₀ hA₁, ?_⟩
  intro W hW
  have h₀ : moment W hW 0 ≤
      A₀ * (q₀ ∪ q₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    (hb₀ W hW).trans (mul_le_mul_of_nonneg_left
    (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W) hA₀)
  have h₁ : moment W hW k ≤
      A₁ * (q₀ ∪ q₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    (hb₁ W hW).trans (mul_le_mul_of_nonneg_left
    (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W) hA₁)
  exact (mul_le_mul h₀ h₁ (moment_nonneg W hW k)
    (mul_nonneg hA₀ (apply_nonneg _ _))).trans_eq (by ring)

theorem joint_polynomial_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (k : ℕ) (B : ℝ)
    (L : LogPlane →L[ℝ] ℝ) :
    Integrable (fun p : LogPlane × ℝ =>
      ProviderInitialIntegral.density W hW k p * polynomialCost k B L p)
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
  have hi := ((weighted_coordinate_integrable L k).mul_prod
    (moment_integrable W hW k)).const_mul B
  convert hi using 1
  funext p
  unfold ProviderInitialIntegral.density polynomialCost
  ring

theorem joint_polynomial_integral (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (k : ℕ) (B : ℝ)
    (L : LogPlane →L[ℝ] ℝ) :
    (∫ p : LogPlane × ℝ, ProviderInitialIntegral.density W hW k p * polynomialCost k B L p
      ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))) =
      B * coordinateMoment k L * moment W hW k := by
  calc
    _ = ∫ p : LogPlane × ℝ, B *
        ((frequencyEnvelope k p.1 * (1 + |L p.1|) ^ k) *
          ((1 + |p.2|) ^ k *
            ‖SecondMellinEnergy.mellinDensity (ProviderInitialIntegral.mellinTest W)
              (ProviderInitialIntegral.mellinTest_support W hW) p.2‖))
          ∂((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
      apply integral_congr_ae
      filter_upwards [] with p
      unfold ProviderInitialIntegral.density polynomialCost
      ring
    _ = _ := by
      rw [integral_const_mul,
        integral_prod_mul (fun xi : LogPlane => frequencyEnvelope k xi * (1 + |L xi|) ^ k)
          (fun t : ℝ => (1 + |t|) ^ k *
            ‖SecondMellinEnergy.mellinDensity (ProviderInitialIntegral.mellinTest W)
              (ProviderInitialIntegral.mellinTest_support W hW) t‖)]
      unfold coordinateMoment moment
      ring

/-- One common decay degree pays the finite child seminorm for both
original Cauchy branches, followed by one original-profile seminorm. -/
theorem exists_uniform_spectral_cost (s : Finset (ℕ × ℕ)) :
    ∃ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∃ q : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      (∀ (side : Bool) (p : LogPlane × ℝ),
        (s.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (FinalMellinTests.weightedTest 0 (p.2 + SecondParentProduction.coordinate side p.1))) ^ 2 ≤
            polynomialCost k B (SecondParentProduction.coordinate side) p) ∧
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (side : Bool),
        SecondMellinEnergy.mellinMass (ProviderInitialIntegral.mellinTest W)
          (ProviderInitialIntegral.mellinTest_support W hW) *
          (∫ p : LogPlane × ℝ, ProviderInitialIntegral.density W hW k p *
            polynomialCost k B (SecondParentProduction.coordinate side) p
            ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))) ≤
        A * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
  obtain ⟨k, B, hB, hb⟩ := SecondSpectralCost.exists_seminorm_majorant s
  obtain ⟨q, C, hC, hc⟩ := exists_cauchy_moment_bound k
  let M := coordinateMoment k (SecondParentProduction.coordinate false) +
    coordinateMoment k (SecondParentProduction.coordinate true)
  have hM : 0 ≤ M := add_nonneg (coordinateMoment_nonneg _ _) (coordinateMoment_nonneg _ _)
  refine ⟨k, B, hB, q, B * M * C, mul_nonneg (mul_nonneg hB hM) hC,
    fun side p => hb _ p, ?_⟩
  intro W hW side
  have hside : coordinateMoment k (SecondParentProduction.coordinate side) ≤ M := by
    cases side
    · exact le_add_of_nonneg_right (coordinateMoment_nonneg _ _)
    · exact le_add_of_nonneg_left (coordinateMoment_nonneg _ _)
  have hmass : SecondMellinEnergy.mellinMass (ProviderInitialIntegral.mellinTest W)
      (ProviderInitialIntegral.mellinTest_support W hW) = moment W hW 0 := by
    simp only [SecondMellinEnergy.mellinMass, moment, pow_zero, one_mul]
  rw [hmass, joint_polynomial_integral]
  calc
    _ = (B * coordinateMoment k (SecondParentProduction.coordinate side)) *
        (moment W hW 0 * moment W hW k) := by ring
    _ ≤ (B * M) * (C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hside hB) (hc W hW)
        (mul_nonneg (moment_nonneg _ _ _) (moment_nonneg _ _ _)) (mul_nonneg hB hM)
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialSpectral

end
