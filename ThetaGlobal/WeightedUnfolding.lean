import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Complex.Basic

/-!
# Weighted orbit unfolding with the actual change of sheet

The character and class mask are retained inside the integrand.  The
measure-preserving map may be multiplication by a frequency (direct
unfolding) or frequency divided by the sheet variable (reflected unfolding).
The hypotheses concern only the group action, sheet measures, and one
integrable local Whittaker profile.  No theta reflection identity is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.WeightedUnfolding

open MeasureTheory Set
open scoped BigOperators Pointwise

variable {Γ X Y : Type*} [Group Γ] [Countable Γ]
  [MeasurableSpace X] [MeasurableSpace Y] [MulAction Γ X]
  [MeasurableConstSMul Γ X] {μ : Measure X} {ν : Measure Y}
  [SMulInvariantMeasure Γ X μ]

/-- Integral norms of the orbit pieces form a convergent series. -/
theorem orbit_integrals_norm_summable {Ω : Set X}
    (hΩ : IsFundamentalDomain Γ Ω μ) (g : X → ℂ)
    (hg : Integrable g μ) :
    Summable (fun γ : Γ => ∫ x in Ω, ‖g (γ • x)‖ ∂μ) := by
  have hsum : Integrable g (Measure.sum fun γ : Γ => μ.restrict (γ • Ω)) := by
    rw [hΩ.sum_restrict]
    exact hg
  have hs := hsum.summable_integral
  apply hs.congr
  intro γ
  exact (measurePreserving_smul γ μ).setIntegral_image_emb
    (measurableEmbedding_const_smul γ) (fun x => ‖g x‖) Ω

/-- Absolute convergence of the complex orbit-integral series. -/
theorem orbit_integrals_summable {Ω : Set X}
    (hΩ : IsFundamentalDomain Γ Ω μ) (g : X → ℂ)
    (hg : Integrable g μ) :
    Summable (fun γ : Γ => ∫ x in Ω, g (γ • x) ∂μ) := by
  apply Summable.of_norm_bounded (orbit_integrals_norm_summable hΩ g hg)
  intro γ
  exact norm_integral_le_integral_norm _

/-- The exact weighted formula, including absolute convergence.  A finite
power-class indicator can be multiplied into `weight` without any change. -/
theorem weighted_orbit_unfolding {Ω : Set X}
    (hΩ : IsFundamentalDomain Γ Ω μ)
    (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (weight : X → ℂ) (targetWeight : Y → ℂ) (f : Y → ℂ) (c : ℂ)
    (hΓ : ∀ (γ : Γ) (x : X), weight (γ • x) = weight x)
    (htransport : ∀ x, weight x = c * targetWeight (e x))
    (hf : Integrable (fun y => targetWeight y * f y) ν) :
    Summable (fun γ : Γ => ∫ x in Ω, weight x * f (e (γ • x)) ∂μ) ∧
      (∑' γ : Γ, ∫ x in Ω, weight x * f (e (γ • x)) ∂μ) =
        c * ∫ y, targetWeight y * f y ∂ν := by
  let g : X → ℂ := fun x => weight x * f (e x)
  have hg : Integrable g μ := by
    have hi := he.integrable_comp_of_integrable (hf.const_mul c)
    apply hi.congr
    filter_upwards [] with x
    simp only [g, Function.comp_apply, htransport x, mul_assoc]
  have hpiece (γ : Γ) :
      (∫ x in Ω, g (γ • x) ∂μ) =
        ∫ x in Ω, weight x * f (e (γ • x)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [g, hΓ]
  constructor
  · exact (orbit_integrals_summable hΩ g hg).congr hpiece
  · calc
      _ = ∑' γ : Γ, ∫ x in Ω, g (γ • x) ∂μ :=
        tsum_congr fun γ => (hpiece γ).symm
      _ = ∫ x, g x ∂μ := (hΩ.integral_eq_tsum'' g hg).symm
      _ = ∫ x, c * (targetWeight (e x) * f (e x)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [g, htransport x, mul_assoc]
      _ = c * ∫ x, targetWeight (e x) * f (e x) ∂μ := integral_const_mul _ _
      _ = c * ∫ y, targetWeight y * f y ∂ν := by
        rw [he.integral_comp' (fun y => targetWeight y * f y)]

/-- Absolute orbit unfolding remains valid after multiplication by a bounded
unitary weight.  This is the estimate needed before signed rearrangement. -/
theorem integrable_weight_mul (w f : Y → ℂ)
    (hw : AEStronglyMeasurable w ν) (hf : Integrable f ν)
    (hw_bound : ∀ᵐ y ∂ν, ‖w y‖ ≤ 1) :
    Integrable (fun y => w y * f y) ν := by
  apply Integrable.mono' hf.norm (hw.mul hf.aestronglyMeasurable)
  filter_upwards [hw_bound] with y hy
  change ‖w y * f y‖ ≤ ‖f y‖
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hy (norm_nonneg _)).trans_eq (one_mul _)

end ThetaGlobal.WeightedUnfolding

#print axioms ThetaGlobal.WeightedUnfolding.weighted_orbit_unfolding
