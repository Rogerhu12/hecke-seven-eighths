import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Complex.Basic

/-!
# Full-sheet unfolding from absolute fundamental-domain pieces

An integrability hypothesis for the full noncompact sheet is unnecessary
once the actual Fourier coefficients already give an absolutely summable
family of integrable orbit pieces.  The fundamental-domain partition
turns precisely those estimates into full-sheet integrability.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalProjectOrbitAbsolute

open MeasureTheory Set
open scoped BigOperators Pointwise

variable {Γ X Y : Type*} [Group Γ] [Countable Γ]
  [MeasurableSpace X] [MeasurableSpace Y] [MulAction Γ X]
  [MeasurableConstSMul Γ X] {μ : Measure X} {ν : Measure Y}
  [SMulInvariantMeasure Γ X μ]

theorem integrable_of_orbit_pieces {Ω : Set X}
    (hΩ : IsFundamentalDomain Γ Ω μ) (g : X → ℂ)
    (hi : ∀ γ : Γ, IntegrableOn (fun x => g (γ • x)) Ω μ)
    (hs : Summable (fun γ : Γ => ∫ x in Ω, ‖g (γ • x)‖ ∂μ)) :
    Integrable g μ := by
  rw [← hΩ.sum_restrict]
  apply integrable_sum_measure
  · intro γ
    exact ((measurePreserving_smul γ μ).integrableOn_image
      (measurableEmbedding_const_smul γ)).mpr (hi γ)
  · apply hs.congr
    intro γ
    exact ((measurePreserving_smul γ μ).setIntegral_image_emb
      (measurableEmbedding_const_smul γ) (fun x => ‖g x‖) Ω).symm

/-- The exact weighted unfolding from the already proved Fourier mass
estimates.  The scalar may vanish: the coefficient is kept inside the
profile, so no division by a possibly zero exterior coefficient occurs. -/
theorem weighted_unfold_of_pieces {Ω : Set X}
    (hΩ : IsFundamentalDomain Γ Ω μ)
    (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (weight : X → ℂ) (targetWeight : Y → ℂ) (f : Y → ℂ) (c : ℂ)
    (hΓ : ∀ (γ : Γ) (x : X), weight (γ • x) = weight x)
    (htransport : ∀ x, weight x = c * targetWeight (e x))
    (hi : ∀ γ : Γ,
      IntegrableOn (fun x => weight x * f (e (γ • x))) Ω μ)
    (hs : Summable (fun γ : Γ =>
      ∫ x in Ω, ‖weight x * f (e (γ • x))‖ ∂μ)) :
    Summable (fun γ : Γ => ∫ x in Ω, weight x * f (e (γ • x)) ∂μ) ∧
      (∑' γ : Γ, ∫ x in Ω, weight x * f (e (γ • x)) ∂μ) =
        c * ∫ y, targetWeight y * f y ∂ν := by
  let g : X → ℂ := fun x => weight x * f (e x)
  have hp (γ : Γ) (x : X) : g (γ • x) = weight x * f (e (γ • x)) := by
    simp only [g, hΓ]
  have hg : Integrable g μ := integrable_of_orbit_pieces hΩ g
    (fun γ => (hi γ).congr (Filter.Eventually.of_forall fun x => (hp γ x).symm))
    (hs.congr fun γ => by simp only [hp])
  refine ⟨?_, ?_⟩
  · apply Summable.of_norm_bounded hs
    intro γ
    exact norm_integral_le_integral_norm _
  · calc
      _ = ∑' γ : Γ, ∫ x in Ω, g (γ • x) ∂μ := by
        apply tsum_congr
        intro γ
        apply integral_congr_ae
        filter_upwards [] with x
        exact (hp γ x).symm
      _ = ∫ x, g x ∂μ := (hΩ.integral_eq_tsum'' g hg).symm
      _ = ∫ x, c * (targetWeight (e x) * f (e x)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [g, htransport x, mul_assoc]
      _ = c * ∫ x, targetWeight (e x) * f (e x) ∂μ := integral_const_mul _ _
      _ = c * ∫ y, targetWeight y * f y ∂ν := by
        rw [he.integral_comp' (fun y => targetWeight y * f y)]

end ThetaGlobal.GlobalProjectOrbitAbsolute

#print axioms ThetaGlobal.GlobalProjectOrbitAbsolute.weighted_unfold_of_pieces
