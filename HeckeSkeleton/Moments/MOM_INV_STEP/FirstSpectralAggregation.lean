import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorIntegrability
import HeckeSkeleton.Moments.MOM_INV_STEP.NestedMellinBudget

/-!
# Finite source aggregation under the original spectral measure

The first arithmetic sources are summed before their second reconstruction
is bounded. The identities below move exactly that finite sum through the
two original integrals. Their integrability follows from the actual bounded
continuous free energies; no new measure or source multiplicity is inserted.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstSpectralAggregation

open MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FirstCenteredErrorIntegrals FirstErrorIntegrability FirstCommonEnvelope CommonKernel
open scoped Classical BigOperators

theorem spectralAverage_const_mul (ρ : SchwartzMap ℝ ℂ) (m : ℕ)
    (coordinate : LogPlane → ℝ) (c : ℝ) (F : ℝ → ℝ) :
    spectralAverage ρ m coordinate (fun s => c * F s) =
      c * spectralAverage ρ m coordinate F := by
  unfold spectralAverage
  have hi (ξ : LogPlane) :
      (∫ t : ℝ, ‖ρ t‖ * (c * F (t + coordinate ξ))) =
        c * ∫ t : ℝ, ‖ρ t‖ * F (t + coordinate ξ) := by
    simp_rw [mul_left_comm (‖ρ _‖) c]
    exact integral_const_mul _ _
  simp_rw [hi, mul_left_comm (frequencyEnvelope m _) c]
  exact integral_const_mul _ _

theorem spectralAverage_finsetSum {α : Type*} (P : Finset α)
    (ρ : SchwartzMap ℝ ℂ) (m : ℕ) (coordinate : LogPlane → ℝ)
    (hc : Continuous coordinate) (F : α → ℝ → ℝ)
    (hF : ∀ i ∈ P, Continuous (F i)) (hF0 : ∀ i ∈ P, ∀ t, 0 ≤ F i t)
    (B : α → ℝ) (hB : ∀ i ∈ P, ∀ t, F i t ≤ B i) :
    spectralAverage ρ m coordinate (fun s => ∑ i ∈ P, F i s) =
      ∑ i ∈ P, spectralAverage ρ m coordinate (F i) := by
  have hint (i : α) (hi : i ∈ P) :=
    spectral_integrability ρ m coordinate hc (F i) (hF i hi)
      (hF0 i hi) (B i) (hB i hi)
  have hinner (ξ : LogPlane) :
      (∫ t : ℝ, ‖ρ t‖ * ∑ i ∈ P, F i (t + coordinate ξ)) =
        ∑ i ∈ P, ∫ t : ℝ, ‖ρ t‖ * F i (t + coordinate ξ) := by
    simp only [Finset.mul_sum]
    exact integral_finsetSum _ (fun i hi => (hint i hi).1 (coordinate ξ))
  unfold spectralAverage
  simp_rw [hinner, Finset.mul_sum]
  exact integral_finsetSum _ (fun i hi => (hint i hi).2)

/-- Pointwise domination is integrated against the unchanged first
Mellin/Fourier measure. Both dominating terms have their actual
integrability certificates; the lower energy needs only positivity. -/
theorem spectralAverage_le_add
    (ρ : SchwartzMap ℝ ℂ) (m : ℕ) (coordinate : LogPlane → ℝ)
    (F P E : ℝ → ℝ) (hF0 : ∀ t, 0 ≤ F t)
    (hbound : ∀ t, F t ≤ P t + E t)
    (hPi : ∀ v : ℝ, Integrable (fun t : ℝ => ‖ρ t‖ * P (t + v)))
    (hEi : ∀ v : ℝ, Integrable (fun t : ℝ => ‖ρ t‖ * E (t + v)))
    (hPo : Integrable (fun ξ : LogPlane => frequencyEnvelope m ξ *
      ∫ t : ℝ, ‖ρ t‖ * P (t + coordinate ξ)))
    (hEo : Integrable (fun ξ : LogPlane => frequencyEnvelope m ξ *
      ∫ t : ℝ, ‖ρ t‖ * E (t + coordinate ξ))) :
    spectralAverage ρ m coordinate F ≤
      spectralAverage ρ m coordinate P + spectralAverage ρ m coordinate E := by
  have hinner (ξ : LogPlane) :
      (∫ t : ℝ, ‖ρ t‖ * F (t + coordinate ξ)) ≤
        (∫ t : ℝ, ‖ρ t‖ * P (t + coordinate ξ)) +
        (∫ t : ℝ, ‖ρ t‖ * E (t + coordinate ξ)) := by
    have hb := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _) (hF0 _)))
      ((hPi (coordinate ξ)).add (hEi (coordinate ξ)))
      (Filter.Eventually.of_forall (fun t =>
        (mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)).trans_eq (mul_add _ _ _)))
    rwa [integral_add' (hPi (coordinate ξ)) (hEi (coordinate ξ))] at hb
  have hout := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun ξ => mul_nonneg (frequencyEnvelope_nonneg m ξ)
      (integral_nonneg (fun t => mul_nonneg (norm_nonneg _) (hF0 _)))))
    (hPo.add hEo)
    (Filter.Eventually.of_forall (fun ξ =>
      (mul_le_mul_of_nonneg_left (hinner ξ) (frequencyEnvelope_nonneg m ξ)).trans_eq
        (mul_add _ _ _)))
  rw [integral_add' hPo hEo] at hout
  exact hout

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstSpectralAggregation

end
