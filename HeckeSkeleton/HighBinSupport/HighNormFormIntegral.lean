import HeckeSkeleton.HighBinSupport.HighNormFormScalar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-!
From dominated actual kernels to the required sum of absolute row pieces.
The row set is fixed throughout integration.  Absolute integrability is
proved from measurability and a genuine integrable majorant; no conclusion
uses the zero default of a nonintegrable Bochner integral.
-/

noncomputable section
namespace HighBinVerified.NormForm
open MeasureTheory
open scoped BigOperators

/-- An envelope bound proves absolute integrability and the L1 estimate. -/
theorem integral_bound_of_envelope {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (envelope : X → ℝ) (M : ℝ)
    (hmeas : AEStronglyMeasurable f μ) (henv : Integrable envelope μ)
    (hpoint : ∀ᵐ x ∂μ, ‖f x‖ ≤ M * envelope x) :
    Integrable f μ ∧ ‖∫ x, f x ∂μ‖ ≤ M * ∫ x, envelope x ∂μ := by
  have hdom : Integrable (fun x => M * envelope x) μ := henv.const_mul M
  refine ⟨hdom.mono' hmeas hpoint, ?_⟩
  simpa only [integral_const_mul] using norm_integral_le_of_norm_le hdom hpoint

/-- This is the exact absolute-row-sum shape of HB-NORMFORM.  It does not
assume a row count or a high-bin bound. -/
theorem sum_norm_integral_le {X Row : Type*} [MeasurableSpace X]
    (μ : Measure X) (rows : Finset Row) (f : Row → X → ℂ)
    (envelope : X → ℝ) (M : ℝ)
    (hmeas : ∀ u ∈ rows, AEStronglyMeasurable (f u) μ)
    (henv : Integrable envelope μ)
    (hpoint : ∀ u ∈ rows, ∀ᵐ x ∂μ, ‖f u x‖ ≤ M * envelope x) :
    (∀ u ∈ rows, Integrable (f u) μ) ∧
      (∑ u ∈ rows, ‖∫ x, f u x ∂μ‖) ≤
        (rows.card : ℝ) * M * ∫ x, envelope x ∂μ := by
  have hh : ∀ u ∈ rows, Integrable (f u) μ ∧
      ‖∫ x, f u x ∂μ‖ ≤ M * ∫ x, envelope x ∂μ :=
    fun u hu => integral_bound_of_envelope μ (f u) envelope M (hmeas u hu) henv (hpoint u hu)
  refine ⟨fun u hu => (hh u hu).1, ?_⟩
  calc
    _ ≤ ∑ _u ∈ rows, M * ∫ x, envelope x ∂μ :=
      Finset.sum_le_sum (fun u hu => (hh u hu).2)
    _ = _ := by simp [mul_assoc]

/-- A uniform pointwise norm form plus the actual profile envelope gives
exactly the desired lambda/4 integral loss.  The profile integral may
carry any fixed polynomial height cost, chosen before Z and T. -/
theorem sum_integral_normForm {X Row : Type*} [MeasurableSpace X]
    (μ : Measure X) (rows : Finset Row) (f : Row → X → ℂ)
    (envelope : X → ℝ) (Z T C Cenv A d a q loss lam : ℝ)
    (hZ : 1 ≤ Z) (hT : 1 ≤ T) (hC : 0 ≤ C) (hCenv : 0 ≤ Cenv)
    (hloss : loss ≤ lam / 4)
    (hmeas : ∀ u ∈ rows, AEStronglyMeasurable (f u) μ)
    (henv : Integrable envelope μ)
    (henvbound : (∫ x, envelope x ∂μ) ≤ Cenv * (1 + T) ^ A)
    (hpoint : ∀ u ∈ rows, ∀ᵐ x ∂μ,
      ‖f u x‖ ≤ C * Z ^ (rowExponent d a q + loss) * envelope x) :
    (∀ u ∈ rows, Integrable (f u) μ) ∧
      (∑ u ∈ rows, ‖∫ x, f u x ∂μ‖) ≤
        (C * Cenv) * (rows.card : ℝ) *
          Z ^ (3 / 16 + moderateExponent d (2 * a - 1) q 0 + lam / 4) *
            (1 + T) ^ A := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hh := sum_norm_integral_le μ rows f envelope
    (C * Z ^ (rowExponent d a q + loss)) hmeas henv hpoint
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hpower : Z ^ (rowExponent d a q + loss) ≤
      Z ^ (rowExponent d a q + lam / 4) :=
    Real.rpow_le_rpow_of_exponent_le hZ (add_le_add le_rfl hloss)
  calc
    (rows.card : ℝ) * (C * Z ^ (rowExponent d a q + loss)) * (∫ x, envelope x ∂μ) ≤
        (rows.card : ℝ) * (C * Z ^ (rowExponent d a q + loss)) *
          (Cenv * (1 + T) ^ A) :=
      mul_le_mul_of_nonneg_left henvbound (by positivity)
    _ = (C * Cenv) * (rows.card : ℝ) * Z ^ (rowExponent d a q + loss) * (1 + T) ^ A := by ring
    _ ≤ (C * Cenv) * (rows.card : ℝ) * Z ^ (rowExponent d a q + lam / 4) * (1 + T) ^ A := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
      exact mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by rw [rowExponent_eq_moderate]

/-- Finite integration and summation are interchangeable once the preceding
majorant has supplied genuine integrability. -/
theorem integral_sum_eq_sum_integral {X Row : Type*} [MeasurableSpace X]
    (μ : Measure X) (rows : Finset Row) (f : Row → X → ℂ)
    (h : ∀ u ∈ rows, Integrable (f u) μ) :
    (∫ x, ∑ u ∈ rows, f u x ∂μ) = ∑ u ∈ rows, ∫ x, f u x ∂μ :=
  integral_finsetSum rows h

end HighBinVerified.NormForm

#print axioms HighBinVerified.NormForm.integral_bound_of_envelope
#print axioms HighBinVerified.NormForm.sum_norm_integral_le
#print axioms HighBinVerified.NormForm.sum_integral_normForm
