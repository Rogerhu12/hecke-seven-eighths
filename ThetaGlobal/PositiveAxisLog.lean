import ThetaGlobal.ScalarMellinConvolution
import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PositiveAxisSheetDisintegration
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Exact logarithmic coordinates for the stored positive Haar measure

The normalization is proved from the literal density `dt / t`.
Consequently the positive-spectrum Fourier transform is the actual
imaginary-axis Mellin transform, without a hidden Haar scalar.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.PositiveAxisLog

open MeasureTheory DedekindZetaZeroFree.ThetaProfileHaarSheets
open scoped Topology

def logEquiv : PositiveAxis ≃ₜ ℝ where
  toFun x := Real.log x.val
  invFun u := ⟨Real.exp u, Real.exp_pos u⟩
  left_inv x := Subtype.ext (Real.exp_log x.property)
  right_inv u := Real.log_exp u
  continuous_toFun := continuous_subtype_val.log (fun x => x.property.ne')
  continuous_invFun := Real.continuous_exp.subtype_mk _

theorem log_measurePreserving : MeasurePreserving logEquiv positiveHaar volume := by
  refine ⟨logEquiv.measurable, ?_⟩
  have h := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure ℝ)
    (s := Set.Ioi 0) (f := Real.log)
    (f' := fun x => ContinuousLinearMap.toSpanSingleton ℝ x⁻¹)
    measurableSet_Ioi.nullMeasurableSet
    (fun x hx => (Real.hasDerivAt_log hx.ne').hasFDerivAt.hasFDerivWithinAt)
    Real.strictMonoOn_log.injOn
  have him : Real.log '' Set.Ioi 0 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro u
    exact ⟨Real.exp u, Real.exp_pos u, Real.log_exp u⟩
  have hd (x : ℝ) : (ContinuousLinearMap.toSpanSingleton ℝ x⁻¹).det = x⁻¹ :=
    ContinuousLinearMap.det_toSpanSingleton _
  simp only [hd, him, Measure.restrict_univ] at h
  change Measure.map (Real.log ∘ Subtype.val) positiveHaar = volume
  rw [← Measure.map_map Real.measurable_log measurable_subtype_coe,
    positiveHaar_map_val, Measure.restrict_withDensity measurableSet_Ioi]
  convert h using 2
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [abs_of_pos (inv_pos.mpr hx)]

theorem integral_log (f : ℝ → ℂ) :
    (∫ u : ℝ, f u) = ∫ t : PositiveAxis, f (Real.log t.val) ∂positiveHaar := by
  rw [← log_measurePreserving.map_eq]
  exact logEquiv.toMeasurableEquiv.measurableEmbedding.integral_map f

theorem integral_exp (f : PositiveAxis → ℂ) :
    (∫ u : ℝ, f (logEquiv.symm u)) = ∫ t : PositiveAxis, f t ∂positiveHaar := by
  rw [integral_log]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => congrArg f (logEquiv.symm_apply_apply t)

theorem integrable_exp_iff (f : PositiveAxis → ℂ) :
    Integrable (fun u : ℝ => f (logEquiv.symm u)) ↔ Integrable f positiveHaar := by
  rw [← log_measurePreserving.map_eq,
    logEquiv.toMeasurableEquiv.measurableEmbedding.integrable_map_iff]
  simpa only [logEquiv.symm_apply_apply]

theorem positiveSpectrum_eq_mellin (f : PositiveAxis → ℂ) (τ : ℝ) :
    ScalarMellinConvolution.positiveSpectrum (fun u => f (logEquiv.symm u)) τ =
      ∫ t : PositiveAxis, (t.val : ℂ) ^ ((τ : ℂ) * Complex.I) * f t ∂positiveHaar := by
  unfold ScalarMellinConvolution.positiveSpectrum
  rw [integral_log]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    rw [logEquiv.symm_apply_apply]
    unfold ScalarMellinConvolution.phase
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr t.property.ne'),
      ← Complex.ofReal_log t.property.le]
    rw [mul_comm (f t)]
    congr 1
    congr 1
    ring

theorem exp_inverse_sq (u : ℝ) : ((Real.exp u) ^ 2)⁻¹ = Real.exp (-2 * u) := by
  rw [← Real.exp_nat_mul, ← Real.exp_neg]
  congr 1
  ring

end ThetaGlobal.PositiveAxisLog

#print axioms ThetaGlobal.PositiveAxisLog.log_measurePreserving
#print axioms ThetaGlobal.PositiveAxisLog.positiveSpectrum_eq_mellin
