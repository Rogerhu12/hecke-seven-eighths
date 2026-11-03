import HeckeGeneral.Analysis.PhysicalProbeData
import HeckeGeneral.Analysis.TraceSchwartzEuler
import HeckeGeneral.Arithmetic.SLocalNormSectionAlgebra
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
UNCOMPILED / native 0. Actual log-radius profiles for the original additive
probe, with a constructed smooth cutoff equal to one on the denominator
annulus. Fourier frequencies use Mathlib's exp(2*pi*i*xi*v) convention.
No smoothness, inversion or finite-ray coefficient identity is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators FourierTransform ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "G" => sLocalMultiplicativeGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "D" => (Module.finrank ℚ K : ℝ)

/-- A concrete bump large enough to contain the logarithmic denominator annulus. -/
def denominatorLogCutoff (W : SmoothAnnularTest) : ContDiffBump (0 : ℝ) where
  rIn := |Real.log W.lower| + |Real.log W.upper| + 1
  rOut := |Real.log W.lower| + |Real.log W.upper| + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem denominatorLogCutoff_log_eq_one (W : SmoothAnnularTest)
    {y : ℝ} (hy : y ∈ Icc W.lower W.upper) :
    denominatorLogCutoff W (Real.log y) = 1 := by
  apply (denominatorLogCutoff W).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  have hlo := Real.log_le_log W.lower_pos hy.1
  have hhi := Real.log_le_log (W.lower_pos.trans_le hy.1) hy.2
  have habs : |Real.log y| ≤ |Real.log W.lower| + |Real.log W.upper| := by
    apply abs_le.mpr
    constructor
    · have := neg_abs_le (Real.log W.lower)
      have := abs_nonneg (Real.log W.upper)
      linarith
    · have := le_abs_self (Real.log W.upper)
      have := abs_nonneg (Real.log W.lower)
      linarith
  change |Real.log y| ≤ |Real.log W.lower| + |Real.log W.upper| + 1
  linarith

/-- The actual local-group curve; finite coordinates do not move. -/
def probeRawLogProfile (P : ProbeData K S) (x : G) (v : ℝ) : ℂ :=
  additiveTest K S P.additive
    (sLocalNormSection K S ⟨Real.exp (-v), Real.exp_pos _⟩ * x)

theorem probeRawLogProfile_eq (P : ProbeData K S) (x : G) (v : ℝ) :
    probeRawLogProfile K S P x v =
      P.additive.infiniteTest
        (Real.exp ((-v) / D) •
          (traceToMixed K).symm (x.1 : mixedEmbedding.mixedSpace K)) *
        ∏ p : S, P.additive.finiteTest p ((x.2 p).val) := by
  simp [probeRawLogProfile, additiveTest, sLocalTensorTestFunction,
    sLocalNormSection, realScaleMixedUnit_val, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, traceNormSection_exp_scale]

theorem contDiff_probeRawLogProfile (P : ProbeData K S) (x : G) :
    ContDiff ℝ ∞ (probeRawLogProfile K S P x) := by
  change ContDiff ℝ ∞ (fun v : ℝ => probeRawLogProfile K S P x v)
  simp_rw [probeRawLogProfile_eq]
  refine ((P.additive.infiniteTest.smooth ⊤).comp ?_).mul contDiff_const
  fun_prop

/-- Compact support is supplied by the actual denominator, not by a profile input. -/
def probeCutLogProfile (P : ProbeData K S) (x : G) (v : ℝ) : ℂ :=
  denominatorLogCutoff P.denominator.toSmoothAnnularTest v •
    probeRawLogProfile K S P x v

theorem contDiff_probeCutLogProfile (P : ProbeData K S) (x : G) :
    ContDiff ℝ ∞ (probeCutLogProfile K S P x) :=
  (denominatorLogCutoff P.denominator.toSmoothAnnularTest).contDiff.smul
    (contDiff_probeRawLogProfile K S P x)

theorem hasCompactSupport_probeCutLogProfile (P : ProbeData K S) (x : G) :
    HasCompactSupport (probeCutLogProfile K S P x) :=
  (denominatorLogCutoff P.denominator.toSmoothAnnularTest).hasCompactSupport.smul_right

def probeLogSchwartz (P : ProbeData K S) (x : G) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_probeCutLogProfile K S P x).toSchwartzMap
    (contDiff_probeCutLogProfile K S P x)

@[simp] theorem probeLogSchwartz_apply (P : ProbeData K S) (x : G) (v : ℝ) :
    probeLogSchwartz K S P x v = probeCutLogProfile K S P x v := rfl

theorem probeLogSchwartz_log_eq (P : ProbeData K S) (x : G)
    {y : ℝ} (hy : P.denominator.toFun y ≠ 0) :
    probeLogSchwartz K S P x (Real.log y) =
      probeRawLogProfile K S P x (Real.log y) := by
  have hmem := P.denominator.support hy
  simp only [probeLogSchwartz_apply, probeCutLogProfile,
    denominatorLogCutoff_log_eq_one _ hmem, one_smul]

/-- Both Fourier integrability conditions are actual Schwartz consequences. -/
theorem probeLogSchwartz_fourier_integrable (P : ProbeData K S) (x : G) :
    Integrable (fun ξ : ℝ => (𝓕 (probeLogSchwartz K S P x)) ξ) :=
  (𝓕 (probeLogSchwartz K S P x)).integrable

/-- Standard 2*pi Fourier inversion, retaining its literal Circle action. -/
theorem probeLogSchwartz_inversion (P : ProbeData K S) (x : G) (v : ℝ) :
    probeLogSchwartz K S P x v =
      ∫ ξ : ℝ, Real.fourierChar (ξ * v) • (𝓕 (probeLogSchwartz K S P x)) ξ := by
  have h := congrFun ((probeLogSchwartz K S P x).continuous.fourierInv_fourier_eq
    (probeLogSchwartz K S P x).integrable
    (𝓕 (probeLogSchwartz K S P x)).integrable) v
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq] at h
  simpa only [mul_neg, neg_neg, SchwartzMap.fourier_coe] using h.symm

/-- Moving the original denominator radius to the log profile is group algebra. -/
theorem probeRawLogProfile_original_scale (P : ProbeData K S)
    (m : NonzeroRingElements (S.integer K)) (t : sLocalNormOneGroup K S)
    (X Y q : ℝ) (hX : 0 < X) (hY : 0 < Y) (hq : 0 < q) :
    probeRawLogProfile K S P
        (sLocalNonzeroIntegerDiagonal K S m /
          ((t : G) * sLocalNormSection K S ⟨X * Y, mul_pos hX hY⟩))
        (Real.log (q / Y)) =
      additiveTest K S P.additive
        (sLocalNonzeroIntegerDiagonal K S m /
          ((t : G) * sLocalNormSection K S ⟨q * X, mul_pos hq hX⟩)) := by
  have hy : 0 < q / Y := div_pos hq hY
  have hexp : Real.exp (-Real.log (q / Y)) = (q / Y)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hy]
  have hrad : (X * Y) * (q / Y) = q * X := by field_simp [hY.ne']
  have hsection :
      sLocalNormSection K S ⟨q * X, mul_pos hq hX⟩ =
        sLocalNormSection K S ⟨X * Y, mul_pos hX hY⟩ *
          sLocalNormSection K S ⟨q / Y, hy⟩ := by
    rw [← sLocalNormSection_mul]
    congr 1
    exact Subtype.ext hrad.symm
  unfold probeRawLogProfile
  have hinv : sLocalNormSection K S ⟨Real.exp (-Real.log (q / Y)), Real.exp_pos _⟩ =
      (sLocalNormSection K S ⟨q / Y, hy⟩)⁻¹ := by
    rw [← sLocalNormSection_inv]
    congr 1
    exact Subtype.ext hexp
  rw [hinv, hsection]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft
