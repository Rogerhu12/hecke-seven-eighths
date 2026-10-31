import HeckeSkeleton.HighBinSupport.ActualRegularEuler
import HeckeSkeleton.HighBinSupport.EulerRegionAnalytic
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The genuine regular Euler product is nonzero in the initial domain

The boundary continuation bridge uses this common regular product. The
finite exceptional factors are not divided out and are not asserted to be nonzero. Only the
common regular product, after an arbitrary finite set is removed, is shown
nonzero from its actual eleven-monomial error estimate and ideal counting.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinContinuation

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

/-- A rational lower bound for the existing fixed denominator margin. -/
theorem sweptTubeEulerMargin_ge_one_eighth : (1 / 8 : ℝ) ≤ sweptTubeEulerMargin := by
  have hsq : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hroot : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    nlinarith [sq_nonneg ((2 : ℝ) ^ (-(1 / 2 : ℝ)) - 1)]
  unfold sweptTubeEulerMargin
  nlinarith

/-- All imaginary parts are allowed; the original initial real parts
put all five summability faces at distance at least six. -/
theorem phaseRowEuler_norm_initial
    {q : ℝ} (hq : 2 ≤ q) (cW cD cE s w z : ℂ)
    (hW : ‖cW‖ ≤ 1) (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    ‖phaseRowEuler q cW cD cE s w z - 1‖ ≤ 88 * q ^ (-7 : ℝ) := by
  have hb := phaseRowEuler_region_bound (δ := 6) hq (by norm_num)
    cW cD cE s w z hW hD hE
    (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  norm_num only at hb
  have hC : 11 / sweptTubeEulerMargin ≤ 88 := by
    apply (div_le_iff₀ sweptTubeEulerMargin_pos).mpr
    nlinarith [sweptTubeEulerMargin_ge_one_eighth]
  exact hb.trans (mul_le_mul_of_nonneg_right hC
    (Real.rpow_nonneg (by linarith : 0 ≤ q) _))

/-- Every common regular factor is nonzero in the initial domain. This
assertion does not apply to any of the exceptional finite Laurent tables. -/
theorem phaseRowEuler_ne_zero_initial
    {q : ℝ} (hq : 2 ≤ q) (cW cD cE s w z : ℂ)
    (hW : ‖cW‖ ≤ 1) (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    phaseRowEuler q cW cD cE s w z ≠ 0 := by
  have hb := phaseRowEuler_norm_initial hq cW cD cE s w z hW hD hE hs hw hz
  have hp : q ^ (-7 : ℝ) ≤ (2 : ℝ) ^ (-7 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
  have hsmall : ‖phaseRowEuler q cW cD cE s w z - 1‖ < 1 := by
    calc
      _ ≤ 88 * q ^ (-7 : ℝ) := hb
      _ ≤ 88 * (2 : ℝ) ^ (-7 : ℝ) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ < 1 := by norm_num
  intro hzero
  simpa only [hzero, zero_sub, norm_neg, norm_one, lt_self_iff_false] using hsmall

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem localRowCorrection_norm_initial (P : ProbeData K S) (ψ χ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s w z : ℂ)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    ‖localRowCorrection K S P ψ χ p s w z - 1‖ ≤
      88 * (p.val.asIdeal.absNorm : ℝ) ^ (-7 : ℝ) := by
  rw [localRowCorrection_eq_phase]
  exact phaseRowEuler_norm_initial (exteriorPrime_norm_two_le K S p) _ _ _ s w z
    (norm_primeCoefficient_le_one K χ p.val) (actualEuler_D_phase_norm K S ψ χ p)
    (actualEuler_E_phase_norm K S P ψ p) hs hw hz

/-- Absolute regular error summability comes directly from actual ideal
counting. There is no local-product or nonvanishing hypothesis. -/
theorem summable_localRowCorrection_norm_initial (P : ProbeData K S)
    (ψ χ : HeckeCharacter K) (s w z : ℂ)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    Summable (fun p : ExteriorPrime K S =>
      ‖localRowCorrection K S P ψ χ p s w z - 1‖) := by
  have hmajor := (summable_exteriorPrime_norm_rpow K S
    (σ := 7) (by norm_num)).mul_left 88
  exact hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => localRowCorrection_norm_initial K S P ψ χ p s w z hs hw hz)

/-- Removing any finite set leaves a nonzero common regular product.
The omitted finite factors may have zeros; none are cancelled here. -/
theorem localRowCorrection_tprod_compl_ne_zero_initial
    (P : ProbeData K S) (ψ χ : HeckeCharacter K)
    (F : Finset (ExteriorPrime K S)) (s w z : ℂ)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    (∏' p : {p : ExteriorPrime K S // p ∉ F},
      localRowCorrection K S P ψ χ p.val s w z) ≠ 0 := by
  let f : {p : ExteriorPrime K S // p ∉ F} → ℂ := fun p =>
    localRowCorrection K S P ψ χ p.val s w z - 1
  have hsum : Summable (fun p => ‖f p‖) := by
    simpa only [f] using
      (summable_localRowCorrection_norm_initial K S P ψ χ s w z hs hw hz).subtype
        (fun p : ExteriorPrime K S => p ∉ F)
  have heq (p : {p : ExteriorPrime K S // p ∉ F}) :
      1 + f p = localRowCorrection K S P ψ χ p.val s w z := by
    dsimp only [f]
    ring
  have hlocal (p : {p : ExteriorPrime K S // p ∉ F}) : 1 + f p ≠ 0 := by
    rw [heq, localRowCorrection_eq_phase]
    exact phaseRowEuler_ne_zero_initial (exteriorPrime_norm_two_le K S p.val)
      _ _ _ s w z (norm_primeCoefficient_le_one K χ p.val.val)
      (actualEuler_D_phase_norm K S ψ χ p.val)
      (actualEuler_E_phase_norm K S P ψ p.val) hs hw hz
  have h := tprod_one_add_ne_zero_of_summable hlocal hsum
  rw [tprod_congr heq] at h
  exact h

#print axioms sweptTubeEulerMargin_ge_one_eighth
#print axioms phaseRowEuler_norm_initial
#print axioms phaseRowEuler_ne_zero_initial
#print axioms localRowCorrection_norm_initial
#print axioms summable_localRowCorrection_norm_initial
#print axioms localRowCorrection_tprod_compl_ne_zero_initial

end HeckeSkeleton.HighBinContinuation
