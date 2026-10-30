import HeckeGeneral.Analysis.PhysicalProbeContours
import HeckeGeneral.Analysis.IdealEulerProduct
import HeckeSkeleton.HighBinSupport.EulerProducts

/-!
# Actual regular Euler factors on the high-bin swept tube

This file specializes the rational estimates to the repository's genuine
`localRowCorrection`, including its Hecke coefficients and theta period.
Prime summability is derived from number-field ideal counting. No Euler
calibration, product bound, or scalar summability is assumed.

The finite exceptional tables and the initial Fourier identity are separate
arithmetic obligations; this file makes no identification for them.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinContinuation

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open Set Filter
open scoped Topology BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem exteriorPrime_norm_two_le (p : ExteriorPrime K S) :
    (2 : ℝ) ≤ (p.val.asIdeal.absNorm : ℝ) := by
  have hqN : 2 ≤ p.val.asIdeal.absNorm := one_lt_primeIdeal_absNorm K p.val
  exact_mod_cast hqN

theorem summable_exteriorPrime_norm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ) ^ (-σ)) := by
  have hp := (summable_nonzeroIdeal_norm_rpow K hσ).comp_injective
    (primeNonzeroIdeal_injective K)
  have hs := hp.comp_injective
    (Subtype.val_injective : Function.Injective (fun p : ExteriorPrime K S => p.val))
  simpa only [primeNonzeroIdeal] using hs

theorem summable_exteriorPrime_swept_error {e : ℝ} (he : 0 < e) :
    Summable (fun p : ExteriorPrime K S =>
      (p.val.asIdeal.absNorm : ℝ) ^ (-1 - 8 * e)) := by
  have h := summable_exteriorPrime_norm_rpow K S (σ := 1 + 8 * e) (by linarith)
  convert h using 1
  funext p
  congr 1
  ring

theorem localRowCorrection_eq_phase (P : ProbeData K S) (ψ χ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s w z : ℂ) :
    localRowCorrection K S P ψ χ p s w z =
      phaseRowEuler (p.val.asIdeal.absNorm : ℝ)
        (primeCoefficient K χ p.val)
        (primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val))
        (primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6) s w z := by
  simp only [localRowCorrection, phaseRowEuler, Complex.ofReal_natCast]

theorem actualEuler_D_phase_norm (ψ χ : HeckeCharacter K) (p : ExteriorPrime K S) :
    ‖primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_one₀ (norm_primeCoefficient_le_one K ψ p.val)
    (norm_nonneg _) (norm_primeCoefficient_le_one K χ p.val)

theorem actualEuler_E_phase_norm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (p : ExteriorPrime K S) :
    ‖primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_primeCoefficient_le_one K _ p.val)

/-- Uniform at every point of the open tube, including all horizontal faces. -/
theorem localRowCorrection_sweptTube_bound (P : ProbeData K S)
    (ψ χ : HeckeCharacter K) (p : ExteriorPrime K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha' : a ≤ 1)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    ‖localRowCorrection K S P ψ χ p v.1 v.2.1 v.2.2 - 1‖ ≤
      (11 / sweptTubeEulerMargin) * (p.val.asIdeal.absNorm : ℝ) ^ (-1 - 8 * e) := by
  rw [localRowCorrection_eq_phase]
  exact phaseRowEuler_sweptTube_bound (exteriorPrime_norm_two_le K S p)
    ha ha' he he' _ _ _ (norm_primeCoefficient_le_one K χ p.val)
    (actualEuler_D_phase_norm K S ψ χ p) (actualEuler_E_phase_norm K S P ψ p) v hv

theorem localRowCorrection_analyticOnNhd_sweptTube (P : ProbeData K S)
    (ψ χ : HeckeCharacter K) (p : ExteriorPrime K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (he : 0 ≤ e) :
    AnalyticOnNhd ℂ
      (fun v : ℂ × ℂ × ℂ => localRowCorrection K S P ψ χ p v.1 v.2.1 v.2.2)
      (sweptTube a e) := by
  simp_rw [localRowCorrection_eq_phase]
  exact phaseRowEuler_analyticOnNhd (exteriorPrime_norm_two_le K S p) ha he _ _ _
    (actualEuler_D_phase_norm K S ψ χ p) (actualEuler_E_phase_norm K S P ψ p)

/-- Absolute regular-prime error summability follows from ideal counting. -/
theorem localRowCorrection_multipliable_sweptTube (P : ProbeData K S)
    (ψ χ : HeckeCharacter K) {a e : ℝ}
    (ha : 51 / 100 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e ≤ 1 / 10000)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    Multipliable (fun p : ExteriorPrime K S =>
      localRowCorrection K S P ψ χ p v.1 v.2.1 v.2.2) := by
  simp_rw [localRowCorrection_eq_phase]
  exact phaseRowEuler_multipliable _ _ _ _ (exteriorPrime_norm_two_le K S)
    ha ha' he.le he' (fun p => norm_primeCoefficient_le_one K χ p.val)
    (actualEuler_D_phase_norm K S ψ χ) (actualEuler_E_phase_norm K S P ψ)
    (summable_exteriorPrime_swept_error K S he) v hv

/-- Normal convergence is on the actual open three-variable domain. -/
theorem localRowCorrection_hasProdLocallyUniformlyOn_sweptTube (P : ProbeData K S)
    (ψ χ : HeckeCharacter K) {a e : ℝ}
    (ha : 51 / 100 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e ≤ 1 / 10000) :
    HasProdLocallyUniformlyOn
      (fun (p : ExteriorPrime K S) (v : ℂ × ℂ × ℂ) =>
        localRowCorrection K S P ψ χ p v.1 v.2.1 v.2.2)
      (fun v : ℂ × ℂ × ℂ => ∏' p : ExteriorPrime K S,
        localRowCorrection K S P ψ χ p v.1 v.2.1 v.2.2) (sweptTube a e) := by
  simp_rw [localRowCorrection_eq_phase]
  exact phaseRowEuler_hasProdLocallyUniformlyOn _ _ _ _ (exteriorPrime_norm_two_le K S)
    ha ha' he.le he' (fun p => norm_primeCoefficient_le_one K χ p.val)
    (actualEuler_D_phase_norm K S ψ χ) (actualEuler_E_phase_norm K S P ψ)
    (summable_exteriorPrime_swept_error K S he)

/-- The actual regular prime product is holomorphic along the s-move. -/
theorem localRowCorrection_tprod_differentiableOn_s (P : ProbeData K S)
    (ψ χ : HeckeCharacter K) {a e : ℝ}
    (ha : 51 / 100 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e ≤ 1 / 10000)
    (w z : ℂ) (hw : 1 - a - 7 * e < w.re) (hz : 17 / 50 - e < z.re) :
    DifferentiableOn ℂ (fun s => ∏' p : ExteriorPrime K S,
      localRowCorrection K S P ψ χ p s w z) {s | a + 15 * e < s.re} := by
  simp_rw [localRowCorrection_eq_phase]
  exact phaseRowEuler_tprod_differentiableOn_s _ _ _ _ (exteriorPrime_norm_two_le K S)
    ha ha' he.le he' (fun p => norm_primeCoefficient_le_one K χ p.val)
    (actualEuler_D_phase_norm K S ψ χ) (actualEuler_E_phase_norm K S P ψ)
    (summable_exteriorPrime_swept_error K S he) w z hw hz

end HeckeSkeleton.HighBinContinuation
