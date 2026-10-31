import HeckeSkeleton.HighBinSupport.ActualNormFormMellinInversion
import HeckeGeneral.Analysis.IdealDerivativePrimePowerSmoothing

/-!
The initial annular logarithmic detector for the genuine Hecke series.

This file performs the actual infinite prime-power sum / Mellin integral
interchange on Re(s)>1. The kernel is the Mellin transform of the original
annular test divided by log(P y); the finite-support argument and Mellin
inversion have already been proved from that test. A subsequent zero-free
contour move is a separate step.
-/

noncomputable section
namespace HighBinVerified.NormFormPrimeDetector

open NumberField IsDedekindDomain MeasureTheory Complex
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open NormFormMellin
open scoped Topology BigOperators

def annularMellinKernel (V : SmoothAnnularTest) (P b sigma t : ℝ) : ℂ :=
  mellin V.toFun (idealVerticalPoint (sigma - b) t) *
    (P : ℂ) ^ idealVerticalPoint (sigma - b) t

theorem integrable_annularMellinKernel (V : SmoothAnnularTest)
    {P : ℝ} (hP : 0 < P) (b sigma : ℝ) :
    Integrable (annularMellinKernel V P b sigma) :=
  integrable_kernel_mul_vertical_cpow (verticalIntegrable_mellin V (sigma - b))
    hP (sigma - b)

private theorem cpow_scale_kernel {P N : ℝ} (hP : 0 < P) (hN : 0 < N)
    (b : ℝ) (s : ℂ) :
    (P : ℂ) ^ (s - (b : ℂ)) * (N : ℂ) ^ (-s) =
      (N : ℂ) ^ (-(b : ℂ)) * ((N / P : ℝ) : ℂ) ^ (-(s - (b : ℂ))) := by
  have hP0 : (P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hP.ne'
  have hN0 : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hNP0 : ((N / P : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos hN hP).ne'
  have hlog : Complex.log ((N / P : ℝ) : ℂ) =
      Complex.log (N : ℂ) - Complex.log (P : ℂ) := by
    rw [← Complex.ofReal_log (div_pos hN hP).le,
      Real.log_div hN.ne' hP.ne', Complex.ofReal_sub,
      Complex.ofReal_log hN.le, Complex.ofReal_log hP.le]
  simp only [Complex.cpow_def_of_ne_zero hP0, Complex.cpow_def_of_ne_zero hN0,
    Complex.cpow_def_of_ne_zero hNP0, hlog]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

private theorem normalized_mellin_integral (V : SmoothAnnularTest)
    (sigma : ℝ) {x : ℝ} (hx : 0 < x) :
    (2 * (Real.pi : ℂ))⁻¹ *
      (∫ t : ℝ, mellin V.toFun (idealVerticalPoint sigma t) *
        (x : ℂ) ^ (-idealVerticalPoint sigma t)) = V.toFun x := by
  have h := mellin_inversion_annular V sigma hx
  simpa only [mellinInv, idealVerticalPoint, Complex.real_smul, smul_eq_mul,
    one_div, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat,
    mul_comm] using h

variable (K : Type) [Field K] [NumberField K]

theorem annular_primePower_integrand (V : SmoothAnnularTest)
    (a : HeightOneSpectrum (𝓞 K) → ℂ) {P : ℝ} (hP : 0 < P)
    (b sigma t : ℝ) (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    annularMellinKernel V P b sigma t *
      primePowerDerivativeTerm K a 0 (idealVerticalPoint sigma t) pn =
    (((pn.2 + 1 : ℕ) : ℂ)⁻¹ *
      (-(Real.log (idealNorm K (primePowerIdeal K pn)) : ℂ)) *
      nonzeroIdealCoefficient a (primePowerIdeal K pn) *
      (idealNorm K (primePowerIdeal K pn) : ℂ) ^ (-(b : ℂ))) *
      (mellin V.toFun (idealVerticalPoint (sigma - b) t) *
        ((idealNorm K (primePowerIdeal K pn) / P : ℝ) : ℂ) ^
          (-idealVerticalPoint (sigma - b) t)) := by
  have hs : idealVerticalPoint sigma t - (b : ℂ) =
      idealVerticalPoint (sigma - b) t := by
    unfold idealVerticalPoint
    push_cast
    ring
  have hp := cpow_scale_kernel hP (idealNorm_pos K (primePowerIdeal K pn)) b
    (idealVerticalPoint sigma t)
  rw [hs] at hp
  simp only [annularMellinKernel, primePowerDerivativeTerm, idealLogTerm,
    zero_add, pow_one, dirichletTerm]
  calc
    _ = (((pn.2 + 1 : ℕ) : ℂ)⁻¹ *
        (-(Real.log (idealNorm K (primePowerIdeal K pn)) : ℂ)) *
        nonzeroIdealCoefficient a (primePowerIdeal K pn)) *
        mellin V.toFun (idealVerticalPoint (sigma - b) t) *
        ((P : ℂ) ^ idealVerticalPoint (sigma - b) t *
          (idealNorm K (primePowerIdeal K pn) : ℂ) ^ (-idealVerticalPoint sigma t)) := by
      ring
    _ = _ := by rw [hp]; ring

/-- Termwise inversion for the actual positive prime ideal powers. -/
theorem integral_annularMellinKernel_primePower (V : SmoothAnnularTest)
    (a : HeightOneSpectrum (𝓞 K) → ℂ) {P : ℝ} (hP : 0 < P)
    (b sigma : ℝ) (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t : ℝ,
      annularMellinKernel V P b sigma t *
        primePowerDerivativeTerm K a 0 (idealVerticalPoint sigma t) pn) =
      (((pn.2 + 1 : ℕ) : ℂ)⁻¹ *
        (-(Real.log (idealNorm K (primePowerIdeal K pn)) : ℂ)) *
        nonzeroIdealCoefficient a (primePowerIdeal K pn) *
        (idealNorm K (primePowerIdeal K pn) : ℂ) ^ (-(b : ℂ))) *
        V.toFun (idealNorm K (primePowerIdeal K pn) / P) := by
  simp_rw [annular_primePower_integrand K V a hP b sigma]
  rw [integral_const_mul]
  calc
    _ = (((pn.2 + 1 : ℕ) : ℂ)⁻¹ *
        (-(Real.log (idealNorm K (primePowerIdeal K pn)) : ℂ)) *
        nonzeroIdealCoefficient a (primePowerIdeal K pn) *
        (idealNorm K (primePowerIdeal K pn) : ℂ) ^ (-(b : ℂ))) *
        ((2 * (Real.pi : ℂ))⁻¹ *
          ∫ t : ℝ, mellin V.toFun (idealVerticalPoint (sigma - b) t) *
            ((idealNorm K (primePowerIdeal K pn) / P : ℝ) : ℂ) ^
              (-idealVerticalPoint (sigma - b) t)) := by ring
    _ = _ := by
      rw [normalized_mellin_integral V (sigma - b)
        (div_pos (idealNorm_pos K (primePowerIdeal K pn)) hP)]

/-- The actual L'/L detector is integrable on every initial line sigma>1. -/
theorem integrable_annular_logDerivative (V : SmoothAnnularTest)
    (chi : HeckeCharacter K) {P : ℝ} (hP : 0 < P)
    (b : ℝ) {sigma : ℝ} (hsigma : 1 < sigma) :
    Integrable (fun t : ℝ => annularMellinKernel V P b sigma t *
      heckeLogDerivative K chi (idealVerticalPoint sigma t)) := by
  have heq (t : ℝ) : heckeLogDerivative K chi (idealVerticalPoint sigma t) =
      primePowerDerivativeSeries K (primeCoefficient K chi) 0 (idealVerticalPoint sigma t) := by
    simpa only [iteratedDeriv_zero] using
      iteratedDeriv_heckeLogDerivative K chi 0 (by simpa using hsigma)
  simp_rw [heq]
  exact integrable_kernel_mul_primePowerDerivativeSeries K (primeCoefficient K chi)
    (norm_primeCoefficient_le_one K chi) 0 hsigma
    (integrable_annularMellinKernel V hP b sigma)

/-- Full initial Mellin identity, with the actual ideal-norm majorant
justifying the infinite prime-power sum / integral exchange. -/
theorem integral_annular_logDerivative (V : SmoothAnnularTest)
    (chi : HeckeCharacter K) {P : ℝ} (hP : 0 < P)
    (b : ℝ) {sigma : ℝ} (hsigma : 1 < sigma) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t : ℝ,
      annularMellinKernel V P b sigma t *
        heckeLogDerivative K chi (idealVerticalPoint sigma t)) =
      ∑' pn : HeightOneSpectrum (𝓞 K) × ℕ,
        (((pn.2 + 1 : ℕ) : ℂ)⁻¹ *
          (-(Real.log (idealNorm K (primePowerIdeal K pn)) : ℂ)) *
          nonzeroIdealCoefficient (primeCoefficient K chi) (primePowerIdeal K pn) *
          (idealNorm K (primePowerIdeal K pn) : ℂ) ^ (-(b : ℂ))) *
          V.toFun (idealNorm K (primePowerIdeal K pn) / P) := by
  have heq (t : ℝ) : heckeLogDerivative K chi (idealVerticalPoint sigma t) =
      primePowerDerivativeSeries K (primeCoefficient K chi) 0 (idealVerticalPoint sigma t) := by
    simpa only [iteratedDeriv_zero] using
      iteratedDeriv_heckeLogDerivative K chi 0 (by simpa using hsigma)
  simp_rw [heq]
  have h := (hasSum_integral_kernel_mul_primePowerDerivativeTerm K (primeCoefficient K chi)
    (norm_primeCoefficient_le_one K chi) 0 hsigma
    (integrable_annularMellinKernel V hP b sigma)).mul_left (2 * (Real.pi : ℂ))⁻¹
  simp_rw [integral_annularMellinKernel_primePower K V (primeCoefficient K chi) hP b sigma] at h
  exact h.tsum_eq.symm

/-- The log-removal test identifies the full actual annular prime-power
detector, including the sign convention L'/L = -sum(log Np ...). -/
theorem integral_annular_primePower_detector (V : SmoothAnnularTest)
    (hann : Function.support V.toFun ⊆ Set.Ioo (1 : ℝ) 2)
    (chi : HeckeCharacter K) {P : ℝ} (hP : 1 < P)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t : ℝ,
      annularMellinKernel (divideLogTest V hann P hP) P (1 / 2) sigma t *
        heckeLogDerivative K chi (idealVerticalPoint sigma t)) =
      -(∑' pn, HigherPrimePowers.heckeAnnularPrimePowerTerm K chi V.toFun P 0 pn) := by
  have hP0 : 0 < P := by linarith
  rw [integral_annular_logDerivative K (divideLogTest V hann P hP) chi hP0
    (1 / 2) hsigma, ← tsum_neg]
  apply tsum_congr
  intro pn
  have hq1 : (1 : ℝ) < (pn.1.asIdeal.absNorm : ℝ) := by
    exact_mod_cast one_lt_primeIdeal_absNorm K pn.1
  have hN1 : 1 < idealNorm K (primePowerIdeal K pn) := by
    rw [idealNorm_primePowerIdeal]
    exact one_lt_pow₀ hq1 (Nat.succ_ne_zero pn.2)
  have hlog : (Real.log (idealNorm K (primePowerIdeal K pn)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos hN1).ne'
  have hcancel : P * (idealNorm K (primePowerIdeal K pn) / P) =
      idealNorm K (primePowerIdeal K pn) := by field_simp [hP0.ne']
  have hvalue : (-(Real.log (idealNorm K (primePowerIdeal K pn)) : ℂ)) *
      (divideLogTest V hann P hP).toFun (idealNorm K (primePowerIdeal K pn) / P) =
      -V.toFun (idealNorm K (primePowerIdeal K pn) / P) := by
    change (-(Real.log (idealNorm K (primePowerIdeal K pn)) : ℂ)) *
      (V.toFun (idealNorm K (primePowerIdeal K pn) / P) /
        (Real.log (P * (idealNorm K (primePowerIdeal K pn) / P)) : ℂ)) = _
    rw [hcancel]
    field_simp [hlog]
  calc
    _ = (((pn.2 + 1 : ℕ) : ℂ)⁻¹ *
        nonzeroIdealCoefficient (primeCoefficient K chi) (primePowerIdeal K pn) *
        (idealNorm K (primePowerIdeal K pn) : ℂ) ^ (-((1 / 2 : ℝ) : ℂ))) *
        ((-(Real.log (idealNorm K (primePowerIdeal K pn)) : ℂ)) *
          (divideLogTest V hann P hP).toFun (idealNorm K (primePowerIdeal K pn) / P)) := by
      ring
    _ = _ := by
      rw [hvalue]
      simp only [HigherPrimePowers.heckeAnnularPrimePowerTerm,
        idealNorm_primePowerIdeal, nonzeroIdealCoefficient, primePowerIdeal_val,
        idealCoefficient_prime_pow, Complex.ofReal_zero, zero_mul, add_zero,
        Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one,
        Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_neg]
      ring

/-- Initial annular prime detector with a fully proved higher-power
error. The only remaining analytic step is the zero-free contour move. -/
theorem norm_annular_prime_sum_add_logDerivative_integral_le
    (V : SmoothAnnularTest) (hann : Function.support V.toFun ⊆ Set.Ioo (1 : ℝ) 2)
    (chi : HeckeCharacter K) (P delta M : ℝ) (hP : 1 < P)
    (hdelta : 0 < delta) (hM : 0 ≤ M) (hV : ∀ y : ℝ, ‖V.toFun y‖ ≤ M)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖(∑' p : HeightOneSpectrum (𝓞 K), V.toFun ((p.asIdeal.absNorm : ℝ) / P) *
        primeCoefficient K chi p * (p.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ))) +
      (2 * (Real.pi : ℂ))⁻¹ * (∫ t : ℝ,
        annularMellinKernel (divideLogTest V hann P hP) P (1 / 2) sigma t *
          heckeLogDerivative K chi (idealVerticalPoint sigma t))‖ ≤
      M * HigherPrimePowers.higherPowerConstant K delta * (2 * P) ^ delta := by
  rw [integral_annular_primePower_detector K V hann chi hP hsigma]
  simpa only [Complex.ofReal_zero, zero_mul, add_zero, sub_eq_add_neg] using
    HigherPrimePowers.norm_annular_prime_sum_sub_primePower_sum_le K chi V.toFun
      P delta 0 M (by linarith) hdelta hM hann hV

/-- The actual norm twist supplies arbitrary prime phases and the exact
height translation in L'/L. The error constant is independent of t. -/
theorem norm_annular_phase_sum_add_logDerivative_integral_le
    (V : SmoothAnnularTest) (hann : Function.support V.toFun ⊆ Set.Ioo (1 : ℝ) 2)
    (chi : HeckeCharacter K) (P delta t M : ℝ) (hP : 1 < P)
    (hdelta : 0 < delta) (hM : 0 ≤ M) (hV : ∀ y : ℝ, ‖V.toFun y‖ ≤ M)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖(∑' p : HeightOneSpectrum (𝓞 K), V.toFun ((p.asIdeal.absNorm : ℝ) / P) *
        primeCoefficient K chi p *
        (p.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)) +
      (2 * (Real.pi : ℂ))⁻¹ * (∫ r : ℝ,
        annularMellinKernel (divideLogTest V hann P hP) P (1 / 2) sigma r *
          heckeLogDerivative K chi (idealVerticalPoint sigma r - (t : ℂ) * Complex.I))‖ ≤
      M * HigherPrimePowers.higherPowerConstant K delta * (2 * P) ^ delta := by
  have h := norm_annular_prime_sum_add_logDerivative_integral_le K V hann
    (chi * heckeNormTwist K t) P delta M hP hdelta hM hV hsigma
  have hphase (p : HeightOneSpectrum (𝓞 K)) :
      V.toFun ((p.asIdeal.absNorm : ℝ) / P) *
          primeCoefficient K (chi * heckeNormTwist K t) p *
          (p.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ)) =
        V.toFun ((p.asIdeal.absNorm : ℝ) / P) * primeCoefficient K chi p *
          (p.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
    have hq0 : (p.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p)).ne'
    rw [primeCoefficient_normTwist]
    change (V.toFun ((p.asIdeal.absNorm : ℝ) / P) *
      (primeCoefficient K chi p * (p.asIdeal.absNorm : ℂ) ^ ((t : ℂ) * Complex.I))) *
      (p.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ)) = _
    calc
      _ = (V.toFun ((p.asIdeal.absNorm : ℝ) / P) * primeCoefficient K chi p) *
          ((p.asIdeal.absNorm : ℂ) ^ ((t : ℂ) * Complex.I) *
            (p.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ))) := by ring
      _ = _ := by rw [← Complex.cpow_add _ _ hq0, add_comm]
  have hshift (r : ℝ) :
      heckeLogDerivative K (chi * heckeNormTwist K t) (idealVerticalPoint sigma r) =
        heckeLogDerivative K chi (idealVerticalPoint sigma r - (t : ℂ) * Complex.I) :=
    heckeLogDerivative_normTwist K chi t (by simpa using hsigma)
  simpa only [hphase, hshift] using h

end HighBinVerified.NormFormPrimeDetector

#print axioms HighBinVerified.NormFormPrimeDetector.integrable_annular_logDerivative
#print axioms HighBinVerified.NormFormPrimeDetector.integral_annular_logDerivative
#print axioms HighBinVerified.NormFormPrimeDetector.integral_annular_primePower_detector
#print axioms HighBinVerified.NormFormPrimeDetector.norm_annular_prime_sum_add_logDerivative_integral_le
#print axioms HighBinVerified.NormFormPrimeDetector.norm_annular_phase_sum_add_logDerivative_integral_le
