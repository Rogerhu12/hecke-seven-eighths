import HeckeSkeleton.HighBinSupport.ActualNormFormWindowDetector
import HeckeSkeleton.HighBinSupport.ActualNormFormUniformMellin
import HeckeSkeleton.HighBinSupport.ActualRowLogDerivative
import HeckeSkeleton.HighBinSupport.BoundaryRectangle

/-!
Finite zero-free contour transport for the actual annular prime detector.

Both horizontal faces and the discarded initial vertical tails are kept.
The logarithmic derivative is the derivative of the genuine continuation;
its initial identity is proved by equality with the genuine Hecke series.
-/

noncomputable section
namespace HighBinVerified.NormFormPrimeContour

open NumberField IsDedekindDomain MeasureTheory Complex Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HeckeBufferedReciprocal
open HeckeSkeleton.HeckePhysicalFamilyBufferedControl
open NormFormMellin NormFormPrimeDetector NormFormActual ActualRowLogDerivative
open scoped Classical Topology BigOperators

def decayWeight (r : ℝ) : ℝ := 1 / (1 + |r|) ^ 2

theorem decayWeight_nonneg (r : ℝ) : 0 ≤ decayWeight r := by
  unfold decayWeight
  positivity

theorem integrable_decayWeight : Integrable decayWeight := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  convert h using 1
  ext r
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity : 0 ≤ 1 + |r|), Real.rpow_two]
  rfl

def decayMass : ℝ := (∫ r : ℝ, decayWeight r) + 1

theorem decayMass_pos : 0 < decayMass := by
  have h := integral_nonneg decayWeight_nonneg
  unfold decayMass
  linarith

theorem norm_setIntegral_decayWeight_le (f : ℝ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (D : Set ℝ) (hD : MeasurableSet D)
    (hbound : ∀ r ∈ D, ‖f r‖ ≤ A * decayWeight r) :
    ‖∫ r in D, f r‖ ≤ A * decayMass := by
  have hg := integrable_decayWeight.const_mul A
  calc
    _ ≤ ∫ r in D, A * decayWeight r :=
      norm_integral_le_of_norm_le hg.restrict
        ((ae_restrict_iff' hD).mpr (Eventually.of_forall hbound))
    _ ≤ ∫ r : ℝ, A * decayWeight r :=
      setIntegral_le_integral hg (Eventually.of_forall
        (fun r => mul_nonneg hA (decayWeight_nonneg r)))
    _ = A * ∫ r : ℝ, decayWeight r := integral_const_mul A _
    _ ≤ A * decayMass := by
      unfold decayMass
      nlinarith

theorem decay_weighted_tail_le {n : ℕ} {H r D v : ℝ}
    (hH : 0 ≤ H) (hr : H ≤ |r|) (hv : 0 ≤ v)
    (hbound : (1 + |r|) ^ (n + 2) * v ≤ D) :
    v ≤ (D / (1 + H) ^ n) * decayWeight r := by
  have hH1 : 0 < 1 + H := by linarith
  have hr1 : 0 < 1 + |r| := by positivity
  have hp : (1 + H) ^ n ≤ (1 + |r|) ^ n :=
    pow_le_pow_left₀ hH1.le (by linarith) n
  have hbase : (1 + H) ^ n * (1 + |r|) ^ 2 * v ≤ D := by
    calc
      _ ≤ (1 + |r|) ^ n * (1 + |r|) ^ 2 * v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by positivity)) hv
      _ = (1 + |r|) ^ (n + 2) * v := by rw [pow_add]
      _ ≤ D := hbound
  unfold decayWeight
  rw [mul_one_div]
  apply (le_div_iff₀ (pow_pos hr1 2)).mpr
  apply (le_div_iff₀ (pow_pos hH1 n)).mpr
  nlinarith [hbase]

variable (K : Type) [Field K] [NumberField K]

def primeDetectorIntegrand (V : SmoothAnnularTest) (chi : HeckeCharacter K)
    (P t : ℝ) (s : ℂ) : ℂ :=
  mellin V.toFun (s - (1 / 2 : ℂ)) * (P : ℂ) ^ (s - (1 / 2 : ℂ)) *
    continuedLogDerivative K chi (s - (t : ℂ) * I)

theorem primeDetectorIntegrand_vertical (V : SmoothAnnularTest)
    (chi : HeckeCharacter K) (P t sigma r : ℝ) :
    primeDetectorIntegrand K V chi P t (idealVerticalPoint sigma r) =
      annularMellinKernel V P (1 / 2) sigma r *
        continuedLogDerivative K chi (idealVerticalPoint sigma r - (t : ℂ) * I) := by
  have hs : idealVerticalPoint sigma r - (1 / 2 : ℂ) =
      idealVerticalPoint (sigma - 1 / 2) r := by
    unfold idealVerticalPoint
    push_cast
    ring
  simp only [primeDetectorIntegrand, annularMellinKernel, hs]

theorem primeDetectorIntegrand_initial (V : SmoothAnnularTest)
    (chi : HeckeCharacter K) (P t r : ℝ) {sigma : ℝ} (hsigma : 1 < sigma) :
    primeDetectorIntegrand K V chi P t (idealVerticalPoint sigma r) =
      annularMellinKernel V P (1 / 2) sigma r *
        heckeLogDerivative K (chi * heckeNormTwist K t) (idealVerticalPoint sigma r) := by
  rw [primeDetectorIntegrand_vertical,
    continuedLogDerivative_eq_heckeLogDerivative K chi (by simpa using hsigma),
    heckeLogDerivative_normTwist K chi t (by simpa using hsigma)]

theorem integrable_primeDetectorIntegrand_initial (V : SmoothAnnularTest)
    (chi : HeckeCharacter K) {P : ℝ} (hP : 0 < P) (t : ℝ)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Integrable (fun r : ℝ => primeDetectorIntegrand K V chi P t (idealVerticalPoint sigma r)) := by
  simp_rw [primeDetectorIntegrand_initial K V chi P t _ hsigma]
  exact integrable_annular_logDerivative K V (chi * heckeNormTwist K t) hP (1 / 2) hsigma

/-- The actual initial L'/L is bounded independently of the character and
phase by the convergent prime-power ideal majorant on Re(s)=3/2. -/
def initialLogDerivativeBound : ℝ :=
  (∑' pn : HeightOneSpectrum (𝓞 K) × ℕ,
    idealVerticalMajorant K 1 (3 / 2) (primePowerIdeal K pn)) + 1

theorem initialLogDerivativeBound_pos : 0 < initialLogDerivativeBound K := by
  have h := tsum_nonneg (fun pn : HeightOneSpectrum (𝓞 K) × ℕ =>
    idealVerticalMajorant_nonneg K 1 (3 / 2) (primePowerIdeal K pn))
  unfold initialLogDerivativeBound
  linarith

theorem continuedLogDerivative_initial_norm_le (chi : HeckeCharacter K) (t r : ℝ) :
    ‖continuedLogDerivative K chi (idealVerticalPoint (3 / 2) r - (t : ℂ) * I)‖ ≤
      initialLogDerivativeBound K := by
  rw [continuedLogDerivative_eq_heckeLogDerivative K chi (by norm_num [idealVerticalPoint]),
    ← heckeLogDerivative_normTwist K chi t (by norm_num [idealVerticalPoint])]
  have heq := iteratedDeriv_heckeLogDerivative K (chi * heckeNormTwist K t) 0
    (s := idealVerticalPoint (3 / 2) r) (by norm_num [idealVerticalPoint])
  rw [iteratedDeriv_zero] at heq
  rw [heq]
  exact (norm_primePowerDerivativeSeries_vertical_le K
    (primeCoefficient K (chi * heckeNormTwist K t))
    (norm_primeCoefficient_le_one K (chi * heckeNormTwist K t)) 0 (by norm_num) r).trans
      (by unfold initialLogDerivativeBound; linarith)

/-- Holomorphy of the actual detector on the complete closed rectangle.
The phase shift consumes exactly |t| of the upper-zero height buffer. -/
theorem primeDetectorIntegrand_differentiableOn_rectangle (V : SmoothAnnularTest)
    (chi : HeckeCharacter K) (hnon : ∀ t : ℝ, chi ≠ heckeNormTwist K t)
    {P : ℝ} (hP : 0 < P) (t l r H U alpha : ℝ)
    (hlr : l ≤ r) (hH : 0 ≤ H) (halpha : 1 / 2 ≤ alpha) (hal : alpha < l)
    (hheight : H + |t| ≤ U) (hupper : ZeroUpperBound K chi U alpha) :
    DifferentiableOn ℂ (primeDetectorIntegrand K V chi P t)
      (uIcc l r ×ℂ uIcc (-H) H) := by
  intro s hs
  rw [uIcc_of_le hlr, uIcc_of_le (by linarith : -H ≤ H)] at hs
  have hsi : |s.im| ≤ H := abs_le.mpr hs.2
  have hshift : |(s - (t : ℂ) * I).im| ≤ U := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add]
    exact (abs_sub s.im t).trans ((add_le_add_right hsi _).trans hheight)
  have hlog := continuedLogDerivative_analyticAt_of_upper K chi hnon U alpha halpha
    hupper (s - (t : ℂ) * I) (by simpa using hal.trans_le hs.1.1) hshift
  have hm := (HighBinBoundary.ActualDenominator.differentiable_mellin V)
    (s - (1 / 2 : ℂ))
  have hp : DifferentiableAt ℂ (fun z : ℂ => (P : ℂ) ^ z) (s - (1 / 2 : ℂ)) :=
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hP.ne'))) _
  exact (((hm.comp s (differentiableAt_id.sub_const _)).mul
    (hp.comp s (differentiableAt_id.sub_const _))).mul
    (hlog.differentiableAt.comp s (differentiableAt_id.sub_const _))).differentiableWithinAt

theorem primeDetectorIntegrand_weighted_norm_le (V : SmoothAnnularTest)
    (chi : HeckeCharacter K) {P : ℝ} (hP : 0 < P)
    (t sigma r D M : ℝ) (n : ℕ) (hD : 0 ≤ D)
    (hmellin : (1 + |r|) ^ n *
      ‖mellin V.toFun (idealVerticalPoint (sigma - 1 / 2) r)‖ ≤ D)
    (hlog : ‖continuedLogDerivative K chi (idealVerticalPoint sigma r - (t : ℂ) * I)‖ ≤ M) :
    (1 + |r|) ^ n *
      ‖primeDetectorIntegrand K V chi P t (idealVerticalPoint sigma r)‖ ≤
      D * P ^ (sigma - 1 / 2) * M := by
  rw [primeDetectorIntegrand_vertical, annularMellinKernel, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hP, idealVerticalPoint_re]
  calc
    _ = ((1 + |r|) ^ n * ‖mellin V.toFun (idealVerticalPoint (sigma - 1 / 2) r)‖) *
        P ^ (sigma - 1 / 2) *
        ‖continuedLogDerivative K chi (idealVerticalPoint sigma r - (t : ℂ) * I)‖ := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hmellin (Real.rpow_nonneg hP.le _))
      hlog (norm_nonneg _) (mul_nonneg hD (Real.rpow_nonneg hP.le _))

end HighBinVerified.NormFormPrimeContour

#print axioms HighBinVerified.NormFormPrimeContour.primeDetectorIntegrand_differentiableOn_rectangle
#print axioms HighBinVerified.NormFormPrimeContour.continuedLogDerivative_initial_norm_le
