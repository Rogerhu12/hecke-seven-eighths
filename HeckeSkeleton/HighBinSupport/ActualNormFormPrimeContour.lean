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
    calc
      |s.im - t| ≤ |s.im| + |-t| := abs_add _ _
      _ = |s.im| + |t| := by rw [abs_neg]
      _ ≤ H + |t| := add_le_add_right hsi _
      _ ≤ U := hheight
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

/-- Quantitative finite transport for the actual detector. The right tail
uses the genuine prime-power majorant; the two finite horizontal faces
use the retained zero-free strip. This lemma is subsequently specialized
to the actual row-family bounds, so M is not an input to the final cap. -/
theorem primeDetector_initial_integral_norm_le (V : SmoothAnnularTest)
    (chi : HeckeCharacter K) (P t l H D M : ℝ) (n : ℕ)
    (hP : 1 ≤ P) (hl : 1 / 2 ≤ l) (hlr : l ≤ 3 / 2) (hH : 0 ≤ H)
    (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hF : DifferentiableOn ℂ (primeDetectorIntegrand K V chi P t)
      (uIcc l (3 / 2) ×ℂ uIcc (-H) H))
    (hmellin : ∀ sigma r : ℝ, l ≤ sigma → sigma ≤ 3 / 2 →
      (1 + |r|) ^ (n + 2) *
        ‖mellin V.toFun (idealVerticalPoint (sigma - 1 / 2) r)‖ ≤ D)
    (hlog : ∀ sigma r : ℝ, l ≤ sigma → sigma ≤ 3 / 2 → |r| ≤ H →
      ‖continuedLogDerivative K chi (idealVerticalPoint sigma r - (t : ℂ) * I)‖ ≤ M) :
    ‖∫ r : ℝ, primeDetectorIntegrand K V chi P t (idealVerticalPoint (3 / 2) r)‖ ≤
      D * M * decayMass * P ^ (l - 1 / 2) +
        D * (initialLogDerivativeBound K * decayMass + 4 * M) * P / (1 + H) ^ n := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hH1 : 0 < 1 + H := by linarith
  have hleft :
      ‖∫ r : ℝ in -H..H, primeDetectorIntegrand K V chi P t (idealVerticalPoint l r)‖ ≤
        D * M * decayMass * P ^ (l - 1 / 2) := by
    rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H),
      ← integral_Icc_eq_integral_Ioc]
    have hb := norm_setIntegral_decayWeight_le
      (fun r => primeDetectorIntegrand K V chi P t (idealVerticalPoint l r))
      (D * P ^ (l - 1 / 2) * M) (by positivity)
      (Icc (-H) H) measurableSet_Icc (by
        intro r hr
        have hw := primeDetectorIntegrand_weighted_norm_le K V chi hP0 t l r D M (n + 2)
          hD (hmellin l r le_rfl hlr) (hlog l r le_rfl hlr (abs_le.mpr hr))
        simpa using decay_weighted_tail_le (H := 0) (by norm_num) (abs_nonneg r)
          (norm_nonneg _) hw)
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hb
  have hface : ∀ sigma ∈ uIcc l (3 / 2), ∀ r : ℝ, |r| = H →
      ‖primeDetectorIntegrand K V chi P t (idealVerticalPoint sigma r)‖ ≤
        D * P * M / (1 + H) ^ n := by
    intro sigma hs r hr
    rw [uIcc_of_le hlr] at hs
    have hw := primeDetectorIntegrand_weighted_norm_le K V chi hP0
      t sigma r D M (n + 2) hD (hmellin sigma r hs.1 hs.2)
        (hlog sigma r hs.1 hs.2 hr.le)
    rw [hr] at hw
    have hp : (1 + H) ^ n ≤ (1 + H) ^ (n + 2) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hscale : P ^ (sigma - 1 / 2) ≤ P := by
      simpa using Real.rpow_le_rpow_of_exponent_le hP
        (show sigma - 1 / 2 ≤ 1 by linarith [hs.2])
    apply (le_div_iff₀ (pow_pos hH1 n)).mpr
    calc
      _ = (1 + H) ^ n *
          ‖primeDetectorIntegrand K V chi P t (idealVerticalPoint sigma r)‖ := by ring
      _ ≤ (1 + H) ^ (n + 2) *
          ‖primeDetectorIntegrand K V chi P t (idealVerticalPoint sigma r)‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ D * P ^ (sigma - 1 / 2) * M := hw
      _ ≤ D * P * M := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale hD) hM
  have hfaces :
      ‖(∫ r : ℝ in -H..H, primeDetectorIntegrand K V chi P t (idealVerticalPoint (3 / 2) r)) -
        (∫ r : ℝ in -H..H, primeDetectorIntegrand K V chi P t (idealVerticalPoint l r))‖ ≤
          4 * D * P * M / (1 + H) ^ n := by
    have hb := HighBinBoundary.finite_rectangle_bound (primeDetectorIntegrand K V chi P t)
      l (3 / 2) H (D * P * M / (1 + H) ^ n) hF
      (fun sigma hs => hface sigma hs (-H) (by simp [abs_of_nonneg hH]))
      (fun sigma hs => hface sigma hs H (abs_of_nonneg hH))
    have hwidth : |3 / 2 - l| ≤ (2 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
    apply hb.trans
    calc
      _ ≤ 2 * (D * P * M / (1 + H) ^ n) * 2 :=
        mul_le_mul_of_nonneg_left hwidth (by positivity)
      _ = _ := by ring
  have htail :
      ‖(∫ r : ℝ, primeDetectorIntegrand K V chi P t (idealVerticalPoint (3 / 2) r)) -
        (∫ r : ℝ in -H..H, primeDetectorIntegrand K V chi P t (idealVerticalPoint (3 / 2) r))‖ ≤
          D * initialLogDerivativeBound K * decayMass * P / (1 + H) ^ n := by
    rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H),
      ← integral_Icc_eq_integral_Ioc,
      ← setIntegral_compl measurableSet_Icc
        (integrable_primeDetectorIntegrand_initial K V chi hP0 t (by norm_num))]
    have hb := norm_setIntegral_decayWeight_le
      (fun r => primeDetectorIntegrand K V chi P t (idealVerticalPoint (3 / 2) r))
      (D * P * initialLogDerivativeBound K / (1 + H) ^ n)
      (by have := (initialLogDerivativeBound_pos K).le; positivity)
      (Icc (-H) H)ᶜ measurableSet_Icc.compl (by
        intro r hr
        have hHr : H ≤ |r| := by
          by_contra hn
          exact hr (abs_le.mp (lt_of_not_ge hn).le)
        have hw := primeDetectorIntegrand_weighted_norm_le K V chi hP0
          t (3 / 2) r D (initialLogDerivativeBound K) (n + 2) hD
          (hmellin (3 / 2) r hlr le_rfl)
          (continuedLogDerivative_initial_norm_le K chi t r)
        norm_num only [show (3 / 2 - 1 / 2 : ℝ) = 1 by ring, Real.rpow_one] at hw
        exact decay_weighted_tail_le hH hHr (norm_nonneg _) hw)
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hb
  let R : ℂ := ∫ r : ℝ, primeDetectorIntegrand K V chi P t (idealVerticalPoint (3 / 2) r)
  let R0 : ℂ := ∫ r : ℝ in -H..H,
    primeDetectorIntegrand K V chi P t (idealVerticalPoint (3 / 2) r)
  let L0 : ℂ := ∫ r : ℝ in -H..H,
    primeDetectorIntegrand K V chi P t (idealVerticalPoint l r)
  have htri : ‖R‖ ≤ ‖L0‖ + ‖R0 - L0‖ + ‖R - R0‖ := by
    calc
      ‖R‖ = ‖(L0 + (R0 - L0)) + (R - R0)‖ := by congr 1; ring
      _ ≤ ‖L0 + (R0 - L0)‖ + ‖R - R0‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right (norm_add_le _ _) _
  apply htri.trans
  calc
    _ ≤ (D * M * decayMass * P ^ (l - 1 / 2) +
        4 * D * P * M / (1 + H) ^ n) +
        D * initialLogDerivativeBound K * decayMass * P / (1 + H) ^ n :=
      add_le_add (add_le_add hleft hfaces) htail
    _ = _ := by ring

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The actual zero-free prime-window cap. The cutoff is independent of
the requested tail order. The input consists of the real upper-zero
detector and its height padding; Mellin inversion, uniform seminorms,
non-norm exclusion, L'/L control, all contour faces, higher prime powers
and the fixed deleted primes are discharged in the proof. -/
theorem exists_actual_primeWindow_cap
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (probe : ProbeData K S) (E : RowEulerData K S probe) (g : PrimeWindowGeometry)
    {e eps delta : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (heps : 0 < eps) (hdelta : 0 < delta) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, Z0 ≤ Z → ∀ d : ℝ, (1 / 16 : ℝ) ≤ d →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
      ∀ a H U t : ℝ, 1 / 2 ≤ a → a ≤ 1 → 0 ≤ H → H + |t| + 2 ≤ U →
      rowZeroBelow K S psi companions probe E u U (a + 2 * e) →
      ∀ chi ∈ physicalRowFamily K S psi companions probe E u,
      ∀ i : Fin g.slots, 2 ≤ primeScale g Z →
        ‖actualWindowPrimePolynomial K S g chi Z t i‖ ≤ C *
          ((1 + heckeConductorScale K chi ^ eps *
              (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps)) *
            ((primeScale g Z) ^ (a - 1 / 2 + 8 * e) +
              primeScale g Z / (1 + H) ^ n) + (primeScale g Z) ^ delta) := by
  obtain ⟨Clog, Z1, hClog, hZ1, hlog⟩ :=
    exists_uniform_actual_high_logDerivative_bound K S psi companions probe E he he' heps
  obtain ⟨Cerr, hCerr, hdetector⟩ := exists_actual_primeWindow_detector_error K S g hdelta
  have hFib := HeckeSkeleton.ActualCanonicalRowConsumers.rowCharacter_fiber_finite K S probe E
  let v : InfinitePlace K := Classical.choice inferInstance
  obtain ⟨Z2, hZ2, hnon⟩ :=
    HeckeSkeleton.HighNormBackgroundExclusion.high_rows_exclude_background_norm_twists
      K S probe E.rows hFib v (physicalBackgrounds K psi companions)
  refine ⟨max Z1 Z2, hZ1.trans (le_max_left _ _), ?_⟩
  intro n
  obtain ⟨D, hD, hmellin⟩ := exists_primeWindow_divideLog_mellin_bound g 0 1 (n + 2)
  let A0 : ℝ := D * Clog * decayMass
  let B0 : ℝ := D * initialLogDerivativeBound K * decayMass
  let A1 : ℝ := 4 * D * Clog
  let CI : ℝ := A0 + B0 + A1
  let k0 : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖
  have hA0 : 0 ≤ A0 := mul_nonneg (mul_nonneg hD.le hClog.le) decayMass_pos.le
  have hB0 : 0 ≤ B0 := mul_nonneg (mul_nonneg hD.le (initialLogDerivativeBound_pos K).le)
    decayMass_pos.le
  have hA1 : 0 ≤ A1 := by dsimp only [A1]; positivity
  have hCI : 0 ≤ CI := add_nonneg (add_nonneg hA0 hB0) hA1
  have hk0 : 0 ≤ k0 := norm_nonneg _
  refine ⟨Cerr + k0 * CI + 1, by have := mul_nonneg hk0 hCI; linarith, ?_⟩
  intro Z hZ d hd u hu a H U t ha ha1 hH hHU hbelow chi hchi i hP
  have hZZ1 : Z1 ≤ Z := (le_max_left _ _).trans hZ
  have hZZ2 : Z2 ≤ Z := (le_max_right _ _).trans hZ
  have hn := hnon Z hZZ2 d hd u hu
  have hchiNon : ∀ r : ℝ, chi ≠ heckeNormTwist K r := by
    obtain ⟨beta, hbeta, hdecomp⟩ := physical_member_background_decomposition
      K S psi companions probe E u chi hchi
    rcases hdecomp with hdecomp | hdecomp
    · rw [hdecomp]
      exact (hn beta hbeta).1
    · rw [hdecomp]
      exact (hn beta hbeta).2
  let P := primeScale g Z
  have hP1 : 1 < P := by dsimp only [P]; linarith
  have hP0 : 0 < P := by linarith
  let Vp := divideLogTest (g.weight i) (g.support_annular i) P hP1
  let G : ℝ := heckeConductorScale K chi ^ eps *
    (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps)
  have hQ : 0 < heckeConductorScale K chi := by
    unfold heckeConductorScale
    exact mul_pos (Nat.cast_pos.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)))
      (Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors (finiteConductor K chi)))
  have hU : 0 < 2 + U := by linarith [abs_nonneg t]
  have hG : 0 ≤ G := mul_nonneg (Real.rpow_nonneg hQ.le _) (Real.rpow_nonneg hU.le _)
  have hl : (1 / 2 : ℝ) ≤ a + 8 * e := by linarith
  have hlr : a + 8 * e ≤ (3 / 2 : ℝ) := by linarith
  have hF := primeDetectorIntegrand_differentiableOn_rectangle K Vp chi hchiNon hP0
    t (a + 8 * e) (3 / 2) H U (a + 2 * e) hlr hH (by linarith) (by linarith)
      (by linarith) (hbelow chi hchi)
  have hmellin' : ∀ sigma r : ℝ, a + 8 * e ≤ sigma → sigma ≤ 3 / 2 →
      (1 + |r|) ^ (n + 2) *
        ‖mellin Vp.toFun (idealVerticalPoint (sigma - 1 / 2) r)‖ ≤ D := by
    intro sigma r hs hs'
    exact hmellin i P hP (sigma - 1 / 2) r (by linarith) (by linarith)
  have hlog' : ∀ sigma r : ℝ, a + 8 * e ≤ sigma → sigma ≤ 3 / 2 → |r| ≤ H →
      ‖continuedLogDerivative K chi (idealVerticalPoint sigma r - (t : ℂ) * I)‖ ≤
        Clog * G := by
    intro sigma r hs hs' hr
    have hh : |r - t| ≤ H + |t| := by
      calc
        |r - t| ≤ |r| + |-t| := abs_add _ _
        _ = |r| + |t| := by rw [abs_neg]
        _ ≤ H + |t| := add_le_add_right hr _
    simpa only [G, mul_assoc] using hlog Z hZZ1 d hd u hu a (H + |t|) U ha ha1
      (add_nonneg hH (abs_nonneg t)) hHU hbelow chi hchi
      (idealVerticalPoint sigma r - (t : ℂ) * I) (by simpa using hs)
      (by simpa using hs') (by simpa [idealVerticalPoint] using hh)
  have hraw := primeDetector_initial_integral_norm_le K Vp chi P t (a + 8 * e) H D
    (Clog * G) n hP1.le hl hlr hH hD.le (mul_nonneg hClog.le hG) hF hmellin' hlog'
  let L : ℝ := P ^ (a - 1 / 2 + 8 * e)
  let R : ℝ := P / (1 + H) ^ n
  have hL : 0 ≤ L := Real.rpow_nonneg hP0.le _
  have hR : 0 ≤ R := div_nonneg hP0.le (pow_nonneg (by linarith) _)
  have hcompact :
      ‖∫ r : ℝ, primeDetectorIntegrand K Vp chi P t (idealVerticalPoint (3 / 2) r)‖ ≤
        CI * (1 + G) * (L + R) := by
    have heq : D * (Clog * G) * decayMass * P ^ (a + 8 * e - 1 / 2) +
        D * (initialLogDerivativeBound K * decayMass + 4 * (Clog * G)) * P /
          (1 + H) ^ n = A0 * G * L + (B0 + A1 * G) * R := by
      dsimp only [A0, B0, A1, L, R]
      rw [show a + 8 * e - 1 / 2 = a - 1 / 2 + 8 * e by ring]
      ring
    rw [heq] at hraw
    have hA0I : A0 ≤ CI := by dsimp only [CI]; linarith
    have hB0I : B0 ≤ CI := by dsimp only [CI]; linarith
    have hA1I : A1 ≤ CI := by dsimp only [CI]; linarith
    apply hraw.trans
    calc
      _ ≤ CI * G * L + (CI + CI * G) * R := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA0I hG) hL)
        (mul_le_mul_of_nonneg_right
          (add_le_add hB0I (mul_le_mul_of_nonneg_right hA1I hG)) hR)
      _ ≤ CI * (1 + G) * L + (CI + CI * G) * R := add_le_add_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : G ≤ 1 + G) hCI) hL) _
      _ = _ := by ring
  let I0 : ℂ := ∫ r : ℝ,
    primeDetectorIntegrand K Vp chi P t (idealVerticalPoint (3 / 2) r)
  have hdet :
      ‖actualWindowPrimePolynomial K S g chi Z t i + (2 * (Real.pi : ℂ))⁻¹ * I0‖ ≤
        Cerr * P ^ delta := by
    have h := hdetector chi Z t i hP1 (sigma := 3 / 2) (by norm_num)
    have hi : I0 = ∫ r : ℝ, annularMellinKernel Vp P (1 / 2) (3 / 2) r *
        heckeLogDerivative K chi (idealVerticalPoint (3 / 2) r - (t : ℂ) * I) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun r => by
        rw [primeDetectorIntegrand_vertical,
          continuedLogDerivative_eq_heckeLogDerivative K chi (by norm_num [idealVerticalPoint])])
    rw [hi]
    exact h
  have hmain : ‖(2 * (Real.pi : ℂ))⁻¹ * I0‖ ≤
      (k0 * CI) * ((1 + G) * (L + R)) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hcompact hk0).trans_eq (by ring)
  have hC1 : Cerr ≤ Cerr + k0 * CI + 1 := by nlinarith [mul_nonneg hk0 hCI]
  have hC2 : k0 * CI ≤ Cerr + k0 * CI + 1 := by linarith
  have hPd : 0 ≤ P ^ delta := Real.rpow_nonneg hP0.le _
  have hX : 0 ≤ (1 + G) * (L + R) := mul_nonneg (by linarith) (add_nonneg hL hR)
  calc
    ‖actualWindowPrimePolynomial K S g chi Z t i‖ =
        ‖(actualWindowPrimePolynomial K S g chi Z t i + (2 * (Real.pi : ℂ))⁻¹ * I0) -
          (2 * (Real.pi : ℂ))⁻¹ * I0‖ := by rw [add_sub_cancel_right]
    _ ≤ _ := norm_sub_le _ _
    _ ≤ Cerr * P ^ delta + (k0 * CI) * ((1 + G) * (L + R)) := add_le_add hdet hmain
    _ ≤ (Cerr + k0 * CI + 1) * P ^ delta +
        (Cerr + k0 * CI + 1) * ((1 + G) * (L + R)) := add_le_add
      (mul_le_mul_of_nonneg_right hC1 hPd) (mul_le_mul_of_nonneg_right hC2 hX)
    _ = _ := by dsimp only [P, G, L, R]; ring

end HighBinVerified.NormFormPrimeContour

#print axioms HighBinVerified.NormFormPrimeContour.primeDetectorIntegrand_differentiableOn_rectangle
#print axioms HighBinVerified.NormFormPrimeContour.continuedLogDerivative_initial_norm_le
#print axioms HighBinVerified.NormFormPrimeContour.exists_actual_primeWindow_cap
