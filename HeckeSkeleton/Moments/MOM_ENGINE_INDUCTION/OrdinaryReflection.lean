import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.AnnularReflection

/-!
# The actual ordinary reflected norm profile

The negative contour proved in `AnnularReflection` is changed to the dual
right half-plane.  Its real-frequency kernel is proved integrable from
the ordinary Gamma bound and the actual compact test's Euler decay.
Absolute ideal summation therefore yields the genuine dual norm-profile
sum.  The conductor scale is the existing discriminant times finite
conductor norm.  No reflection identity is supplied as a hypothesis.

The reflected profile need not have compact support.  Its absolutely
convergent whole ideal sum is retained here; uniform finite truncation
and the original deleted Euler factors require later constructions.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeGammaReciprocal
open HeckeSkeleton.HeckeUniformStripGrowth
open scoped BigOperators Classical Topology

variable (K : Type) [Field K] [NumberField K]

/-- The actual ordinary Gamma ratio and the original test's Mellin
transform, evaluated on the dual line Re(w)=1+δ. -/
def ordinaryReflectionKernel (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (δ t : ℝ) : ℂ :=
  let s := 1 - idealVerticalPoint (1 + δ) t
  mellin V.toFun s * ((canonicalHeckeGammaProfile K χ s)⁻¹ *
    canonicalHeckeGammaProfile K χ⁻¹ (1 - s))

private theorem one_sub_dual_vertical (δ t : ℝ) :
    1 - idealVerticalPoint (1 + δ) t = idealVerticalPoint (-δ) (-t) := by
  unfold idealVerticalPoint
  push_cast
  ring

theorem continuous_ordinaryReflectionKernel (χ : HeckeCharacter K)
    (V : SmoothAnnularTest) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (ordinaryReflectionKernel K χ V δ) := by
  have hs : Continuous (fun t : ℝ => 1 - idealVerticalPoint (1 + δ) t) :=
    continuous_const.sub (continuous_idealVerticalPoint (1 + δ))
  have hM : Differentiable ℂ (mellin V.toFun) := by
    simpa only [Function.comp_def, neg_neg] using
      (differentiable_mellin_neg V).comp differentiable_neg
  have hGinv : Continuous (fun t : ℝ =>
      (canonicalHeckeGammaProfile K χ⁻¹ (1 - (1 - idealVerticalPoint (1 + δ) t)))⁻¹) :=
    (differentiable_canonicalHeckeGammaReciprocal K χ⁻¹).continuous.comp
      (continuous_const.sub hs)
  have hG : Continuous (fun t : ℝ =>
      canonicalHeckeGammaProfile K χ⁻¹ (1 - (1 - idealVerticalPoint (1 + δ) t))) := by
    have h := hGinv.inv₀ (fun t => inv_ne_zero
      (canonicalHeckeGammaProfile_ne_zero_of_re_pos K χ⁻¹ (by
        simp only [Complex.sub_re, Complex.one_re, idealVerticalPoint_re]
        linarith)))
    simpa only [inv_inv] using h
  exact (hM.continuous.comp hs).mul
    (((differentiable_canonicalHeckeGammaReciprocal K χ).continuous.comp hs).mul hG)

/-- Actual polynomial Gamma growth and Euler decay prove the required
kernel integrability, even at reciprocal-Gamma zero locations. -/
theorem integrable_ordinaryReflectionKernel
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) :
    Integrable (ordinaryReflectionKernel K χ V δ) := by
  obtain ⟨G, hGpos, hG⟩ := fixedType_gamma_multiplier_left_bound K hcomplex
    (fun v => heckeRadialParameter K v χ) (heckeArchWeight K χ) δ hδ hδsmall
  let k : ℕ := 2 * Fintype.card (InfinitePlace K)
  let B : ℝ := 2 ^ (k + 2) * (Iint V 0 δ + Iint V (k + 2) δ)
  have hB : 0 ≤ B := mul_nonneg (by positivity)
    (add_nonneg (Iint_nonneg V _ _) (Iint_nonneg V _ _))
  apply ((integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul
    (B * G * 2 ^ k)).mono' (continuous_ordinaryReflectionKernel K χ V hδ).aestronglyMeasurable
  filter_upwards [] with t
  let s := 1 - idealVerticalPoint (1 + δ) t
  let T : ℝ := 1 + |t|
  have hT : 0 < T := by dsimp [T]; positivity
  have hsre : s.re = -δ := by simp [s, idealVerticalPoint]; ring
  have hsim : |s.im| = |t| := by simp [s, idealVerticalPoint]
  have hgamma : ‖(canonicalHeckeGammaProfile K χ s)⁻¹ *
      canonicalHeckeGammaProfile K χ⁻¹ (1 - s)‖ ≤ G * (2 + |t|) ^ k := by
    rw [canonicalHeckeGammaProfile_inv, canonicalHeckeGammaProfile, mul_comm]
    simpa only [hsim, k] using hG s hsre
  have hgamma' : ‖(canonicalHeckeGammaProfile K χ s)⁻¹ *
      canonicalHeckeGammaProfile K χ⁻¹ (1 - s)‖ ≤ (G * 2 ^ k) * T ^ k := by
    have hp : (2 + |t|) ^ k ≤ 2 ^ k * T ^ k := by
      calc
        _ ≤ (2 * T) ^ k := pow_le_pow_left₀ (by positivity)
          (by dsimp [T]; linarith [abs_nonneg t]) k
        _ = _ := mul_pow _ _ _
    exact (hgamma.trans (mul_le_mul_of_nonneg_left hp hGpos.le)).trans_eq (by ring)
  have hM : ‖mellin V.toFun s‖ ≤ B * T ^ (-((k + 2 : ℕ) : ℝ)) := by
    simpa only [s, one_sub_dual_vertical, neg_neg, abs_neg, B, T] using
      smoothAnnular_mellin_vertical_decay V (k + 2) (-δ) (-t)
  have he : T ^ (-((k + 2 : ℕ) : ℝ)) * T ^ k = T ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hT]
    congr 1
    push_cast
    ring
  calc
    ‖ordinaryReflectionKernel K χ V δ t‖ = ‖mellin V.toFun s‖ *
        ‖(canonicalHeckeGammaProfile K χ s)⁻¹ *
          canonicalHeckeGammaProfile K χ⁻¹ (1 - s)‖ := norm_mul _ _
    _ ≤ (B * T ^ (-((k + 2 : ℕ) : ℝ))) * ((G * 2 ^ k) * T ^ k) :=
      mul_le_mul hM hgamma' (norm_nonneg _) (mul_nonneg hB (Real.rpow_nonneg hT.le _))
    _ = (B * G * 2 ^ k) * (1 + |t|) ^ (-(2 : ℝ)) := by
      calc
        _ = (B * G * 2 ^ k) * (T ^ (-((k + 2 : ℕ) : ℝ)) * T ^ k) := by ring
        _ = _ := by rw [he]

/-- A genuine inverse-Mellin norm profile on the dual line. -/
def ordinaryReflectedProfile (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (δ y : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t : ℝ, (y : ℂ) ^ (-idealVerticalPoint (1 + δ) t) *
      ordinaryReflectionKernel K χ V δ t

/-- At each positive dual norm ratio the defining profile integral is
absolutely convergent, independently of the arithmetic coefficient. -/
theorem integrable_ordinaryReflectedProfile
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ y : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hy : 0 < y) :
    Integrable (fun t : ℝ => (y : ℂ) ^ (-idealVerticalPoint (1 + δ) t) *
      ordinaryReflectionKernel K χ V δ t) := by
  have hc : Continuous (fun t : ℝ => (y : ℂ) ^ (-idealVerticalPoint (1 + δ) t)) :=
    (differentiable_neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).continuous.comp
        (continuous_idealVerticalPoint (1 + δ))
  have hb : ∀ᵐ t : ℝ, ‖(y : ℂ) ^ (-idealVerticalPoint (1 + δ) t)‖ ≤ y ^ (-(1 + δ)) := by
    filter_upwards [] with t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.neg_re, idealVerticalPoint_re]
  have h := (integrable_ordinaryReflectionKernel K hcomplex χ V hδ hδsmall).mul_bdd
    hc.aestronglyMeasurable hb
  simpa only [mul_comm] using h

private theorem reflected_scale_cpow {X q : ℝ} (hX : 0 < X) (hq : 0 < q) (s : ℂ) :
    (X : ℂ) ^ s * (q : ℂ) ^ (-s) = ((q / X : ℝ) : ℂ) ^ (-s) := by
  have hratio := div_pos hq hX
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hratio.ne'),
    ← Complex.ofReal_log hX.le, ← Complex.ofReal_log hq.le,
    ← Complex.ofReal_log hratio.le, Real.log_div hq.ne' hX.ne', ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The literal dual ideal term is the inverse profile at its norm ratio. -/
theorem integral_ordinaryReflectedProfile_term (χ : HeckeCharacter K)
    (V : SmoothAnnularTest) (δ : ℝ) {Y : ℝ} (hY : 0 < Y) (I : NonzeroIdeal K) :
    (2 * (Real.pi : ℂ))⁻¹ *
      (∫ t : ℝ, (ordinaryReflectionKernel K χ V δ t *
        (Y : ℂ) ^ idealVerticalPoint (1 + δ) t) *
          dirichletTerm (idealNorm K) (heckeIdealCoefficient K χ⁻¹)
            (idealVerticalPoint (1 + δ) t) I) =
      heckeIdealCoefficient K χ⁻¹ I * ordinaryReflectedProfile K χ V δ (idealNorm K I / Y) := by
  unfold ordinaryReflectedProfile
  calc
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, heckeIdealCoefficient K χ⁻¹ I *
          (((idealNorm K I / Y : ℝ) : ℂ) ^ (-idealVerticalPoint (1 + δ) t) *
            ordinaryReflectionKernel K χ V δ t) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      unfold dirichletTerm
      rw [← reflected_scale_cpow hY (idealNorm_pos K I)]
      ring
    _ = _ := by rw [integral_const_mul]; ring

/-- The complete dual ideal sum converges absolutely, before truncation. -/
theorem summable_ordinaryReflectedIdealTerms
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ Y : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hY : 0 < Y) :
    Summable (fun I : NonzeroIdeal K =>
      ‖heckeIdealCoefficient K χ⁻¹ I * ordinaryReflectedProfile K χ V δ (idealNorm K I / Y)‖) := by
  have hk := integrable_ordinaryReflectionKernel K hcomplex χ V hδ hδsmall
  have hks := integrable_kernel_mul_vertical_cpow hk hY (1 + δ)
  have hs := summable_integral_norm_kernel_mul_idealLogTerm K (heckeIdealCoefficient K χ⁻¹)
    (norm_heckeIdealCoefficient_le_one K χ⁻¹) 0 (show 1 < 1 + δ by linarith) hks
  simp only [idealLogTerm_zero] at hs
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun I => ?_) (hs.mul_left ‖(2 * (Real.pi : ℂ))⁻¹‖)
  rw [← integral_ordinaryReflectedProfile_term K χ V δ hY I, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)

/-- The positive dual contour equals that actual absolutely convergent sum. -/
theorem ordinaryReflectedProfile_sum
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ Y : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hY : 0 < Y) :
    (2 * (Real.pi : ℂ))⁻¹ *
      (∫ t : ℝ, (ordinaryReflectionKernel K χ V δ t *
        (Y : ℂ) ^ idealVerticalPoint (1 + δ) t) *
          heckeLSeries K χ⁻¹ (idealVerticalPoint (1 + δ) t)) =
      ∑' I, heckeIdealCoefficient K χ⁻¹ I *
        ordinaryReflectedProfile K χ V δ (idealNorm K I / Y) := by
  have hexchange := integral_mellin_kernel_mul_idealLogSeries K (heckeIdealCoefficient K χ⁻¹)
    (norm_heckeIdealCoefficient_le_one K χ⁻¹) 0 (show 1 < 1 + δ by linarith)
    (integrable_ordinaryReflectionKernel K hcomplex χ V hδ hδsmall) hY
  simp only [idealLogSeries_zero, idealLogTerm_zero] at hexchange
  change (2 * (Real.pi : ℂ))⁻¹ *
    (∫ t : ℝ, (ordinaryReflectionKernel K χ V δ t *
      (Y : ℂ) ^ idealVerticalPoint (1 + δ) t) *
        idealDirichletSeries K (heckeIdealCoefficient K χ⁻¹) (idealVerticalPoint (1 + δ) t)) = _
  rw [hexchange, ← tsum_mul_left]
  exact tsum_congr (integral_ordinaryReflectedProfile_term K χ V δ hY)

private theorem conductor_reflection_cpow {X Q : ℝ} (hX : 0 < X) (hQ : 0 < Q)
    (s : ℂ) :
    (X : ℂ) ^ s / (Q : ℂ) ^ (s - 1 / 2) =
      ((X : ℂ) / (Q : ℂ) ^ (1 / 2 : ℂ)) * ((Q / X : ℝ) : ℂ) ^ (1 - s) := by
  have hratio := div_pos hQ hX
  have hc (x : ℝ) (hx : 0 < x) (z : ℂ) :
      (x : ℂ) ^ z = Complex.exp ((Real.log x : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      ← Complex.ofReal_log hx.le]
  have hxexp : Complex.exp (Real.log X : ℂ) = (X : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hX]
  rw [hc X hX s, hc Q hQ (s - 1 / 2), hc Q hQ (1 / 2), hc (Q / X) hratio (1 - s),
    Real.log_div hQ.ne' hX.ne', Complex.ofReal_sub]
  calc
    _ = Complex.exp ((Real.log X : ℂ) * s - (Real.log Q : ℂ) * (s - 1 / 2)) :=
      (Complex.exp_sub _ _).symm
    _ = Complex.exp ((Real.log X : ℂ) - (Real.log Q : ℂ) * (1 / 2)) *
        Complex.exp (((Real.log Q : ℂ) - (Real.log X : ℂ)) * (1 - s)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    _ = _ := by rw [Complex.exp_sub, hxexp]

/-- Ordinary reflection of the real finite Hecke polynomial, with its
actual conductor scale and actual dual norm profile. -/
theorem annularHeckeSum_reflection
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (V : SmoothAnnularTest) {X δ : ℝ} (hX : 0 < X)
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧
      annularIdealSum K (heckeIdealCoefficient K χ) V X =
        (ε⁻¹ * (X : ℂ) / (heckeConductorScale K χ : ℂ) ^ (1 / 2 : ℂ)) *
          ∑' I, heckeIdealCoefficient K χ⁻¹ I * ordinaryReflectedProfile K χ V δ
            (idealNorm K I / (heckeConductorScale K χ / X)) := by
  obtain ⟨ε, hε, hQ, hFE⟩ := exists_uncompleted_functionalEquation_left_of_one K χ hχ
  refine ⟨ε, hε, ?_⟩
  let A : ℂ := ε⁻¹ * (X : ℂ) / (heckeConductorScale K χ : ℂ) ^ (1 / 2 : ℂ)
  have hpoint (t : ℝ) :
      annularHeckeContour K χ V X (idealVerticalPoint (-δ) (-t)) =
        A * ((ordinaryReflectionKernel K χ V δ t *
          ((heckeConductorScale K χ / X : ℝ) : ℂ) ^ idealVerticalPoint (1 + δ) t) *
            heckeLSeries K χ⁻¹ (idealVerticalPoint (1 + δ) t)) := by
    let s := 1 - idealVerticalPoint (1 + δ) t
    have hs : idealVerticalPoint (-δ) (-t) = s := (one_sub_dual_vertical δ t).symm
    have hsre : s.re < 1 := by simp [s, idealVerticalPoint]; linarith
    have hdual : 1 - s = idealVerticalPoint (1 + δ) t := by dsimp [s]; ring
    rw [hs, annularHeckeContour, hFE s hsre, hdual,
      heckeContinuation_eq_series K χ⁻¹ (by simp only [idealVerticalPoint_re]; linarith)]
    have hp := conductor_reflection_cpow hX hQ s
    rw [hdual] at hp
    calc
      _ = ε⁻¹ * ((X : ℂ) ^ s / (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2)) *
          (mellin V.toFun s * ((canonicalHeckeGammaProfile K χ s)⁻¹ *
            canonicalHeckeGammaProfile K χ⁻¹ (idealVerticalPoint (1 + δ) t))) *
              heckeLSeries K χ⁻¹ (idealVerticalPoint (1 + δ) t) := by
        simp only [div_eq_mul_inv, mul_inv]
        ring
      _ = _ := by
        rw [hp]
        dsimp [A, ordinaryReflectionKernel]
        rw [show 1 - (1 - idealVerticalPoint (1 + δ) t) =
          idealVerticalPoint (1 + δ) t by ring]
        dsimp [s]
        ring
  calc
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, annularHeckeContour K χ V X (idealVerticalPoint (-δ) t) :=
      annularHeckeSum_shift K hcomplex χ hχ V hX hδ hδsmall
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, annularHeckeContour K χ V X (idealVerticalPoint (-δ) (-t)) := by
      congr 1
      exact (integral_neg_eq_self _ volume).symm
    _ = A * ((2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, (ordinaryReflectionKernel K χ V δ t *
          ((heckeConductorScale K χ / X : ℝ) : ℂ) ^ idealVerticalPoint (1 + δ) t) *
            heckeLSeries K χ⁻¹ (idealVerticalPoint (1 + δ) t)) := by
      simp_rw [hpoint]
      rw [integral_const_mul]
      ring
    _ = _ := by
      rw [ordinaryReflectedProfile_sum K hcomplex χ V hδ hδsmall (div_pos hQ hX)]

end HeckeSkeleton.Moments.EngineInduction
