import HeckeSkeleton.ThetaKernel.TestMellin
import HeckeSkeleton.ThetaKernel.Shift
import HeckeGeneral.Analysis.IdealDerivativeSmoothing
import HeckeGeneral.Analysis.MomentInputs
import Mathlib.Analysis.MellinInversion

/-!
# Mellin inversion of the actual finite annular ideal polynomial

Every compact smooth annular test has an integrable Mellin transform on
every vertical line.  The Euler-derivative estimate proves this analytic
hypothesis, after which Mathlib's genuine Mellin inversion evaluates each
ideal term.  The already proved absolutely convergent ideal-series
interchange then gives the ordinary Hecke polynomial formula on Re(s)>1.

The finite support below contains exactly the nonzero test values at
actual ideal norms.  No final reflection formula, contour identity, or
uniform moment bound is assumed.  Finite deleted Euler factors and the
leftward functional-equation contour are subsequent operations.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped BigOperators Classical Topology

/-- The actual Mellin transform has arbitrary polynomial vertical decay. -/
theorem smoothAnnular_mellin_vertical_decay (V : SmoothAnnularTest)
    (J : ℕ) (σ t : ℝ) :
    ‖mellin V.toFun (idealVerticalPoint σ t)‖ ≤
      (2 ^ J * (Iint V 0 (-σ) + Iint V J (-σ))) *
        (1 + |t|) ^ (-(J : ℝ)) := by
  have hw : ((-σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I =
      -idealVerticalPoint σ t := by
    unfold idealVerticalPoint
    push_cast
    ring
  have hm := pow_mul_norm_mellin_le V J (-σ) (-t)
  rw [hw, norm_neg, neg_neg] at hm
  have him : |t| ≤ ‖idealVerticalPoint σ t‖ := by
    simpa only [idealVerticalPoint_im] using
      Complex.abs_im_le_norm (idealVerticalPoint σ t)
  have hp : (1 + |t|) ^ J * ‖mellin V.toFun (idealVerticalPoint σ t)‖ ≤
      2 ^ J * (Iint V 0 (-σ) + Iint V J (-σ)) :=
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith) J) (norm_nonneg _)).trans hm
  have ht : 0 < 1 + |t| := by positivity
  have hd : ‖mellin V.toFun (idealVerticalPoint σ t)‖ ≤
      (2 ^ J * (Iint V 0 (-σ) + Iint V J (-σ))) / (1 + |t|) ^ J :=
    (le_div_iff₀ (pow_pos ht J)).2 (by
    simpa only [mul_comm] using hp)
  simpa only [Real.rpow_neg ht.le, Real.rpow_natCast, div_eq_mul_inv] using hd

/-- Vertical integrability is derived from order-two Euler decay. -/
theorem smoothAnnular_mellin_verticalIntegrable (V : SmoothAnnularTest) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin V.toFun) σ := by
  have hdiff : Differentiable ℂ (mellin V.toFun) := by
    simpa only [Function.comp_def, neg_neg] using
      (differentiable_mellin_neg V).comp differentiable_neg
  have hc : Continuous (fun t : ℝ => mellin V.toFun (idealVerticalPoint σ t)) :=
    hdiff.continuous.comp (continuous_idealVerticalPoint σ)
  change Integrable (fun t : ℝ => mellin V.toFun (idealVerticalPoint σ t))
  apply ((integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul
    (2 ^ (2 : ℕ) * (Iint V 0 (-σ) + Iint V 2 (-σ)))).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (smoothAnnular_mellin_vertical_decay V 2 σ)

/-- Genuine inversion for every positive norm ratio and every real line. -/
theorem smoothAnnular_mellin_inversion (V : SmoothAnnularTest)
    (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    (2 * (Real.pi : ℂ))⁻¹ *
      (∫ t : ℝ, (y : ℂ) ^ (-idealVerticalPoint σ t) *
        mellin V.toFun (idealVerticalPoint σ t)) = V.toFun y := by
  have h := mellinInv_mellin_eq σ V.toFun hy
    ((good_toFun V).integrableOn_mellin (σ : ℂ))
    (smoothAnnular_mellin_verticalIntegrable V σ) V.smooth.continuous.continuousAt
  simpa only [mellinInv, idealVerticalPoint, one_div, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul] using h

variable (K : Type) [Field K] [NumberField K]

/-- A finite norm envelope filtered to the literal nonzero annular values. -/
def annularIdealSupport (V : SmoothAnnularTest) (X : ℝ) : Finset (NonzeroIdeal K) :=
  ((Ideal.finite_setOfPred_absNorm_le₀ (S := 𝓞 K) (Nat.ceil (V.upper * X))).toFinset).filter
    (fun I => V.toFun (idealNorm K I / X) ≠ 0)

theorem mem_annularIdealSupport (V : SmoothAnnularTest) {X : ℝ} (hX : 0 < X)
    (I : NonzeroIdeal K) :
    I ∈ annularIdealSupport K V X ↔ V.toFun (idealNorm K I / X) ≠ 0 := by
  simp only [annularIdealSupport, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have hn : idealNorm K I ≤ V.upper * X :=
      (div_le_iff₀ hX).1 (V.support h).2
    change (I.val.absNorm : ℝ) ≤ V.upper * X at hn
    exact_mod_cast hn.trans (Nat.le_ceil (V.upper * X))

/-- The actual finite annular sum with coefficients still explicit. -/
def annularIdealSum (a : NonzeroIdeal K → ℂ) (V : SmoothAnnularTest) (X : ℝ) : ℂ :=
  ∑ I ∈ annularIdealSupport K V X, a I * V.toFun (idealNorm K I / X)

theorem annularIdealSum_eq_tsum (a : NonzeroIdeal K → ℂ)
    (V : SmoothAnnularTest) {X : ℝ} (hX : 0 < X) :
    annularIdealSum K a V X = ∑' I, a I * V.toFun (idealNorm K I / X) := by
  unfold annularIdealSum
  symm
  apply tsum_eq_sum
  intro I hI
  have hz : V.toFun (idealNorm K I / X) = 0 := by
    by_contra h
    exact hI ((mem_annularIdealSupport K V hX I).2 h)
  rw [hz, mul_zero]

private theorem scaled_ideal_cpow (X : ℝ) (hX : 0 < X)
    (I : NonzeroIdeal K) (s : ℂ) :
    (X : ℂ) ^ s * (idealNorm K I : ℂ) ^ (-s) =
      ((idealNorm K I / X : ℝ) : ℂ) ^ (-s) := by
  have hI := idealNorm_pos K I
  have hratio : 0 < idealNorm K I / X := div_pos hI hX
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hI.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hratio.ne'),
    ← Complex.ofReal_log hX.le, ← Complex.ofReal_log hI.le,
    ← Complex.ofReal_log hratio.le, Real.log_div hI.ne' hX.ne', ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- One real Mellin inversion evaluates each actual ideal term. -/
theorem integral_annularMellin_idealTerm (a : NonzeroIdeal K → ℂ)
    (V : SmoothAnnularTest) (σ : ℝ) {X : ℝ} (hX : 0 < X) (I : NonzeroIdeal K) :
    (2 * (Real.pi : ℂ))⁻¹ *
      (∫ t : ℝ, (mellin V.toFun (idealVerticalPoint σ t) *
        (X : ℂ) ^ idealVerticalPoint σ t) *
          dirichletTerm (idealNorm K) a (idealVerticalPoint σ t) I) =
      a I * V.toFun (idealNorm K I / X) := by
  have he (t : ℝ) :
      (mellin V.toFun (idealVerticalPoint σ t) * (X : ℂ) ^ idealVerticalPoint σ t) *
        dirichletTerm (idealNorm K) a (idealVerticalPoint σ t) I =
      a I * (((idealNorm K I / X : ℝ) : ℂ) ^ (-idealVerticalPoint σ t) *
        mellin V.toFun (idealVerticalPoint σ t)) := by
    unfold dirichletTerm
    rw [← scaled_ideal_cpow K X hX I]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  calc
    _ = a I * ((2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, ((idealNorm K I / X : ℝ) : ℂ) ^ (-idealVerticalPoint σ t) *
          mellin V.toFun (idealVerticalPoint σ t)) := by ring
    _ = _ := by rw [smoothAnnular_mellin_inversion V σ (div_pos (idealNorm_pos K I) hX)]

/-- The contour of the actual ideal series is an integrable function. -/
theorem integrable_annularMellin_idealSeries (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (V : SmoothAnnularTest) {σ X : ℝ}
    (hσ : 1 < σ) (hX : 0 < X) :
    Integrable (fun t : ℝ => (mellin V.toFun (idealVerticalPoint σ t) *
      (X : ℂ) ^ idealVerticalPoint σ t) *
        idealDirichletSeries K a (idealVerticalPoint σ t)) := by
  simpa only [idealLogSeries_zero, idealVerticalPoint] using
    integrable_kernel_mul_idealLogSeries K a ha 0 hσ
      (integrable_kernel_mul_vertical_cpow (smoothAnnular_mellin_verticalIntegrable V σ) hX σ)

/-- Absolute ideal summation and real Mellin inversion give the actual
finite polynomial; there is no independent contour identity hypothesis. -/
theorem annularIdealSum_mellin (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (V : SmoothAnnularTest) {σ X : ℝ}
    (hσ : 1 < σ) (hX : 0 < X) :
    annularIdealSum K a V X = (2 * (Real.pi : ℂ))⁻¹ *
      (∫ t : ℝ, (mellin V.toFun (idealVerticalPoint σ t) *
        (X : ℂ) ^ idealVerticalPoint σ t) *
          idealDirichletSeries K a (idealVerticalPoint σ t)) := by
  have hexchange :
      (∫ t : ℝ, (mellin V.toFun (idealVerticalPoint σ t) *
        (X : ℂ) ^ idealVerticalPoint σ t) *
          idealDirichletSeries K a (idealVerticalPoint σ t)) =
      ∑' I, ∫ t : ℝ, (mellin V.toFun (idealVerticalPoint σ t) *
        (X : ℂ) ^ idealVerticalPoint σ t) *
          dirichletTerm (idealNorm K) a (idealVerticalPoint σ t) I := by
    simpa only [idealLogSeries_zero, idealLogTerm_zero, idealVerticalPoint] using
      integral_mellin_kernel_mul_idealLogSeries K a ha 0 hσ
        (smoothAnnular_mellin_verticalIntegrable V σ) hX
  rw [annularIdealSum_eq_tsum K a V hX, hexchange, ← tsum_mul_left]
  apply tsum_congr
  intro I
  exact (integral_annularMellin_idealTerm K a V σ hX I).symm

/-- Specialization to the literal zero-extended coefficients of an actual
Hecke character.  No unramified or nonprincipal condition is needed yet. -/
theorem annularHeckeSum_mellin (χ : HeckeCharacter K)
    (V : SmoothAnnularTest) {σ X : ℝ} (hσ : 1 < σ) (hX : 0 < X) :
    annularIdealSum K (heckeIdealCoefficient K χ) V X =
      (2 * (Real.pi : ℂ))⁻¹ *
        (∫ t : ℝ, (mellin V.toFun (idealVerticalPoint σ t) *
          (X : ℂ) ^ idealVerticalPoint σ t) * heckeLSeries K χ (idealVerticalPoint σ t)) :=
  annularIdealSum_mellin K (heckeIdealCoefficient K χ)
    (norm_heckeIdealCoefficient_le_one K χ) V hσ hX

end HeckeSkeleton.Moments.EngineInduction
