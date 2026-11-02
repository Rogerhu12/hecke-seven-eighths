import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.AnnularMellinSeparation
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PowerWindowSeminorm

/-!
# Uniform Euler control of one fixed Mellin separation window

The cutoff is a fixed genuine smooth annular test.  Only the imaginary
power varies with the frequency.  Logarithmic coordinates turn Euler
differentiation into ordinary differentiation of the fixed log cutoff
times a unit-modulus exponential.  Finite Leibniz sums therefore give
the exact polynomial frequency growth required by the strict-step
preprocessing.  The integral weight is bounded on the same fixed annulus.

Every coefficient is selected before the frequency and any moving source
profile or arithmetic row.  No polynomial or moment estimate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators ContDiff Topology

private def mellinWindowLogCutoff (B : SmoothAnnularTest) (x : ℝ) : ℂ :=
  B.toFun (Real.exp x)

private theorem mellinWindowLogCutoff_smooth (B : SmoothAnnularTest) :
    ContDiff ℝ ∞ (mellinWindowLogCutoff B) := B.smooth.comp Real.contDiff_exp

private def mellinWindowLogExp (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (z * (x : ℂ))

private theorem mellinWindowLogExp_smooth (z : ℂ) :
    ContDiff ℝ ∞ (mellinWindowLogExp z) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

private theorem mellinWindowLogExp_deriv (z : ℂ) (x : ℝ) :
    HasDerivAt (mellinWindowLogExp z) (z * mellinWindowLogExp z x) x := by
  have hlinear : HasDerivAt (fun y : ℝ => z * (y : ℂ)) z x := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul z
  simpa only [mellinWindowLogExp, mul_comm] using! hlinear.cexp

private theorem mellinWindowLogExp_iteratedDeriv (z : ℂ) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (mellinWindowLogExp z) x = z ^ j * mellinWindowLogExp z x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hd : deriv (mellinWindowLogExp z) = fun x => z * mellinWindowLogExp z x :=
      funext (fun x => (mellinWindowLogExp_deriv z x).deriv)
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih, pow_succ]
    ring

private theorem mellinWindow_phase_norm (frequency : ℝ) :
    ‖-idealVerticalPoint 0 frequency‖ = |frequency| := by
  simp only [idealVerticalPoint, Complex.ofReal_zero, zero_add, norm_neg,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]

private theorem mellinWindow_logExp_norm (frequency x : ℝ) :
    ‖mellinWindowLogExp (-idealVerticalPoint 0 frequency) x‖ = 1 := by
  simp only [mellinWindowLogExp, Complex.norm_exp, Complex.mul_re,
    Complex.neg_re, idealVerticalPoint_re, Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, zero_mul, mul_zero, sub_zero, Real.exp_zero]

private theorem annularMellinWindow_single_euler_bound (B : SmoothAnnularTest) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ frequency : ℝ, ∀ y ∈ Icc B.lower B.upper,
      ‖eulerDerivativeOrder j (annularMellinWindow B frequency) y‖ ≤
        C * (1 + |frequency|) ^ j := by
  let Q : ℝ → ℝ := fun x => ∑ k ∈ Finset.range (j + 1),
    (j.choose k : ℝ) * ‖iteratedDeriv k (mellinWindowLogCutoff B) x‖
  have hQ : Continuous Q := by
    dsimp only [Q]
    exact continuous_finset_sum _ (fun k _ => continuous_const.mul
      ((mellinWindowLogCutoff_smooth B).continuous_iteratedDeriv k (by simp)).norm)
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact
    (Icc (Real.log B.lower) (Real.log B.upper))).bddAbove_image hQ.continuousOn
  refine ⟨|M| + 1, by positivity, fun frequency y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le B.lower_pos hy.1
  have hylog : Real.log y ∈ Icc (Real.log B.lower) (Real.log B.upper) :=
    ⟨Real.log_le_log B.lower_pos hy.1, Real.log_le_log hy0 hy.2⟩
  have hQbound : Q (Real.log y) ≤ |M| + 1 :=
    (hM (Set.mem_image_of_mem _ hylog)).trans (by linarith [le_abs_self M])
  let z : ℂ := -idealVerticalPoint 0 frequency
  have heq : (fun x : ℝ => annularMellinWindow B frequency (Real.exp x)) =
      fun x => mellinWindowLogCutoff B x * mellinWindowLogExp z x := by
    funext x
    dsimp only [annularMellinWindow, profilePower, mellinWindowLogCutoff,
      mellinWindowLogExp, z]
    rw [Real.log_exp, mul_comm (x : ℂ)]
  have heuler := eulerDerivativeOrder_log_coordinate (annularMellinWindowTest B frequency)
    j (Real.log y)
  change eulerDerivativeOrder j (annularMellinWindow B frequency) (Real.exp (Real.log y)) =
    iteratedDeriv j (fun x : ℝ => annularMellinWindow B frequency (Real.exp x)) (Real.log y)
    at heuler
  rw [Real.exp_log hy0, heq] at heuler
  have hprod := norm_iteratedFDeriv_mul_le (mellinWindowLogCutoff_smooth B)
    (mellinWindowLogExp_smooth z) (Real.log y) (n := j) (by simp)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hprod
  have hpower (k : ℕ) :
      ‖iteratedDeriv (j - k) (mellinWindowLogExp z) (Real.log y)‖ ≤
        (1 + |frequency|) ^ j := by
    rw [mellinWindowLogExp_iteratedDeriv, norm_mul, norm_pow]
    dsimp only [z]
    rw [mellinWindow_phase_norm, mellinWindow_logExp_norm, mul_one]
    have hfrequency : |frequency| ≤ 1 + |frequency| := by linarith
    exact (pow_le_pow_left₀ (abs_nonneg frequency) hfrequency _).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg frequency]) (Nat.sub_le _ _))
  rw [heuler]
  apply hprod.trans
  calc
    _ ≤ ∑ k ∈ Finset.range (j + 1),
        ((j.choose k : ℝ) * ‖iteratedDeriv k (mellinWindowLogCutoff B) (Real.log y)‖) *
          (1 + |frequency|) ^ j := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hpower k) (by positivity)
    _ = Q (Real.log y) * (1 + |frequency|) ^ j := by rw [← Finset.sum_mul]
    _ ≤ (|M| + 1) * (1 + |frequency|) ^ j :=
      mul_le_mul_of_nonneg_right hQbound (by positivity)

/-- Every Euler derivative up to the prescribed order has one common
frequency bound for this fixed actual cutoff, at every real point. -/
theorem annularMellinWindow_euler_bound (B : SmoothAnnularTest) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ frequency : ℝ, ∀ j ≤ J, ∀ y : ℝ,
      ‖eulerDerivativeOrder j (annularMellinWindow B frequency) y‖ ≤
        C * (1 + |frequency|) ^ J := by
  choose c hc hbound using fun i : Fin (J + 1) =>
    annularMellinWindow_single_euler_bound B i.val
  let C : ℝ := (∑ i : Fin (J + 1), c i) + 1
  have hsum : 0 ≤ ∑ i : Fin (J + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, fun frequency j hj y => ?_⟩
  by_cases hy : y ∈ Icc B.lower B.upper
  · let i : Fin (J + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    have hci : c i ≤ C := by
      have hi : c i ≤ ∑ k : Fin (J + 1), c k :=
        Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ i)
      dsimp only [C]
      linarith
    exact (hbound i frequency y hy).trans
      (mul_le_mul hci (pow_le_pow_right₀ (by linarith [abs_nonneg frequency]) hj)
        (by positivity) hC.le)
  · have hz := ((good_toFun (annularMellinWindowTest B frequency)).eulerDerivativeOrder j).zero y hy
    change eulerDerivativeOrder j (annularMellinWindow B frequency) y = 0 at hz
    rw [hz, norm_zero]
    positivity

private theorem mellinWindow_integral_weight_bound (B : SmoothAnnularTest) (A : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ y ∈ Icc B.lower B.upper,
      (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y ≤ D := by
  have hc : ContinuousOn (fun y : ℝ => (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y)
      (Icc B.lower B.upper) := by
    have hn : ∀ y ∈ Icc B.lower B.upper, y ≠ 0 :=
      fun y hy => (lt_of_lt_of_le B.lower_pos hy.1).ne'
    exact ((continuousOn_id.rpow_const (fun y hy => Or.inl (hn y hy))).add
      (continuousOn_id.rpow_const (fun y hy => Or.inl (hn y hy)))).div continuousOn_id hn
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc B.lower B.upper)).bddAbove_image hc
  exact ⟨|M| + 1, by positivity, fun y hy =>
    (hM (Set.mem_image_of_mem _ hy)).trans (by linarith [le_abs_self M])⟩

/-- The genuine weighted Euler seminorm of a fixed Mellin separation
window has the required polynomial frequency growth. The coefficient
depends only on the fixed cutoff, requested order and integral weight. -/
theorem annularMellinWindow_testSeminorm_bound (B : SmoothAnnularTest) (J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ frequency : ℝ,
      testSeminorm (annularMellinWindow B frequency) J A ≤
        C * (1 + |frequency|) ^ J := by
  obtain ⟨D, hD, hder⟩ := annularMellinWindow_euler_bound B J
  obtain ⟨E, hE, hweight⟩ := mellinWindow_integral_weight_bound B A
  let m : ℝ := volume.real (Icc B.lower B.upper)
  have hm : 0 ≤ m := measureReal_nonneg
  refine ⟨D * E * (m + 1), by positivity, fun frequency => ?_⟩
  apply testSeminorm_le_of_integrals _ _ _ _ (by positivity)
  intro j hj
  let f : ℝ → ℝ := fun y =>
    ‖eulerDerivativeOrder j (annularMellinWindow B frequency) y‖ *
      (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y
  have hz : ∀ y, y ∉ Icc B.lower B.upper → f y = 0 := by
    intro y hy
    have he := ((good_toFun (annularMellinWindowTest B frequency)).eulerDerivativeOrder j).zero y hy
    change eulerDerivativeOrder j (annularMellinWindow B frequency) y = 0 at he
    simp only [f, he, norm_zero, zero_mul, zero_div]
  have hsupport : ∀ y, y ∉ Ioi (0 : ℝ) → f y = 0 := by
    intro y hy
    apply hz y
    intro hmem
    exact hy (lt_of_lt_of_le B.lower_pos hmem.1)
  have hint : testIntegral (annularMellinWindow B frequency) j A =
      ∫ y in Icc B.lower B.upper, f y := by
    change (∫ y in Ioi (0 : ℝ), f y) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupport,
      setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hfbound : ∀ y ∈ Icc B.lower B.upper,
      ‖f y‖ ≤ (D * (1 + |frequency|) ^ J) * E := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le B.lower_pos hy.1
    have hwnonneg : 0 ≤ (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y := by positivity
    have hfn : 0 ≤ f y := by dsimp only [f]; positivity
    rw [Real.norm_of_nonneg hfn]
    change ‖eulerDerivativeOrder j (annularMellinWindow B frequency) y‖ *
      (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y ≤ _
    rw [mul_div_assoc]
    exact mul_le_mul (hder frequency j hj y) (hweight y hy) hwnonneg (by positivity)
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := f) (s := Icc B.lower B.upper) isCompact_Icc.measure_lt_top hfbound
  rw [hint]
  calc
    _ ≤ ‖∫ y in Icc B.lower B.upper, f y‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (∫ y in Icc B.lower B.upper, f y)
    _ ≤ ((D * (1 + |frequency|) ^ J) * E) * m := hi
    _ ≤ ((D * (1 + |frequency|) ^ J) * E) * (m + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (D * E * (m + 1)) * (1 + |frequency|) ^ J := by ring

end HeckeSkeleton.Moments.EngineInduction
