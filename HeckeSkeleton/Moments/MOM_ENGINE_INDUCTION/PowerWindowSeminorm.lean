import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryPowerWindows
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Choose

/-!
# Uniform Euler bounds for the actual two-line reflection windows

The fixed cutoff is the repository's `fixedDyadicWeight`, and the tests
are exactly `ordinaryPowerWindow σ t`.  Euler differentiation is ordinary
differentiation after the change of variables `y = exp x`.  Leibniz's rule
then separates the fixed smooth log cutoff from the complex exponential.
All constants are chosen before the real part and frequency.  In fact the
whole interval `1/4 ≤ σ ≤ 3/4` is controlled, not only its endpoints.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.ThetaKernel HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators ContDiff Topology

/-- The literal Euler iterates become ordinary derivatives in logarithmic
coordinates.  This identity uses the actual annular test, including its
global smooth extension across the nonpositive real axis. -/
theorem eulerDerivativeOrder_log_coordinate (V : SmoothAnnularTest) (j : ℕ) (x : ℝ) :
    eulerDerivativeOrder j V.toFun (Real.exp x) =
      iteratedDeriv j (fun z : ℝ => V.toFun (Real.exp z)) x := by
  induction j generalizing x with
  | zero => simp [eulerDerivativeOrder]
  | succ j ih =>
    have hid : iteratedDeriv j (fun z : ℝ => V.toFun (Real.exp z)) =
        fun z => eulerDerivativeOrder j V.toFun (Real.exp z) :=
      funext (fun z => (ih z).symm)
    rw [eulerDerivativeOrder_succ, iteratedDeriv_succ, hid]
    have hd := (((good_toFun V).eulerDerivativeOrder j).smooth.differentiable
      (by simp) (Real.exp x)).hasDerivAt
    simpa only [Function.comp_def, Complex.real_smul] using
      (hd.scomp x (Real.hasDerivAt_exp x)).deriv.symm

private def powerWindowLogCutoff (x : ℝ) : ℂ :=
  (fixedDyadicWeight (Real.exp x) : ℂ)

private theorem powerWindowLogCutoff_smooth :
    ContDiff ℝ ∞ powerWindowLogCutoff :=
  Complex.ofRealCLM.contDiff.comp
    (contDiff_fixedDyadicWeight.comp Real.contDiff_exp)

private def powerWindowLogExp (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (z * (x : ℂ))

private theorem powerWindowLogExp_smooth (z : ℂ) :
    ContDiff ℝ ∞ (powerWindowLogExp z) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

private theorem powerWindowLogExp_deriv (z : ℂ) (x : ℝ) :
    HasDerivAt (powerWindowLogExp z) (z * powerWindowLogExp z x) x := by
  have hlinear : HasDerivAt (fun y : ℝ => z * (y : ℂ)) z x := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul z
  simpa only [powerWindowLogExp, mul_comm] using! hlinear.cexp

private theorem powerWindowLogExp_iteratedDeriv (z : ℂ) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (powerWindowLogExp z) x = z ^ j * powerWindowLogExp z x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hd : deriv (powerWindowLogExp z) = fun x => z * powerWindowLogExp z x :=
      funext (fun x => (powerWindowLogExp_deriv z x).deriv)
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih, pow_succ]
    ring

private theorem powerWindow_exponent_norm (σ t : ℝ)
    (hσ : σ ∈ Icc (1 / 4 : ℝ) (3 / 4)) :
    ‖idealVerticalPoint σ t - 1‖ ≤ 1 + |t| := by
  have hid : idealVerticalPoint σ t - 1 = ((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    simp only [idealVerticalPoint, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hreal : |σ - 1| ≤ 1 := by
    rw [abs_of_nonpos (by linarith [hσ.2])]
    linarith [hσ.1]
  rw [hid]
  calc
    _ ≤ ‖((σ - 1 : ℝ) : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |σ - 1| + |t| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one]
    _ ≤ 1 + |t| := add_le_add hreal le_rfl

private theorem powerWindow_logExp_norm (σ t : ℝ)
    (hσ : σ ∈ Icc (1 / 4 : ℝ) (3 / 4)) {y : ℝ}
    (hy : y ∈ Icc (1 / 2 : ℝ) 2) :
    ‖powerWindowLogExp (idealVerticalPoint σ t - 1) (Real.log y)‖ ≤ 2 := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
  have hlo : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hlog : |Real.log y| ≤ Real.log 2 := by
    apply abs_le.mpr
    constructor
    · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hy.1
      simpa only [hlo] using h
    · exact Real.log_le_log hy0 hy.2
  have hreal : |σ - 1| ≤ 1 := by
    rw [abs_of_nonpos (by linarith [hσ.2])]
    linarith [hσ.1]
  have hprod : (σ - 1) * Real.log y ≤ Real.log 2 := by
    calc
      _ ≤ |(σ - 1) * Real.log y| := le_abs_self _
      _ = |σ - 1| * |Real.log y| := abs_mul _ _
      _ ≤ 1 * Real.log 2 := mul_le_mul hreal hlog (abs_nonneg _) (by norm_num)
      _ = Real.log 2 := one_mul _
  calc
    _ = Real.exp ((σ - 1) * Real.log y) := by
      simp only [powerWindowLogExp, Complex.norm_exp, Complex.mul_re,
        Complex.sub_re, Complex.one_re, idealVerticalPoint_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hprod
    _ = 2 := Real.exp_log (by norm_num)

private theorem ordinaryPowerWindow_single_euler_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc (1 / 4 : ℝ) (3 / 4), ∀ t : ℝ,
      ∀ y ∈ Icc (1 / 2 : ℝ) 2,
        ‖eulerDerivativeOrder j (ordinaryPowerWindow σ t) y‖ ≤ C * (1 + |t|) ^ j := by
  let B : ℝ → ℝ := fun x => ∑ k ∈ Finset.range (j + 1),
    (j.choose k : ℝ) * ‖iteratedDeriv k powerWindowLogCutoff x‖
  have hB : Continuous B := by
    dsimp only [B]
    exact continuous_finset_sum _ (fun k _ => continuous_const.mul
      (powerWindowLogCutoff_smooth.continuous_iteratedDeriv k (by simp)).norm)
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact
    (Icc (Real.log (1 / 2 : ℝ)) (Real.log 2))).bddAbove_image hB.continuousOn
  refine ⟨2 * (|M| + 1), by positivity, fun σ hσ t y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
  have hylog : Real.log y ∈ Icc (Real.log (1 / 2 : ℝ)) (Real.log 2) :=
    ⟨Real.log_le_log (by norm_num) hy.1, Real.log_le_log hy0 hy.2⟩
  have hBbound : B (Real.log y) ≤ |M| + 1 :=
    (hM (Set.mem_image_of_mem _ hylog)).trans (by linarith [le_abs_self M])
  let z : ℂ := idealVerticalPoint σ t - 1
  have heq : (fun x : ℝ => ordinaryPowerWindow σ t (Real.exp x)) =
      fun x => powerWindowLogCutoff x * powerWindowLogExp z x := by
    funext x
    dsimp only [ordinaryPowerWindow, profilePower, powerWindowLogCutoff,
      powerWindowLogExp, z]
    rw [Real.log_exp, mul_comm (x : ℂ)]
  have heuler := eulerDerivativeOrder_log_coordinate (ordinaryPowerWindowTest σ t)
    j (Real.log y)
  change eulerDerivativeOrder j (ordinaryPowerWindow σ t) (Real.exp (Real.log y)) =
    iteratedDeriv j (fun x : ℝ => ordinaryPowerWindow σ t (Real.exp x)) (Real.log y)
    at heuler
  rw [Real.exp_log hy0, heq] at heuler
  have hprod := norm_iteratedFDeriv_mul_le powerWindowLogCutoff_smooth
    (powerWindowLogExp_smooth z) (Real.log y) (n := j) (by simp)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hprod
  have hpower (k : ℕ) :
      ‖iteratedDeriv (j - k) (powerWindowLogExp z) (Real.log y)‖ ≤
        2 * (1 + |t|) ^ j := by
    rw [powerWindowLogExp_iteratedDeriv, norm_mul, norm_pow]
    have hz : ‖z‖ ≤ 1 + |t| := powerWindow_exponent_norm σ t hσ
    have hzpow : ‖z‖ ^ (j - k) ≤ (1 + |t|) ^ j :=
      (pow_le_pow_left₀ (norm_nonneg _) hz _).trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg t]) (Nat.sub_le _ _))
    calc
      _ ≤ (1 + |t|) ^ j * 2 := mul_le_mul hzpow
        (powerWindow_logExp_norm σ t hσ hy) (norm_nonneg _) (by positivity)
      _ = 2 * (1 + |t|) ^ j := mul_comm _ _
  rw [heuler]
  apply hprod.trans
  calc
    _ ≤ ∑ k ∈ Finset.range (j + 1),
        ((j.choose k : ℝ) * ‖iteratedDeriv k powerWindowLogCutoff (Real.log y)‖) *
          (2 * (1 + |t|) ^ j) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hpower k) (by positivity)
    _ = B (Real.log y) * (2 * (1 + |t|) ^ j) := by rw [← Finset.sum_mul]
    _ ≤ (|M| + 1) * (2 * (1 + |t|) ^ j) :=
      mul_le_mul_of_nonneg_right hBbound (by positivity)
    _ = (2 * (|M| + 1)) * (1 + |t|) ^ j := by ring

/-- A single constant controls every actual Euler derivative through
order `J`, uniformly in the two lines and the whole interval between
them.  The bound holds at every real point, since all Euler derivatives
retain the fixed annular support. -/
theorem ordinaryPowerWindow_euler_bound (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc (1 / 4 : ℝ) (3 / 4), ∀ t : ℝ,
      ∀ j ≤ J, ∀ y : ℝ,
        ‖eulerDerivativeOrder j (ordinaryPowerWindow σ t) y‖ ≤ C * (1 + |t|) ^ J := by
  choose c hc hbound using fun i : Fin (J + 1) => ordinaryPowerWindow_single_euler_bound i.val
  let C : ℝ := (∑ i : Fin (J + 1), c i) + 1
  have hsum : 0 ≤ ∑ i : Fin (J + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, fun σ hσ t j hj y => ?_⟩
  by_cases hy : y ∈ Icc (1 / 2 : ℝ) 2
  · let i : Fin (J + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    have hci : c i ≤ C := by
      have hi : c i ≤ ∑ k : Fin (J + 1), c k :=
        Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ i)
      dsimp only [C]
      linarith
    exact (hbound i σ hσ t y hy).trans
      (mul_le_mul hci (pow_le_pow_right₀ (by linarith [abs_nonneg t]) hj)
        (by positivity) hC.le)
  · have hz := ((good_toFun (ordinaryPowerWindowTest σ t)).eulerDerivativeOrder j).zero y hy
    change eulerDerivativeOrder j (ordinaryPowerWindow σ t) y = 0 at hz
    rw [hz, norm_zero]
    positivity

private theorem powerWindow_integral_weight_bound (A : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ y ∈ Icc (1 / 2 : ℝ) 2,
      (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y ≤ B := by
  have hc : ContinuousOn (fun y : ℝ => (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y)
      (Icc (1 / 2 : ℝ) 2) := by
    have hn : ∀ y ∈ Icc (1 / 2 : ℝ) 2, y ≠ 0 :=
      fun y hy => (lt_of_lt_of_le (by norm_num) hy.1).ne'
    exact ((continuousOn_id.rpow_const (fun y hy => Or.inl (hn y hy))).add
      (continuousOn_id.rpow_const (fun y hy => Or.inl (hn y hy)))).div
        continuousOn_id hn
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (1 / 2 : ℝ) 2)).bddAbove_image hc
  exact ⟨|M| + 1, by positivity, fun y hy =>
    (hM (Set.mem_image_of_mem _ hy)).trans (by linarith [le_abs_self M])⟩

/-- The repository's exact weighted Euler seminorm of the real reflected
test grows polynomially in its actual Mellin frequency.  The constant
depends only on `J`, `A` and the fixed cutoff. -/
theorem ordinaryPowerWindow_testSeminorm_bound (J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc (1 / 4 : ℝ) (3 / 4), ∀ t : ℝ,
      testSeminorm (ordinaryPowerWindow σ t) J A ≤ C * (1 + |t|) ^ J := by
  obtain ⟨D, hD, hder⟩ := ordinaryPowerWindow_euler_bound J
  obtain ⟨B, hB, hweight⟩ := powerWindow_integral_weight_bound A
  let m : ℝ := volume.real (Icc (1 / 2 : ℝ) 2)
  have hm : 0 ≤ m := measureReal_nonneg
  refine ⟨D * B * (m + 1), by positivity, fun σ hσ t => ?_⟩
  apply testSeminorm_le_of_integrals _ _ _ _ (by positivity)
  intro j hj
  let f : ℝ → ℝ := fun y =>
    ‖eulerDerivativeOrder j (ordinaryPowerWindow σ t) y‖ *
      (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y
  have hz : ∀ y, y ∉ Icc (1 / 2 : ℝ) 2 → f y = 0 := by
    intro y hy
    have he := ((good_toFun (ordinaryPowerWindowTest σ t)).eulerDerivativeOrder j).zero y hy
    change eulerDerivativeOrder j (ordinaryPowerWindow σ t) y = 0 at he
    simp only [f, he, norm_zero, zero_mul, zero_div]
  have hsupport : ∀ y, y ∉ Ioi (0 : ℝ) → f y = 0 := by
    intro y hy
    apply hz y
    intro hmem
    exact hy (lt_of_lt_of_le (by norm_num) hmem.1)
  have hint : testIntegral (ordinaryPowerWindow σ t) j A =
      ∫ y in Icc (1 / 2 : ℝ) 2, f y := by
    change (∫ y in Ioi (0 : ℝ), f y) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupport,
      setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hfbound : ∀ y ∈ Icc (1 / 2 : ℝ) 2, ‖f y‖ ≤ (D * (1 + |t|) ^ J) * B := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
    have hwnonneg : 0 ≤ (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y := by positivity
    have hfn : 0 ≤ f y := by dsimp only [f]; positivity
    rw [Real.norm_of_nonneg hfn]
    change ‖eulerDerivativeOrder j (ordinaryPowerWindow σ t) y‖ *
      (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y ≤ _
    rw [mul_div_assoc]
    exact mul_le_mul (hder σ hσ t j hj y) (hweight y hy) hwnonneg (by positivity)
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := f) (s := Icc (1 / 2 : ℝ) 2) isCompact_Icc.measure_lt_top hfbound
  rw [hint]
  calc
    _ ≤ ‖∫ y in Icc (1 / 2 : ℝ) 2, f y‖ := by
      simpa only [Real.norm_eq_abs] using
        le_abs_self (∫ y in Icc (1 / 2 : ℝ) 2, f y)
    _ ≤ ((D * (1 + |t|) ^ J) * B) * m := hi
    _ ≤ ((D * (1 + |t|) ^ J) * B) * (m + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (D * B * (m + 1)) * (1 + |t|) ^ J := by ring

/-- Concrete profile control, with its smoothness and actual support
proved from the fixed dyadic window.  It can be supplied to the genuine
model-profile consumer without adding an analytic hypothesis. -/
theorem ordinaryPowerWindow_sliceControl (J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc (1 / 4 : ℝ) (3 / 4), ∀ t : ℝ,
      SliceControl J A C (J : ℝ) (1 / 2) 2 |t| (ordinaryPowerWindow σ t) := by
  obtain ⟨C, hC, hbound⟩ := ordinaryPowerWindow_testSeminorm_bound J A
  refine ⟨C, hC, fun σ hσ t => ⟨ordinaryPowerWindow_smooth σ t, ?_, ?_⟩⟩
  · intro y hy
    exact ordinaryPowerWindow_support σ t hy
  · simpa only [Real.rpow_natCast] using hbound σ hσ t

end HeckeSkeleton.Moments.EngineInduction
