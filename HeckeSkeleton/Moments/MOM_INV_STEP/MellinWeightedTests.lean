module

public import HeckeSkeleton.Moments.MOM_INV_STEP.MellinSchwartz

/-!
# Actual weighted Mellin tests

Real powers and logarithmic unit phases are placed in one fixed compact
norm window.  Every finite Schwartz seminorm has polynomial growth in
the Mellin frequency, with constants selected before that frequency.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.MellinWeightedTests

open MeasureTheory
open MellinSchwartz CommonKernel
open scoped Classical ContDiff BigOperators

def weightedCutoff (a x : ℝ) : ℂ :=
  cutoff x * (Real.exp (a * logExtension x) : ℂ)

theorem weightedCutoff_contDiff (a : ℝ) : ContDiff ℝ ∞ (weightedCutoff a) := by
  unfold weightedCutoff
  exact cutoff_contDiff.mul (Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul logExtension_contDiff)))

theorem weightedCutoff_compact (a : ℝ) : HasCompactSupport (weightedCutoff a) :=
  cutoff_compact.mul_right

def weightedCutoffSchwartz (a : ℝ) : SchwartzMap ℝ ℂ :=
  (weightedCutoff_compact a).toSchwartzMap (weightedCutoff_contDiff a)

def weightedJoint (a : ℝ) (p : ℝ × ℝ) : ℂ :=
  weightedCutoff a p.1 *
    Complex.exp (((2 * Real.pi * p.2 * logExtension p.1 : ℝ) : ℂ) * Complex.I)

theorem weightedJoint_temperate (a : ℝ) :
    Function.HasTemperateGrowth (weightedJoint a) := by
  have hw : Function.HasTemperateGrowth (weightedCutoff a) :=
    (weightedCutoffSchwartz a).hasTemperateGrowth
  have hl : Function.HasTemperateGrowth logExtension := logExtensionSchwartz.hasTemperateGrowth
  have hfst : Function.HasTemperateGrowth (fun p : ℝ × ℝ => p.1) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
  have hsnd : Function.HasTemperateGrowth (fun p : ℝ × ℝ => p.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  have harg : Function.HasTemperateGrowth
      (fun p : ℝ × ℝ => 2 * Real.pi * p.2 * logExtension p.1) :=
    ((Function.HasTemperateGrowth.const (2 * Real.pi)).mul hsnd).mul (hl.comp hfst)
  exact (hw.comp hfst).mul (Complex.hasTemperateGrowth_exp_mul_I.comp harg)

def weightedFunction (a t x : ℝ) : ℂ := weightedJoint a (x, t)

theorem weightedFunction_contDiff (a t : ℝ) :
    ContDiff ℝ ∞ (weightedFunction a t) := by
  have h := (weightedJoint_temperate a).1
  unfold weightedFunction
  fun_prop

theorem weightedFunction_support (a t : ℝ) :
    tsupport (weightedFunction a t) ⊆ tsupport cutoff := by
  apply closure_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hc
  apply hx
  simp only [weightedFunction, weightedJoint, weightedCutoff, hc, zero_mul]

theorem weightedFunction_compact (a t : ℝ) :
    HasCompactSupport (weightedFunction a t) :=
  cutoff_compact.of_isClosed_subset isClosed_closure (weightedFunction_support a t)

def weightedTest (a t : ℝ) : SchwartzMap ℝ ℂ :=
  (weightedFunction_compact a t).toSchwartzMap (weightedFunction_contDiff a t)

@[simp] theorem weightedTest_apply (a t x : ℝ) :
    weightedTest a t x = weightedFunction a t x := rfl

theorem weightedTest_support (a t : ℝ) :
    tsupport (weightedTest a t) ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2) :=
  (weightedFunction_support a t).trans cutoff_support_interval

theorem weightedTest_eq (a t x : ℝ) :
    weightedTest a t x =
      cutoff x * ((x ^ a : ℝ) : ℂ) * columnPhase t (Real.log x) := by
  by_cases hc : cutoff x = 0
  · simp only [weightedTest_apply, weightedFunction, weightedJoint, weightedCutoff, hc, zero_mul]
  · have hs : x ∈ tsupport cutoff := subset_closure (Function.mem_support.mpr hc)
    have hx := (cutoff_support_bounds hs).1
    rw [weightedTest_apply]
    unfold weightedFunction weightedJoint weightedCutoff
    rw [logExtension_eq_log hs, columnPhase_eq_exp, Real.rpow_def_of_pos hx]
    rw [mul_comm a (Real.log x)]

theorem norm_weightedTest (a t x : ℝ) :
    ‖weightedTest a t x‖ = ‖cutoff x‖ * ‖(x ^ a : ℝ)‖ := by
  rw [weightedTest_eq, norm_mul, norm_mul, norm_columnPhase, mul_one, Complex.norm_real]

theorem continuous_weightedTest (a x : ℝ) :
    Continuous (fun t : ℝ => weightedTest a t x) := by
  simp only [weightedTest_eq]
  exact continuous_const.mul (continuous_columnPhase (Real.log x))

theorem columnPhase_add (t x y : ℝ) :
    columnPhase t (x + y) = columnPhase t x * columnPhase t y := by
  simp only [columnPhase, inner_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem columnPhase_frequency_add (t u x : ℝ) :
    columnPhase t x * columnPhase u x = columnPhase (t + u) x := by
  simp only [columnPhase, inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]

/-- The precise scale factor is retained; no norm power is treated as
a unit phase. -/
theorem scaled_weighted_phase (a t u U : ℝ) (hu : 0 < u) (hU : 0 < U)
    (hlo : 1 ≤ u / U) (hhi : u / U ≤ 2) :
    ((u ^ a : ℝ) : ℂ) * columnPhase t (Real.log u) =
      ((U ^ a : ℝ) : ℂ) * columnPhase t (Real.log U) *
        weightedTest a t (u / U) := by
  rw [weightedTest_eq, cutoff_one hlo hhi, one_mul]
  have hp : u ^ a = U ^ a * (u / U) ^ a := by
    rw [← Real.mul_rpow hU.le (div_pos hu hU).le]
    congr 1
    field_simp
  have hl : Real.log u = Real.log U + Real.log (u / U) := by
    rw [Real.log_div hu.ne' hU.ne']
    ring
  rw [hp, hl, columnPhase_add, Complex.ofReal_mul]
  ring

theorem weightedTest_polynomial_bound (a : ℝ) (k n : ℕ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ k n (weightedTest a t) ≤ C * (1 + |t|) ^ m := by
  obtain ⟨m, C, hC, hb⟩ := (weightedJoint_temperate a).norm_iteratedFDeriv_le_uniform n
  refine ⟨m, 3 ^ k * C * 4 ^ m, by positivity, fun t => ?_⟩
  apply SchwartzMap.seminorm_le_bound ℝ k n (weightedTest a t) (by positivity)
  intro x
  by_cases hx : x ∈ tsupport cutoff
  · have hxnorm := (cutoff_support_bounds hx).2
    have hp : 1 + ‖(x, t)‖ ≤ 4 * (1 + |t|) := by
      simp only [Prod.norm_def, Real.norm_eq_abs]
      have hmax : max |x| |t| ≤ 3 + |t| := max_le
        (by simpa only [Real.norm_eq_abs] using
          hxnorm.trans (le_add_of_nonneg_right (abs_nonneg t)))
        (le_add_of_nonneg_left (by norm_num))
      nlinarith [abs_nonneg t]
    have hder : ‖iteratedFDeriv ℝ n (weightedTest a t) x‖ ≤
        C * (1 + ‖(x, t)‖) ^ m :=
      (partial_derivative_bound (weightedJoint a)
        (weightedJoint_temperate a).1 n x t).trans (hb n le_rfl (x, t))
    calc
      _ ≤ 3 ^ k * (C * (1 + ‖(x, t)‖) ^ m) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxnorm k) hder
          (norm_nonneg _) (by positivity)
      _ ≤ 3 ^ k * (C * (4 * (1 + |t|)) ^ m) := by
        gcongr
      _ = (3 ^ k * C * 4 ^ m) * (1 + |t|) ^ m := by
        rw [mul_pow]
        ring
  · have hz : iteratedFDeriv ℝ n (weightedTest a t) x = 0 := by
      by_contra hz
      exact hx ((weightedFunction_support a t)
        (support_iteratedFDeriv_subset n (Function.mem_support.mpr hz)))
    rw [hz, norm_zero, mul_zero]
    positivity

/-- All finitely many seminorms use one frequency exponent and one
constant, selected before the frequency. -/
theorem finite_seminorm_polynomial_bound (a : ℝ) (s : Finset (ℕ × ℕ)) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (weightedTest a t) ≤ C * (1 + |t|) ^ m := by
  choose m C hC hb using fun i : ℕ × ℕ => weightedTest_polynomial_bound a i.1 i.2
  have hsum : 0 ≤ ∑ i ∈ s, C i := Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨s.sup m, ∑ i ∈ s, C i, hsum, fun t => ?_⟩
  apply Seminorm.finset_sup_apply_le (mul_nonneg hsum (by positivity))
  intro i hi
  exact (hb i t).trans (mul_le_mul
    (Finset.single_le_sum (fun j _ => hC j) hi)
    (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg t)) (Finset.le_sup hi))
    (by positivity) hsum)

theorem combined_frequency_seminorm_bound (a : ℝ) (s : Finset (ℕ × ℕ)) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t u : ℝ,
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (weightedTest a (t + u)) ≤
        C * (1 + |t|) ^ m * (1 + |u|) ^ m := by
  obtain ⟨m, C, hC, hb⟩ := finite_seminorm_polynomial_bound a s
  refine ⟨m, C, hC, fun t u => (hb (t + u)).trans ?_⟩
  have hp : 1 + |t + u| ≤ (1 + |t|) * (1 + |u|) := by
    have ha := abs_add_le t u
    nlinarith [abs_nonneg t, abs_nonneg u, mul_nonneg (abs_nonneg t) (abs_nonneg u)]
  calc
    C * (1 + |t + u|) ^ m ≤ C * ((1 + |t|) * (1 + |u|)) ^ m := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

end HeckeSkeleton.Moments.MOM_INV_STEP.MellinWeightedTests

end
