module

public import HeckeSkeleton.Moments.MOM_INV_STEP.MellinSeparation

/-! A fixed positive wide Mellin window, with plateau [1/4,5/2]. -/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.WideMellinTests

open MeasureTheory
open scoped Classical ContDiff BigOperators Topology

def normBump : ContDiffBump (11 / 8 : ℝ) where
  rIn := 9 / 8
  rOut := 5 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def logBump : ContDiffBump (11 / 8 : ℝ) where
  rIn := 5 / 4
  rOut := 21 / 16
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoff (x : ℝ) : ℂ := (normBump x : ℂ)

theorem cutoff_contDiff : ContDiff ℝ ∞ cutoff :=
  Complex.ofRealCLM.contDiff.comp normBump.contDiff

theorem cutoff_compact : HasCompactSupport cutoff :=
  normBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

theorem cutoff_tsupport :
    tsupport cutoff = Metric.closedBall (11 / 8 : ℝ) (5 / 4) := by
  have hs : Function.support cutoff = Function.support normBump := by
    ext x
    change ((normBump x : ℝ) : ℂ) ≠ 0 ↔ normBump x ≠ 0
    exact not_congr Complex.ofReal_eq_zero
  change closure (Function.support cutoff) = _
  rw [hs]
  exact normBump.tsupport_eq

theorem cutoff_one {x : ℝ} (hx : 1 / 4 ≤ x) (hx2 : x ≤ 5 / 2) :
    cutoff x = 1 := by
  have hm : x ∈ Metric.closedBall (11 / 8 : ℝ) normBump.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq]
    change |x - 11 / 8| ≤ 9 / 8
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  unfold cutoff
  rw [normBump.one_of_mem_closedBall hm]
  norm_num

theorem cutoff_support_interval :
    tsupport cutoff ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8) := by
  intro x hx
  rw [cutoff_tsupport, Metric.mem_closedBall, Real.dist_eq] at hx
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  constructor <;> linarith

theorem cutoff_support_bounds {x : ℝ} (hx : x ∈ tsupport cutoff) :
    0 < x ∧ ‖x‖ ≤ 3 := by
  obtain ⟨hl, hu⟩ := cutoff_support_interval hx
  have hp : 0 < x := by linarith
  exact ⟨hp, by rw [Real.norm_eq_abs, abs_of_pos hp]; linarith⟩

theorem norm_cutoff_le_one (x : ℝ) : ‖cutoff x‖ ≤ 1 := by
  rw [cutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg normBump.nonneg]
  exact normBump.le_one

def cutoffSchwartz : SchwartzMap ℝ ℂ :=
  cutoff_compact.toSchwartzMap cutoff_contDiff

@[simp] theorem cutoffSchwartz_apply (x : ℝ) : cutoffSchwartz x = cutoff x := rfl

def logExtension (x : ℝ) : ℝ := logBump x * Real.log x

theorem logExtension_contDiff : ContDiff ℝ ∞ logExtension := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport logBump
  · have hpos : 0 < x := by
      rw [logBump.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hx
      change |x - 11 / 8| ≤ 21 / 16 at hx
      have hl := (abs_le.mp hx).1
      linarith
    exact logBump.contDiff.contDiffAt.mul (Real.contDiffAt_log.mpr hpos.ne')
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    have he : logExtension =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hz] with y hy
      change logBump y * Real.log y = 0
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem logExtension_compact : HasCompactSupport logExtension :=
  logBump.hasCompactSupport.mul_right

def logExtensionSchwartz : SchwartzMap ℝ ℝ :=
  logExtension_compact.toSchwartzMap logExtension_contDiff

@[simp] theorem logExtensionSchwartz_apply (x : ℝ) :
    logExtensionSchwartz x = logExtension x := rfl

theorem logExtension_eq_log {x : ℝ} (hx : x ∈ tsupport cutoff) :
    logExtension x = Real.log x := by
  have hm : x ∈ Metric.closedBall (11 / 8 : ℝ) logBump.rIn := by
    simpa only [cutoff_tsupport, logBump] using hx
  unfold logExtension
  rw [logBump.one_of_mem_closedBall hm, one_mul]

theorem columnPhase_eq_exp (t x : ℝ) :
    CommonKernel.columnPhase t x =
      Complex.exp (((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I) := by
  simp only [CommonKernel.columnPhase, Real.fourierChar_apply, Real.inner_apply]
  congr 2
  push_cast
  ring

/-- Restricting a smooth two-variable function to a horizontal line
does not increase the norm of an iterated derivative. -/
theorem partial_derivative_bound (f : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x t : ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => f (y, t)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (x, t)‖ := by
  let g : ℝ × ℝ → ℂ := fun p => f (p + (0, t))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have he : (fun y => f (y, t)) = g ∘ ContinuousLinearMap.inl ℝ ℝ ℝ := by
    funext y
    simp [g]
  rw [he, (ContinuousLinearMap.inl ℝ ℝ ℝ).iteratedFDeriv_comp_right hg x
    (by exact_mod_cast le_top)]
  have hb := (iteratedFDeriv ℝ n g ((ContinuousLinearMap.inl ℝ ℝ ℝ) x)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => ContinuousLinearMap.inl ℝ ℝ ℝ)
  simpa only [ContinuousLinearMap.norm_inl, Finset.prod_const_one, mul_one,
    g, iteratedFDeriv_comp_add_right, ContinuousLinearMap.inl_apply,
    Prod.mk_add_mk, add_zero, zero_add] using hb


open MeasureTheory
open CommonKernel
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
    tsupport (weightedTest a t) ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8) :=
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
    (hlo : 1 / 4 ≤ u / U) (hhi : u / U ≤ 5 / 2) :
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


/-- The zero-order seminorm does not depend on the Mellin frequency. -/
theorem weightedTest_norm (a t x : ℝ) :
    ‖weightedTest a t x‖ = ‖weightedTest a 0 x‖ := by
  rw [norm_weightedTest, norm_weightedTest]

theorem seminorm_zero_eq_of_norm_eq (F G : SchwartzMap ℝ ℂ)
    (h : ∀ x : ℝ, ‖F x‖ = ‖G x‖) :
    SchwartzMap.seminorm ℝ 0 0 F = SchwartzMap.seminorm ℝ 0 0 G := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 F (apply_nonneg _ _)
    intro x
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, h x] using
      SchwartzMap.norm_le_seminorm ℝ G x
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 G (apply_nonneg _ _)
    intro x
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, ← h x] using
      SchwartzMap.norm_le_seminorm ℝ F x

theorem weightedTest_seminorm_zero (a t : ℝ) :
    SchwartzMap.seminorm ℝ 0 0 (weightedTest a t) =
      SchwartzMap.seminorm ℝ 0 0 (weightedTest a 0) :=
  seminorm_zero_eq_of_norm_eq _ _ (weightedTest_norm a t)

theorem parent_weightedTest_seminorm_zero (a t : ℝ) :
    SchwartzMap.seminorm ℝ 0 0 (MellinWeightedTests.weightedTest a t) =
      SchwartzMap.seminorm ℝ 0 0 (MellinWeightedTests.weightedTest a 0) := by
  apply seminorm_zero_eq_of_norm_eq
  intro x
  rw [MellinWeightedTests.norm_weightedTest, MellinWeightedTests.norm_weightedTest]

/-- The cutoff is kept explicitly outside its plateau. -/
theorem scaled_weighted_phase_all (a t u U : ℝ) (hu : 0 < u) (hU : 0 < U) :
    ((U ^ a : ℝ) : ℂ) * columnPhase t (Real.log U) *
      weightedTest a t (u / U) =
        cutoff (u / U) * ((u ^ a : ℝ) : ℂ) * columnPhase t (Real.log u) := by
  rw [weightedTest_eq]
  have hp : u ^ a = U ^ a * (u / U) ^ a := by
    rw [← Real.mul_rpow hU.le (div_pos hu hU).le]
    congr 1
    field_simp
  have hl : Real.log u = Real.log U + Real.log (u / U) := by
    rw [Real.log_div hu.ne' hU.ne']
    ring
  rw [hp, hl, columnPhase_add, Complex.ofReal_mul]
  ring

/-- Multiplication by the fixed wide-window power is a genuine Schwartz
operator. It preserves the support of the original test. -/
def powerTest (W : SchwartzMap ℝ ℂ) (a : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (weightedTest a 0) W

@[simp] theorem powerTest_apply (W : SchwartzMap ℝ ℂ) (a x : ℝ) :
    powerTest W a x = weightedTest a 0 x * W x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (weightedTest a 0).hasTemperateGrowth W x

theorem powerTest_support (W : SchwartzMap ℝ ℂ) (a : ℝ) :
    tsupport (powerTest W a) ⊆ tsupport W := by
  exact (SchwartzMap.tsupport_smulLeftCLM_subset (weightedTest a 0) W).trans
    Set.inter_subset_left

theorem powerTest_apply_of_support (W : SchwartzMap ℝ ℂ) (a : ℝ)
    (hW : tsupport W ⊆ Set.Icc (1 / 4 : ℝ) (5 / 2)) (x : ℝ) :
    powerTest W a x = W x * ((x ^ a : ℝ) : ℂ) := by
  rw [powerTest_apply, weightedTest_eq]
  by_cases hx : W x = 0
  · simp only [hx, mul_zero, zero_mul]
  · have hb := hW (subset_closure (Function.mem_support.mpr hx))
    rw [cutoff_one hb.1 hb.2]
    have hz : columnPhase 0 (Real.log x) = 1 := by simp [columnPhase]
    rw [hz, one_mul, mul_one, mul_comm]

theorem scaled_powerTest (W : SchwartzMap ℝ ℂ) (a q X : ℝ)
    (hq : 0 < q) (hX : 0 < X)
    (hW : tsupport W ⊆ Set.Icc (1 / 4 : ℝ) (5 / 2)) :
    W (q / X) * ((q ^ a : ℝ) : ℂ) =
      ((X ^ a : ℝ) : ℂ) * powerTest W a (q / X) := by
  rw [powerTest_apply_of_support W a hW]
  have hp : q ^ a = X ^ a * (q / X) ^ a := by
    rw [← Real.mul_rpow hX.le (div_pos hq hX).le]
    congr 1
    field_simp
  rw [hp, Complex.ofReal_mul]
  ring

theorem powerTest_finite_seminorm_bound (a : ℝ) (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ W : SchwartzMap ℝ ℂ,
      t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (powerTest W a) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let T := (SchwartzMap.smulLeftCLM ℂ (weightedTest a 0)).restrictScalars ℝ
  let p : Seminorm ℝ (SchwartzMap ℝ ℂ) :=
    (t.sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp T.toLinearMap
  have ht : Continuous (fun W : SchwartzMap ℝ ℂ =>
      t.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
    Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)
  obtain ⟨s, C, hC, hb⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ ℝ ℂ) p (ht.comp T.continuous)
  exact ⟨s, C, C.property, fun W => Seminorm.le_def.mp hb W⟩

end HeckeSkeleton.Moments.MOM_INV_STEP.WideMellinTests

end

