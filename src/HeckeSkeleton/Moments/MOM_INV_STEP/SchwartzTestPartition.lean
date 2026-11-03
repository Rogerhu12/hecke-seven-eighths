module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

/-!
# A fixed smooth partition of every permitted positive norm test

The 24 scales are (3/2)^j for j=-18,...,5. A compact smooth difference
rho((2/3)x)-rho(x), with rho=1 on |x|≤1 and rho=0 on |x|≥4/3,
turns each dilated test into a genuine Schwartz function supported on
[1,2]. The finite sum telescopes exactly. The continuous linear maps
supply one finite seminorm bound for all pieces, before the original
test, arithmetic coefficients, rows and labels are chosen.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SchwartzTestPartition

open scoped Classical BigOperators ContDiff

def rho : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 4 / 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem rho_one {x : ℝ} (hx : |x| ≤ 1) : rho x = 1 := by
  apply rho.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, rho] using hx

theorem rho_zero {x : ℝ} (hx : 4 / 3 ≤ |x|) : rho x = 0 := by
  apply rho.zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, rho] using hx

def rhoSchwartz : SchwartzMap ℝ ℂ :=
  (rho.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp rho.contDiff)

@[simp] theorem rhoSchwartz_apply (x : ℝ) : rhoSchwartz x = (rho x : ℂ) := rfl

/-- Positive scalar dilation, with its actual inverse. -/
def dilation (a : ℝ) (ha : 0 < a) : ℝ ≃L[ℝ] ℝ where
  toFun x := a * x
  invFun x := a⁻¹ * x
  left_inv x := by
    change a⁻¹ * (a * x) = x
    rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  right_inv x := by
    change a * (a⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  map_add' x y := mul_add _ _ _
  map_smul' c x := by
    change a * (c * x) = c * (a * x)
    ring
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

@[simp] theorem dilation_apply (a : ℝ) (ha : 0 < a) (x : ℝ) :
    dilation a ha x = a * x := rfl

def window : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (dilation (2 / 3) (by norm_num)) rhoSchwartz -
    rhoSchwartz

@[simp] theorem window_apply (x : ℝ) :
    window x = (rho ((2 / 3) * x) : ℂ) - (rho x : ℂ) := rfl

theorem window_zero_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) : window x = 0 := by
  rw [window_apply, rho_one hx]
  have hsmall : |(2 / 3 : ℝ) * x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    nlinarith [abs_nonneg x]
  rw [rho_one hsmall]
  simp

theorem window_zero_of_two_le_abs {x : ℝ} (hx : 2 ≤ |x|) : window x = 0 := by
  rw [window_apply]
  have hsmall : (4 / 3 : ℝ) ≤ |(2 / 3 : ℝ) * x| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    nlinarith
  rw [rho_zero hsmall, rho_zero (by linarith : (4 / 3 : ℝ) ≤ |x|)]
  simp

def scale (j : ℤ) : ℝ := (3 / 2 : ℝ) ^ j

theorem scale_pos (j : ℤ) : 0 < scale j := zpow_pos (by norm_num) _

theorem scale_add_one (j : ℤ) : scale (j + 1) = scale j * (3 / 2) := by
  simp only [scale, zpow_add₀ (by norm_num : (3 / 2 : ℝ) ≠ 0), zpow_one]

def pieceCLM (j : ℤ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ window).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (dilation (scale j) (scale_pos j)))

def piece (W : SchwartzMap ℝ ℂ) (j : ℤ) : SchwartzMap ℝ ℂ := pieceCLM j W

@[simp] theorem piece_apply (W : SchwartzMap ℝ ℂ) (j : ℤ) (x : ℝ) :
    piece W j x = W (scale j * x) * window x := by
  unfold piece pieceCLM
  rw [ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply window.hasTemperateGrowth]
  change window x * W (scale j * x) = _
  exact mul_comm _ _

/-- This is a smooth test supported on [1,2], with no hard indicator. -/
theorem piece_support (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 512 : ℝ) 4) (j : ℤ) :
    tsupport (piece W j) ⊆ Set.Icc (1 : ℝ) 2 := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  have hn : piece W j x ≠ 0 := Function.mem_support.mp hx
  rw [piece_apply] at hn
  have hWn : W (scale j * x) ≠ 0 := (mul_ne_zero_iff.mp hn).1
  have hwin : window x ≠ 0 := (mul_ne_zero_iff.mp hn).2
  have hs := hW (subset_closure (Function.mem_support.mpr hWn))
  have hxpos : 0 < x := (mul_pos_iff_of_pos_left (scale_pos j)).mp (by linarith [hs.1])
  constructor
  · by_contra hl
    exact hwin (window_zero_of_abs_le_one (by rw [abs_of_pos hxpos]; linarith))
  · by_contra hh
    exact hwin (window_zero_of_two_le_abs (by rw [abs_of_pos hxpos]; linarith))

abbrev Index := Fin 24

def exponent (i : Index) : ℤ := (i.val : ℤ) - 18

theorem exponent_bounds (i : Index) : -18 ≤ exponent i ∧ exponent i ≤ 5 := by
  have hi := i.isLt
  dsimp only [exponent]
  omega

theorem successive_argument (x : ℝ) (j : ℤ) :
    (2 / 3 : ℝ) * (x / scale j) = x / scale (j + 1) := by
  rw [scale_add_one]
  field_simp [(scale_pos j).ne']

/-- The exact finite telescoping identity, before using the source support. -/
theorem sum_windows (x : ℝ) :
    (∑ i : Index, window (x / scale (exponent i))) =
      (rho (x / scale 6) : ℂ) - (rho (x / scale (-18)) : ℂ) := by
  let f : ℕ → ℂ := fun n => (rho (x / scale ((n : ℤ) - 18)) : ℂ)
  calc
    _ = ∑ i : Index, (f (i.val + 1) - f i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [window_apply, successive_argument]
      dsimp only [f, exponent]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show (i.val : ℤ) + 1 - 18 = (i.val : ℤ) - 18 + 1 by ring]
    _ = f 24 - f 0 := by
      change (∑ i : Fin 24, (fun n : ℕ => f (n + 1) - f n) i.val) = _
      exact (Fin.sum_univ_eq_sum_range (fun n : ℕ => f (n + 1) - f n) 24).trans
        (Finset.sum_range_sub f 24)
    _ = _ := by norm_num [f]

theorem lower_endpoint : (4 / 3 : ℝ) * scale (-18) ≤ 1 / 512 := by
  norm_num [scale]

theorem upper_endpoint : (4 : ℝ) ≤ scale 6 := by
  norm_num [scale]

theorem windows_sum_one {x : ℝ} (hx : x ∈ Set.Icc (1 / 512 : ℝ) 4) :
    (∑ i : Index, window (x / scale (exponent i))) = 1 := by
  have hxpos : 0 < x := by linarith [hx.1]
  have hu : rho (x / scale 6) = 1 := by
    apply rho_one
    rw [abs_of_pos (div_pos hxpos (scale_pos _))]
    exact (div_le_one (scale_pos _)).mpr (hx.2.trans upper_endpoint)
  have hl : rho (x / scale (-18)) = 0 := by
    apply rho_zero
    rw [abs_of_pos (div_pos hxpos (scale_pos _))]
    exact (le_div_iff₀ (scale_pos _)).mpr (lower_endpoint.trans hx.1)
  rw [sum_windows, hu, hl]
  norm_num

/-- Exact reconstruction of every permitted test, including all zeros. -/
theorem reconstruct (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 512 : ℝ) 4) (x : ℝ) :
    W x = ∑ i : Index, piece W (exponent i) (x / scale (exponent i)) := by
  have hp (i : Index) :
      piece W (exponent i) (x / scale (exponent i)) =
        W x * window (x / scale (exponent i)) := by
    rw [piece_apply]
    congr 1
    congr 1
    field_simp [(scale_pos (exponent i)).ne']
  simp_rw [hp]
  rw [← Finset.mul_sum]
  by_cases hx : W x = 0
  · rw [hx, zero_mul]
  · rw [windows_sum_one (hW (subset_closure (Function.mem_support.mpr hx))), mul_one]

theorem reconstruct_scaled (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 512 : ℝ) 4) (q U : ℝ) :
    W (q / U) = ∑ i : Index,
      piece W (exponent i) (q / (scale (exponent i) * U)) := by
  rw [reconstruct W hW (q / U)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [div_div, mul_comm U]

/-- Arbitrary arithmetic coefficients and rows are untouched by the
finite smooth decomposition of their norm test. -/
theorem finite_source_reconstruct {α : Type*} (T : Finset α)
    (A : α → ℂ) (q : α → ℝ) (U : ℝ) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 512 : ℝ) 4) :
    (∑ x ∈ T, A x * W (q x / U)) =
      ∑ i : Index, ∑ x ∈ T, A x *
        piece W (exponent i) (q x / (scale (exponent i) * U)) := by
  simp_rw [reconstruct_scaled W hW, Finset.mul_sum]
  exact Finset.sum_comm

/-- One fixed finite Schwartz control bounds all 24 genuine smooth
pieces simultaneously. No source or test enters its choice. -/
theorem exists_finite_seminorm_bound (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (i : Index),
      t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (piece W (exponent i)) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let T : Index → SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
    fun i => (pieceCLM (exponent i)).restrictScalars ℝ
  let q : Seminorm ℝ (SchwartzMap ℝ ℂ) := t.sup (schwartzSeminormFamily ℝ ℝ ℂ)
  let p : Seminorm ℝ (SchwartzMap ℝ ℂ) :=
    Finset.univ.sup (fun i : Index => q.comp (T i).toLinearMap)
  have hq : Continuous q := Seminorm.continuous_finsetSup (fun k _ =>
    (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm k)
  have hp : Continuous p := Seminorm.continuous_finsetSup
    (fun i _ => hq.comp (T i).continuous)
  obtain ⟨s, C, _hC, hb⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ ℝ ℂ) p hp
  refine ⟨s, C, C.property, ?_⟩
  intro W i
  have hi : q (T i W) ≤ p W :=
    Seminorm.le_finset_sup_apply (p := fun i : Index => q.comp (T i).toLinearMap)
      (x := W) (Finset.mem_univ i)
  exact hi.trans (Seminorm.le_def.mp hb W)

end HeckeSkeleton.Moments.MOM_INV_STEP.SchwartzTestPartition

end

