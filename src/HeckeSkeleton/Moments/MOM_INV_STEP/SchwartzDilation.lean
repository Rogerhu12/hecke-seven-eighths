module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

/-!
# Uniform positive dilations of the one-dimensional Schwartz test

Clipping a short norm scale changes only the test's positive dilation.
The dilation is proved pointwise and its seminorm bound is uniform on a
fixed compact interval of dilation factors.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SchwartzDilation

open scoped Classical BigOperators

def dilate (a : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 a ha.ne')) W

@[simp] theorem dilate_apply (a : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ) (x : ℝ) :
    dilate a ha W x = W (a * x) := by
  change W (x * a) = _
  rw [mul_comm]

theorem iteratedFDeriv_dilate (a : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (n : ℕ) (x : ℝ) :
    iteratedFDeriv ℝ n (dilate a ha W) x =
      a ^ n • iteratedFDeriv ℝ n W (a * x) := by
  have he : (dilate a ha W : ℝ → ℂ) = fun y => W (a • y) := by
    funext y
    simp only [dilate_apply, smul_eq_mul]
  rw [he, iteratedFDeriv_comp_const_smul a (W.smooth n)]
  rfl

theorem seminorm_dilate_le (a B : ℝ) (ha : 0 < a) (ha₁ : 1 ≤ a) (haB : a ≤ B)
    (W : SchwartzMap ℝ ℂ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (dilate a ha W) ≤
      B ^ n * SchwartzMap.seminorm ℝ k n W := by
  have hB : 0 ≤ B := ha.le.trans haB
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro x
  rw [iteratedFDeriv_dilate, norm_smul, norm_pow, Real.norm_of_nonneg ha.le]
  have hxx : ‖x‖ ≤ ‖a * x‖ := by
    rw [norm_mul, Real.norm_of_nonneg ha.le]
    exact le_mul_of_one_le_left (norm_nonneg _) ha₁
  calc
    _ = a ^ n * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n W (a * x)‖) := by ring
    _ ≤ a ^ n * (‖a * x‖ ^ k * ‖iteratedFDeriv ℝ n W (a * x)‖) := by gcongr
    _ ≤ a ^ n * SchwartzMap.seminorm ℝ k n W :=
      mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℝ k n W (a * x)) (pow_nonneg ha.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le haB _) (apply_nonneg _ _)

theorem finite_seminorm_dilate_le (B : ℝ) (hB : 1 ≤ B) (s : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, ∀ ha : 0 < a, 1 ≤ a → a ≤ B →
      ∀ W : SchwartzMap ℝ ℂ,
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (dilate a ha W) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let C := ∑ i ∈ s, B ^ i.2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans hB) _)
  refine ⟨C, hC, ?_⟩
  intro a ha ha₁ haB W
  apply Seminorm.finset_sup_apply_le (mul_nonneg hC (apply_nonneg _ _))
  intro i hi
  have hc : B ^ i.2 ≤ C :=
    Finset.single_le_sum (fun _ _ => pow_nonneg (zero_le_one.trans hB) _) hi
  have hs : SchwartzMap.seminorm ℝ i.1 i.2 W ≤
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    rw [← SchwartzMap.schwartzSeminormFamily_apply]
    exact Seminorm.le_finset_sup_apply hi
  exact (seminorm_dilate_le a B ha ha₁ haB W i.1 i.2).trans
    (mul_le_mul hc hs (apply_nonneg _ _) hC)

theorem tsupport_dilate_subset (a B lo hi : ℝ) (ha : 0 < a)
    (ha₁ : 1 ≤ a) (haB : a ≤ B) (hlo : 0 ≤ lo)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc lo hi) :
    tsupport (dilate a ha W) ⊆ Set.Icc (lo / B) hi := by
  have hB : 0 < B := ha.trans_le haB
  apply closure_minimal
  · intro x hx
    have hxW : W (a * x) ≠ 0 := by
      simpa only [Function.mem_support, dilate_apply] using hx
    have hloc := hW (subset_closure (Function.mem_support.mpr hxW))
    have hx0 : 0 ≤ x := nonneg_of_mul_nonneg_right (hlo.trans hloc.1) ha
    constructor
    · apply (div_le_iff₀ hB).mpr
      exact hloc.1.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right haB hx0)
    · exact (le_mul_of_one_le_left hx0 ha₁).trans hloc.2
  · exact isClosed_Icc

theorem clip_dilation_bounds (U : ℝ) (hU : 0 < U) (hlive : 1 ≤ 4 * U) :
    1 ≤ max 1 U / U ∧ max 1 U / U ≤ 4 := by
  constructor
  · exact (le_div_iff₀ hU).mpr (by simpa using le_max_right (1 : ℝ) U)
  · apply (div_le_iff₀ hU).mpr
    exact max_le hlive (by linarith)

theorem clip_test_identity (U : ℝ) (hU : 0 < U) (W : SchwartzMap ℝ ℂ) (q : ℝ) :
    dilate (max 1 U / U) (div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hU)
      W (q / max 1 U) = W (q / U) := by
  rw [dilate_apply]
  congr 1
  field_simp [hU.ne', (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) U)).ne']

end HeckeSkeleton.Moments.MOM_INV_STEP.SchwartzDilation

end

