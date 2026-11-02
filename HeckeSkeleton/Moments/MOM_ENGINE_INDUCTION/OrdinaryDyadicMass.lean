import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# The scale-uniform mass of ordinary reflection windows

A short window has normalized cost r^(1/4), while a long window has
arbitrary negative power.  The two-sided dyadic envelope below has a
single finite mass for every positive physical dual scale, including
subunit scales.  The cutoff is finite and arbitrary.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open scoped BigOperators Classical

private theorem geometric_balance_mass {q s : ℝ} (hq : 1 < q) (hs : 0 < s) (J : ℕ) :
    (∑ j ∈ Finset.range J, min (q ^ j / s) (s / q ^ j)) ≤ 2 / (1 - q⁻¹) := by
  have hq0 : 0 < q := by linarith
  let r : ℝ := q⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr hq0.le
  have hr1 : r < 1 := (inv_lt_one₀ hq0).mpr hq
  have hden : 0 < 1 - r := by linarith
  have hgeo := hasSum_geometric_of_lt_one hr0 hr1
  let f : ℕ → ℝ := fun j => min (q ^ j / s) (s / q ^ j)
  have hf0 (j : ℕ) : 0 ≤ f j := le_min (by positivity) (by positivity)
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le hf0 (fun j => ?_) (hgeo.summable.mul_left s)
    calc
      _ ≤ s / q ^ j := min_le_right _ _
      _ = s * r ^ j := by simp only [r, inv_pow, div_eq_mul_inv]
  have htotal : (∑' j, f j) ≤ 2 / (1 - r) := by
    by_cases hsmall : s ≤ 1
    · have hm : (∑' j, f j) ≤ s * (1 - r)⁻¹ := by
        calc
          _ ≤ ∑' j, s * r ^ j := hf.tsum_le_tsum (fun j => by
            exact (min_le_right _ _).trans_eq (by simp only [r, inv_pow, div_eq_mul_inv]))
              (hgeo.summable.mul_left s)
          _ = _ := by rw [tsum_mul_left, hgeo.tsum_eq]
      exact hm.trans (by
        have hi : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr hden.le
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by linarith) hi)
    · obtain ⟨N, hlow, hhigh⟩ := exists_nat_pow_near (le_of_not_ge hsmall) hq
      have hhead : (∑ j ∈ Finset.range (N + 1), f j) ≤ (1 - r)⁻¹ := by
        calc
          _ ≤ ∑ j ∈ Finset.range (N + 1), r ^ (N - j) := by
            apply Finset.sum_le_sum
            intro j hj
            have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
            calc
              _ ≤ q ^ j / s := min_le_left _ _
              _ ≤ q ^ j / q ^ N :=
                div_le_div_of_nonneg_left (pow_nonneg hq0.le _) (pow_pos hq0 _) hlow
              _ = r ^ (N - j) := by
                dsimp [r]
                rw [inv_pow]
                field_simp [pow_ne_zero _ hq0.ne']
                rw [← pow_add, Nat.add_sub_of_le hjN]
          _ = ∑ j ∈ Finset.range (N + 1), r ^ j := by
            simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun j => r ^ j) (N + 1)
          _ ≤ ∑' j, r ^ j := hgeo.summable.sum_le_tsum _ (fun j _ => pow_nonneg hr0 _)
          _ = _ := hgeo.tsum_eq
      have htail : (∑' j, f (j + (N + 1))) ≤ (1 - r)⁻¹ := by
        calc
          _ ≤ ∑' j, r ^ j :=
            ((summable_nat_add_iff (N + 1)).mpr hf).tsum_le_tsum (fun j => by
              calc
                _ ≤ s / q ^ (j + (N + 1)) := min_le_right _ _
                _ ≤ q ^ (N + 1) / q ^ (j + (N + 1)) :=
                  div_le_div_of_nonneg_right hhigh.le (pow_nonneg hq0.le _)
                _ = r ^ j := by
                  dsimp [r]
                  rw [pow_add, inv_pow]
                  field_simp [pow_ne_zero _ hq0.ne']
                  <;> ring) hgeo.summable
          _ = _ := hgeo.tsum_eq
      rw [← hf.sum_add_tsum_nat_add (N + 1)]
      rw [div_eq_mul_inv]
      linarith
  exact (hf.sum_le_tsum _ (fun j _ => hf0 j)).trans htotal

/-- A single explicit mass bound for all positive dual scales and all
finite dyadic truncations.  Taking α=1/4 charges the actual short and
long reflected-window factors to one common summable envelope. -/
theorem ordinaryReflection_dyadic_mass {α : ℝ} (hα : 0 < α)
    {Y : ℝ} (hY : 0 < Y) (J : ℕ) :
    (∑ j ∈ Finset.range J,
      min (((2 : ℝ) ^ j / Y) ^ α) (((2 : ℝ) ^ j / Y) ^ (-α))) ≤
        2 / (1 - (2 : ℝ) ^ (-α)) := by
  let q : ℝ := (2 : ℝ) ^ α
  let s : ℝ := Y ^ α
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) hα
  have hs : 0 < s := Real.rpow_pos_of_pos hY α
  have he (j : ℕ) :
      min (((2 : ℝ) ^ j / Y) ^ α) (((2 : ℝ) ^ j / Y) ^ (-α)) =
        min (q ^ j / s) (s / q ^ j) := by
    have hp : ((2 : ℝ) ^ j) ^ α = q ^ j :=
      (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) α j).symm
    rw [Real.div_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j) hY.le,
      Real.div_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j) hY.le,
      Real.rpow_neg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j) α, Real.rpow_neg hY.le α, hp]
    simp only [s, div_eq_mul_inv, inv_inv, mul_comm]
  simp_rw [he]
  have h := geometric_balance_mass hq hs J
  simpa only [q, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] using h

end HeckeSkeleton.Moments.EngineInduction
