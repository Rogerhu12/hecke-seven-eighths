import HeckeGeneral.Analysis.SmoothIntegerPartition
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! A concrete nonnegative smooth dyadic partition on q >= 1. -/

noncomputable section

namespace HeckeGeneral.Analysis

open scoped Topology ContDiff

theorem fixedIntegerCutoff_hasSum (x : ℝ) :
    HasSum (fun k : ℤ => fixedIntegerCutoff (x - k)) 1 := by
  have h : Summable (fun k : ℤ => fixedIntegerCutoff (x - k)) :=
    summable_of_ne_finset_zero (fixedIntegerCutoff_shift_zero x)
  simpa only [fixedIntegerCutoff_partition] using h.hasSum

theorem fixedIntegerCutoff_nat_hasSum {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun k : ℕ => fixedIntegerCutoff (x - k)) 1 := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := Nat.cast_injective
  have hzero : ∀ k : ℤ, k ∉ Set.range (fun n : ℕ => (n : ℤ)) →
      fixedIntegerCutoff (x - k) = 0 := by
    intro k hk
    have hkneg : k < 0 := by
      by_contra h
      exact hk ⟨k.toNat, Int.toNat_of_nonneg (le_of_not_gt h)⟩
    have hk' : (k : ℝ) ≤ -1 := by
      exact_mod_cast (show k ≤ -1 by omega)
    exact fixedIntegerCutoff_zero_of_ge (by linarith)
  apply HasSum.congr_fun ((hinj.hasSum_iff hzero).mpr (fixedIntegerCutoff_hasSum x))
  intro n
  change fixedIntegerCutoff (x - (n : ℝ)) =
    fixedIntegerCutoff (x - ((n : ℤ) : ℝ))
  rw [Int.cast_natCast]

def fixedDyadicWeight (y : ℝ) : ℝ :=
  if 0 < y then fixedIntegerCutoff (Real.log y / Real.log 2) else 0

theorem fixedDyadicWeight_nonneg (y : ℝ) : 0 ≤ fixedDyadicWeight y := by
  unfold fixedDyadicWeight
  split_ifs
  · exact fixedIntegerCutoff_nonneg _
  · exact le_rfl

theorem fixedDyadicWeight_le_one (y : ℝ) : fixedDyadicWeight y ≤ 1 := by
  unfold fixedDyadicWeight
  split_ifs
  · exact fixedIntegerCutoff_le_one _
  · norm_num

theorem fixedDyadicWeight_zero_of_le {y : ℝ} (hy : y ≤ 1 / 2) :
    fixedDyadicWeight y = 0 := by
  unfold fixedDyadicWeight
  split_ifs with hpos
  · apply fixedIntegerCutoff_zero_of_le
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    have hlog := Real.log_le_log hpos hy
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at hlog
    linarith
  · rfl

theorem fixedDyadicWeight_zero_of_ge {y : ℝ} (hy : 2 ≤ y) :
    fixedDyadicWeight y = 0 := by
  have hpos : 0 < y := by linarith
  rw [fixedDyadicWeight, if_pos hpos]
  apply fixedIntegerCutoff_zero_of_ge
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) hy

theorem tsupport_fixedDyadicWeight :
    tsupport fixedDyadicWeight ⊆ Set.Icc (1 / 2) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  constructor
  · by_contra h
    exact hy (fixedDyadicWeight_zero_of_le (le_of_not_ge h))
  · by_contra h
    exact hy (fixedDyadicWeight_zero_of_ge (le_of_not_ge h))

theorem hasCompactSupport_fixedDyadicWeight : HasCompactSupport fixedDyadicWeight :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) tsupport_fixedDyadicWeight

theorem contDiffOn_fixedDyadicWeight : ContDiffOn ℝ ∞ fixedDyadicWeight (Set.Ioi 0) := by
  have hlog : ContDiffOn ℝ ∞ Real.log (Set.Ioi (0 : ℝ)) :=
    Real.contDiffOn_log.mono (fun y hy => ne_of_gt hy)
  have h := contDiff_fixedIntegerCutoff.comp_contDiffOn
    (hlog.div_const (Real.log 2))
  exact h.congr (fun y hy => by
    have hy' : 0 < y := hy
    simp [Function.comp_apply, fixedDyadicWeight, hy'])

theorem contDiff_fixedDyadicWeight : ContDiff ℝ ∞ fixedDyadicWeight := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : 0 < y
  · exact contDiffOn_fixedDyadicWeight.contDiffAt (isOpen_Ioi.mem_nhds hy)
  · have hzero : fixedDyadicWeight =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [gt_mem_nhds (show y < 1 / 2 by linarith)] with z hz
      exact fixedDyadicWeight_zero_of_le hz.le
    exact contDiffAt_const.congr_of_eventuallyEq hzero

theorem fixedDyadicWeight_scale {q : ℝ} (hq : 0 < q) (j : ℕ) :
    fixedDyadicWeight (q / (2 : ℝ) ^ j) =
      fixedIntegerCutoff (Real.log q / Real.log 2 - j) := by
  rw [fixedDyadicWeight, if_pos (div_pos hq (pow_pos (by norm_num) j)),
    Real.log_div hq.ne' (pow_ne_zero j (by norm_num)), Real.log_pow]
  congr 1
  field_simp

/-- The actual cutoff has the source's one-sided dyadic partition identity. -/
theorem fixedDyadicWeight_hasSum {q : ℝ} (hq : 1 ≤ q) :
    HasSum (fun j : ℕ => fixedDyadicWeight (q / (2 : ℝ) ^ j)) 1 := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hx : 0 ≤ Real.log q / Real.log 2 :=
    div_nonneg (Real.log_nonneg hq) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  simpa only [fixedDyadicWeight_scale hqpos] using fixedIntegerCutoff_nat_hasSum hx

theorem fixedDyadicWeight_partition {q : ℝ} (hq : 1 ≤ q) :
    (∑' j : ℕ, fixedDyadicWeight (q / (2 : ℝ) ^ j)) = 1 :=
  (fixedDyadicWeight_hasSum hq).tsum_eq

end HeckeGeneral.Analysis
