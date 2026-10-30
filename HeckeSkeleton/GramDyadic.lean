import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-!
# The dyadic double sum of the Gram estimate (GR-08)

From the uncompiled candidate `ActualDyadicDoubleSum.lean`
(old repository cache `actual-gram-dyadic-sum-20261012`), compiled here, plus
the conversion to the skeleton's form: `2 ^ (-(i + j : ℝ))` and a sum over
`ℕ × ℕ`.
-/
noncomputable section

open scoped BigOperators
open Finset

namespace HeckeSkeleton.GramDyadic

def dyadicKernel (L : ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n * min 1 (((2 : ℝ) ^ n / L) ^ 3)

def weightedKernel (L : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * dyadicKernel L n

def weightedGeometric (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n

lemma dyadicKernel_nonneg {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 ≤ dyadicKernel L n := by
  exact mul_nonneg (pow_nonneg (by norm_num) _) (le_min (by norm_num)
    (pow_nonneg (div_nonneg (pow_nonneg (by norm_num) _) hL.le) _))

lemma dyadicKernel_le_geometric (L : ℝ) (n : ℕ) :
    dyadicKernel L n ≤ (1 / 2 : ℝ) ^ n := by
  simpa only [dyadicKernel, mul_one] using
    mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) (((2 : ℝ)^n/L)^3))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n)

lemma weightedKernel_nonneg {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 ≤ weightedKernel L n :=
  mul_nonneg (by positivity) (dyadicKernel_nonneg hL n)

lemma weightedKernel_le_geometric (L : ℝ) (n : ℕ) :
    weightedKernel L n ≤ weightedGeometric n :=
  mul_le_mul_of_nonneg_left (dyadicKernel_le_geometric L n) (by positivity)

lemma hasSum_half_geometric : HasSum (fun n : ℕ => (1 / 2 : ℝ)^n) 2 := by
  convert hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1) using 1
  norm_num

lemma hasSum_weightedGeometric : HasSum weightedGeometric 4 := by
  have h : HasSum (fun n : ℕ => (n : ℝ) * (1/2 : ℝ)^n) 2 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one
      (by norm_num : ‖(1/2 : ℝ)‖ < 1) using 1
    norm_num
  convert h.add hasSum_half_geometric using 1
  · funext n
    dsimp only [weightedGeometric]
    ring
  · norm_num

lemma summable_weightedKernel {L : ℝ} (hL : 0 < L) :
    Summable (weightedKernel L) :=
  Summable.of_nonneg_of_le (weightedKernel_nonneg hL)
    (weightedKernel_le_geometric L) hasSum_weightedGeometric.summable

lemma summable_pairKernel {L : ℝ} (hL : 0 < L) :
    Summable (fun p : ℕ × ℕ => dyadicKernel L (p.1 + p.2)) := by
  have h := hasSum_half_geometric.summable.mul_of_nonneg
    hasSum_half_geometric.summable (fun n => pow_nonneg (by norm_num) n)
      (fun n => pow_nonneg (by norm_num) n)
  exact Summable.of_nonneg_of_le (fun p => dyadicKernel_nonneg hL _)
    (fun p => by simpa only [pow_add] using dyadicKernel_le_geometric L (p.1+p.2)) h

/-- The multiplicity of a diagonal is exactly `n+1`; the two indices are retained. -/
lemma tsum_pairKernel_eq {L : ℝ} (hL : 0 < L) :
    (∑' p : ℕ × ℕ, dyadicKernel L (p.1+p.2)) = ∑' n : ℕ, weightedKernel L n := by
  let e : (Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n) ≃ ℕ × ℕ :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  have hσ : Summable (fun p : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n =>
      dyadicKernel L ((p.2 : ℕ × ℕ).1 + (p.2 : ℕ × ℕ).2)) :=
    e.summable_iff.mpr (summable_pairKernel hL)
  calc
    _ = ∑' p : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n,
        dyadicKernel L ((p.2 : ℕ × ℕ).1 + (p.2 : ℕ × ℕ).2) :=
      (e.tsum_eq _).symm
    _ = ∑' n : ℕ, ∑' p : Finset.HasAntidiagonal.antidiagonal n,
        dyadicKernel L ((p : ℕ × ℕ).1 + (p : ℕ × ℕ).2) :=
      hσ.tsum_sigma' (fun _ => (hasSum_fintype _).summable)
    _ = _ := by
      apply tsum_congr
      intro n
      have hp (p : Finset.HasAntidiagonal.antidiagonal n) :
          dyadicKernel L ((p : ℕ × ℕ).1 + (p : ℕ × ℕ).2) = dyadicKernel L n := by
        rw [Finset.HasAntidiagonal.mem_antidiagonal.mp p.property]
      simp_rw [hp]
      simp [weightedKernel, Finset.Nat.card_antidiagonal, Nat.cast_add, Nat.cast_one]

lemma tsum_iterated_eq {L : ℝ} (hL : 0 < L) :
    (∑' i : ℕ, ∑' j : ℕ, dyadicKernel L (i+j)) =
      ∑' n : ℕ, weightedKernel L n := by
  rw [← (summable_pairKernel hL).tsum_prod]
  exact tsum_pairKernel_eq hL

lemma dyadicKernel_le_cubic {L : ℝ} (_hL : 0 < L) (n : ℕ) :
    dyadicKernel L n ≤ (4 : ℝ)^n / L^3 := by
  have hid : (1/2 : ℝ)^n * ((2 : ℝ)^n)^3 = (4 : ℝ)^n := by
    rw [← pow_mul, Nat.mul_comm n 3, pow_mul, ← mul_pow]
    norm_num
  calc
    _ ≤ (1/2 : ℝ)^n * (((2 : ℝ)^n/L)^3) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg (by norm_num) _)
    _ = _ := by rw [div_pow ((2 : ℝ)^n) L 3, ← mul_div_assoc, hid]

lemma sum_weighted_four_pow_le (N : ℕ) :
    (∑ n ∈ range N, ((n : ℝ)+1)*(4 : ℝ)^n) ≤ ((N : ℝ)+1)*(4 : ℝ)^N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    have hp : 0 ≤ (4 : ℝ)^N := pow_nonneg (by norm_num) _
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    have hnp : 0 ≤ (N : ℝ) * (4 : ℝ)^N := mul_nonneg hn hp
    nlinarith

lemma four_pow_div_two_pow_cube (N : ℕ) :
    (4 : ℝ)^N / ((2 : ℝ)^N)^3 = (1/2 : ℝ)^N := by
  rw [← pow_mul, Nat.mul_comm N 3, pow_mul, ← div_pow]
  norm_num

lemma sum_head_le {L : ℝ} (hL : 0 < L) (N : ℕ) (hNL : (2 : ℝ)^N ≤ L) :
    (∑ n ∈ range N, weightedKernel L n) ≤ ((N : ℝ)+1)*(1/2 : ℝ)^N := by
  have hd : 0 < ((2 : ℝ)^N)^3 := pow_pos (pow_pos (by norm_num) _) _
  have hcube : ((2 : ℝ)^N)^3 ≤ L^3 := pow_le_pow_left₀ (by positivity) hNL 3
  calc
    _ ≤ ∑ n ∈ range N, (((n : ℝ)+1)*(4 : ℝ)^n) / L^3 := by
      apply sum_le_sum
      intro n hn
      simpa only [weightedKernel, mul_div_assoc] using
        mul_le_mul_of_nonneg_left (dyadicKernel_le_cubic hL n) (by positivity)
    _ = (∑ n ∈ range N, ((n : ℝ)+1)*(4 : ℝ)^n) / L^3 := by
      rw [sum_div]
    _ ≤ (((N : ℝ)+1)*(4 : ℝ)^N) / L^3 :=
      div_le_div_of_nonneg_right (sum_weighted_four_pow_le N) (by positivity)
    _ ≤ (((N : ℝ)+1)*(4 : ℝ)^N) / ((2 : ℝ)^N)^3 :=
      div_le_div_of_nonneg_left (by positivity) hd hcube
    _ = _ := by rw [mul_div_assoc, four_pow_div_two_pow_cube]

lemma hasSum_weightedGeometric_shift (N : ℕ) :
    HasSum (fun k : ℕ => weightedGeometric (k+N))
      ((1/2 : ℝ)^N * (4 + 2*(N : ℝ))) := by
  have h := (hasSum_weightedGeometric.add
    (hasSum_half_geometric.mul_left (N : ℝ))).mul_left ((1/2 : ℝ)^N)
  convert h using 1
  · funext k
    simp only [weightedGeometric, Nat.cast_add, pow_add]
    ring
  · ring

/-- A uniform cutoff estimate, valid whenever `2^N ≤ L`. -/
theorem tsum_weightedKernel_le_cutoff {L : ℝ} (hL : 0 < L) (N : ℕ)
    (hNL : (2 : ℝ)^N ≤ L) :
    (∑' n : ℕ, weightedKernel L n) ≤ 6*((N : ℝ)+1)*(1/2 : ℝ)^N := by
  have hs := summable_weightedKernel hL
  have htail : (∑' k : ℕ, weightedKernel L (k+N)) ≤
      (1/2 : ℝ)^N * (4+2*(N : ℝ)) := by
    calc
      _ ≤ ∑' k : ℕ, weightedGeometric (k+N) :=
        Summable.tsum_le_tsum (fun k => weightedKernel_le_geometric L (k+N))
          ((summable_nat_add_iff N).mpr hs) (hasSum_weightedGeometric_shift N).summable
      _ = _ := (hasSum_weightedGeometric_shift N).tsum_eq
  rw [← hs.sum_add_tsum_nat_add N]
  have hhead := sum_head_le hL N hNL
  have hp : 0 ≤ (1/2 : ℝ)^N := pow_nonneg (by norm_num) _
  have hnp : 0 ≤ (N : ℝ)*(1/2 : ℝ)^N := mul_nonneg (Nat.cast_nonneg _) hp
  nlinarith

lemma tsum_weightedKernel_le_four {L : ℝ} (hL : 0 < L) :
    (∑' n : ℕ, weightedKernel L n) ≤ 4 := by
  calc
    _ ≤ ∑' n : ℕ, weightedGeometric n :=
      Summable.tsum_le_tsum (weightedKernel_le_geometric L)
        (summable_weightedKernel hL) hasSum_weightedGeometric.summable
    _ = _ := hasSum_weightedGeometric.tsum_eq

def dyadicBoundConstant : ℝ := 12 * (1 + 1 / Real.log 2)

lemma dyadicBoundConstant_ge_four : 4 ≤ dyadicBoundConstant := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hi : 0 ≤ 1 / Real.log 2 := le_of_lt (one_div_pos.mpr h)
  dsimp [dyadicBoundConstant]
  linarith

/-- The continuous-parameter bound includes the range `0 < L < 1`. -/
theorem tsum_weightedKernel_le_log {L : ℝ} (hL : 0 < L) :
    (∑' n : ℕ, weightedKernel L n) ≤
      dyadicBoundConstant * (1 + Real.log (2+L)) / L := by
  have hlog : 0 ≤ Real.log (2+L) := Real.log_nonneg (by linarith)
  have hC := dyadicBoundConstant_ge_four
  by_cases hsmall : L < 1
  · apply (tsum_weightedKernel_le_four hL).trans
    apply (le_div_iff₀ hL).mpr
    have hCL : 0 ≤ dyadicBoundConstant * Real.log (2+L) := mul_nonneg (by linarith) hlog
    nlinarith
  · obtain ⟨N, hlow, hhigh⟩ := exists_nat_pow_near (le_of_not_gt hsmall)
      (by norm_num : (1 : ℝ) < 2)
    have hpow : 0 < (2 : ℝ)^N := pow_pos (by norm_num) _
    have hhalf : (1/2 : ℝ)^N ≤ 2/L := by
      rw [one_div_pow]
      apply (div_le_div_iff₀ hpow hL).mpr
      simpa only [pow_succ, mul_comm, one_mul, mul_one] using hhigh.le
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hnlog : (N : ℝ)*Real.log 2 ≤ Real.log (2+L) := by
      calc
        _ = Real.log ((2 : ℝ)^N) := (Real.log_pow _ _).symm
        _ ≤ Real.log L := Real.log_le_log hpow hlow
        _ ≤ Real.log (2+L) := Real.log_le_log hL (by linarith)
    have hn : (N : ℝ) ≤ Real.log (2+L) / Real.log 2 :=
      (le_div_iff₀ hlog2).mpr hnlog
    have hcoef : (N : ℝ)+1 ≤ (1+1/Real.log 2)*(1+Real.log (2+L)) := by
      have hi : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr hlog2.le
      simp only [div_eq_mul_inv, one_mul] at hn ⊢
      nlinarith
    calc
      _ ≤ 6*((N : ℝ)+1)*(1/2 : ℝ)^N := tsum_weightedKernel_le_cutoff hL N hlow
      _ ≤ 6*((N : ℝ)+1)*(2/L) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = 12*((N : ℝ)+1)/L := by ring
      _ ≤ 12*((1+1/Real.log 2)*(1+Real.log (2+L)))/L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (by norm_num)) hL.le
      _ = _ := by unfold dyadicBoundConstant; ring

/-- The actual double sum, with a single absolute constant for every positive parameter. -/
theorem dyadic_double_sum_bound {L : ℝ} (hL : 0 < L) :
    (∑' i : ℕ, ∑' j : ℕ,
      (1/2 : ℝ)^(i+j) * min 1 (((2 : ℝ)^(i+j)/L)^3)) ≤
        dyadicBoundConstant * (1+Real.log (2+L))/L := by
  change (∑' i : ℕ, ∑' j : ℕ, dyadicKernel L (i+j)) ≤ _
  rw [tsum_iterated_eq hL]
  exact tsum_weightedKernel_le_log hL

theorem dyadic_double_summable {L : ℝ} (hL : 0 < L) :
    Summable (fun p : ℕ × ℕ =>
      (1/2 : ℝ)^(p.1+p.2) * min 1 (((2 : ℝ)^(p.1+p.2)/L)^3)) :=
  summable_pairKernel hL

theorem exists_uniform_dyadic_double_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L →
      (∑' i : ℕ, ∑' j : ℕ,
        (1/2 : ℝ)^(i+j) * min 1 (((2 : ℝ)^(i+j)/L)^3)) ≤
          C * (1+Real.log (2+L))/L := by
  refine ⟨dyadicBoundConstant, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4)
    dyadicBoundConstant_ge_four, ?_⟩
  intro L hL
  exact dyadic_double_sum_bound hL


theorem kernel_eq (Λ : ℝ) (ij : ℕ × ℕ) :
    (2 : ℝ) ^ (-(ij.1 + ij.2 : ℝ)) * min 1 (((2 : ℝ) ^ (ij.1 + ij.2) / Λ) ^ 3) =
      dyadicKernel Λ (ij.1 + ij.2) := by
  rw [dyadicKernel, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Nat.cast_add,
    Real.rpow_natCast, one_div, inv_pow]

/-- GR-08 in the form stated in `HeckeSkeleton.Gram`. -/
theorem positive_dyadic_double_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 0 < Λ →
      Summable (fun ij : ℕ × ℕ =>
        (2 : ℝ) ^ (-(ij.1 + ij.2 : ℝ)) *
          min 1 (((2 : ℝ) ^ (ij.1 + ij.2) / Λ) ^ 3)) ∧
      (∑' ij : ℕ × ℕ,
        (2 : ℝ) ^ (-(ij.1 + ij.2 : ℝ)) *
          min 1 (((2 : ℝ) ^ (ij.1 + ij.2) / Λ) ^ 3)) ≤
        C * (1 + Real.log (2 + Λ)) / Λ := by
  refine ⟨dyadicBoundConstant, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4)
    dyadicBoundConstant_ge_four, fun Λ hΛ => ⟨?_, ?_⟩⟩
  · exact (summable_pairKernel hΛ).congr (fun ij => (kernel_eq Λ ij).symm)
  · rw [tsum_congr (kernel_eq Λ), tsum_pairKernel_eq hΛ]
    exact tsum_weightedKernel_le_log hΛ

end HeckeSkeleton.GramDyadic
