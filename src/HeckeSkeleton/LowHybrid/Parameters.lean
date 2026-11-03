import HeckeSkeleton.LowHybrid.SieveComposition
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual parameter inequalities for the completed hybrid block

The full cube contributes T^2 * G = B. The estimates below use the actual
quadratic and cubic sieve parameters, including their divisors D and r.
The final finite sum retains A_D / D and the reciprocal r sum explicitly.
No energy inequality or asymptotic estimate is assumed in this file.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators
noncomputable section

/-- The lower bound for T ensures that the squarefree part G is at most B. -/
theorem cube_block_squarefree_le (T G B : ℝ)
    (hT : 1 ≤ T) (hG : 0 ≤ G) (hB : T ^ 2 * G = B) : G ≤ B := by
  have hT2 : 1 ≤ T ^ 2 := by
    nlinarith [sq_nonneg (T - 1)]
  calc
    G = 1 * G := by ring
    _ ≤ T ^ 2 * G := mul_le_mul_of_nonneg_right hT2 hG
    _ = B := hB

/-- The actual quadratic parameter is bounded without a second cube factor. -/
theorem completed_quadratic_parameter_le (K N D r C T G B : ℝ)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hC : 1 ≤ C) (hT : 1 ≤ T) (hG : 0 ≤ G)
    (hB : T ^ 2 * G = B) :
    K / (D * r) + N * G / C ^ 2 ≤ K + N * B := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hDr : 1 ≤ D * r := one_le_mul_of_one_le_of_one_le hD hr
  have hC2 : 1 ≤ C ^ 2 := by
    nlinarith [sq_nonneg (C - 1)]
  have hfirst : K / (D * r) ≤ K := div_le_self hK0 hDr
  have hsecond : N * G / C ^ 2 ≤ N * B := by
    calc
      _ ≤ N * G := div_le_self (mul_nonneg hN0 hG) hC2
      _ ≤ N * B :=
        mul_le_mul_of_nonneg_left (cube_block_squarefree_le T G B hT hG hB) hN0
  exact add_le_add hfirst hsecond

/-- The cubic parameter retains both divisors before monotonicity is used. -/
theorem completed_cubic_parameter_le (N L D r : ℝ)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hD : 1 ≤ D) (hr : 1 ≤ r) :
    N / r + L / D + (N * L / (r * D)) ^ (2 / 3 : ℝ) ≤
      N + L + (N * L) ^ (2 / 3 : ℝ) := by
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hrD : 1 ≤ r * D := one_le_mul_of_one_le_of_one_le hr hD
  have hbase : 0 ≤ N * L / (r * D) :=
    div_nonneg (mul_nonneg hN0 hL0) (le_trans zero_le_one hrD)
  have harg : N * L / (r * D) ≤ N * L :=
    div_le_self (mul_nonneg hN0 hL0) hrD
  have hpow : (N * L / (r * D)) ^ (2 / 3 : ℝ) ≤
      (N * L) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hbase harg (by norm_num)
  exact add_le_add
    (add_le_add (div_le_self hN0 hr) (div_le_self hL0 hD)) hpow

/-- Nonnegativity needed when multiplying the actual cubic sieve factor. -/
theorem completed_cubic_parameter_nonneg (N L D r : ℝ)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hD : 1 ≤ D) (hr : 1 ≤ r) :
    0 ≤ N / r + L / D + (N * L / (r * D)) ^ (2 / 3 : ℝ) := by
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  exact add_nonneg
    (add_nonneg (div_nonneg hN0 hr0) (div_nonneg hL0 hD0))
    (Real.rpow_nonneg
      (div_nonneg (mul_nonneg hN0 hL0) (mul_nonneg hr0 hD0)) _)

/-- The entire t,c',h count is B/r, with no extra B. -/
theorem completed_cube_count (T G C r B : ℝ)
    (hC : 1 ≤ C) (hr : 1 ≤ r) (hB : T ^ 2 * G = B) :
    T ^ 2 * (C / r) * (G / C) = B / r := by
  have hCne : C ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC)
  have hrne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  simpa using fixed_block_scalar_ledger T G C r B 1 1 1 hCne hrne hB

/-- Literal scalar expression after the two sieve applications.
A is the surviving squared column coefficient mass. -/
def completedBlock (K N L D r C T G A : ℝ) : ℝ :=
  T ^ 2 * (K / (D * r) + N * G / C ^ 2) * (C / r) * (G / C) *
    (N / r + L / D + (N * L / (r * D)) ^ (2 / 3 : ℝ)) * A

/-- Full H6 block bound with the actual quadratic and cubic parameters.
The column mass A is kept, rather than replaced by a unit bound. -/
theorem block_envelope (K N L D r C T G B A : ℝ)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hD : 1 ≤ D) (hr : 1 ≤ r) (hC : 1 ≤ C) (hT : 1 ≤ T)
    (hG : 0 ≤ G) (hA : 0 ≤ A) (hB : T ^ 2 * G = B) :
    completedBlock K N L D r C T G A ≤
      (K + N * B) * (B / r) * (N + L + (N * L) ^ (2 / 3 : ℝ)) * A := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hB0 : 0 ≤ B := by
    rw [← hB]
    exact mul_nonneg (sq_nonneg _) hG
  have hBr : 0 ≤ B / r := div_nonneg hB0 hr0
  have hQ0 : 0 ≤ K + N * B := add_nonneg hK0 (mul_nonneg hN0 hB0)
  have hCne : C ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC)
  have hrne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  have hq := completed_quadratic_parameter_le K N D r C T G B
    hK hN hD hr hC hT hG hB
  have hc := completed_cubic_parameter_le N L D r hN hL hD hr
  have hc0 := completed_cubic_parameter_nonneg N L D r hN hL hD hr
  calc
    _ = (K / (D * r) + N * G / C ^ 2) * (B / r) *
        (N / r + L / D + (N * L / (r * D)) ^ (2 / 3 : ℝ)) * A :=
      fixed_block_scalar_ledger T G C r B
        (K / (D * r) + N * G / C ^ 2)
        (N / r + L / D + (N * L / (r * D)) ^ (2 / 3 : ℝ)) A hCne hrne hB
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul
        (mul_le_mul_of_nonneg_right hq hBr) hc hc0 (mul_nonneg hQ0 hBr)) hA

/-- Restore the exact outer divisor normalization from a(P)/sqrt(q(P)).
The final factors are A_D / D and 1/r, each occurring once. -/
theorem normalized_block_envelope (K N L D r C T G B A : ℝ)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hD : 1 ≤ D) (hr : 1 ≤ r) (hC : 1 ≤ C) (hT : 1 ≤ T)
    (hG : 0 ≤ G) (hA : 0 ≤ A) (hB : T ^ 2 * G = B) :
    (1 / D) * completedBlock K N L D r C T G A ≤
      (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) *
        (A / D) * (1 / r) := by
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  calc
    _ ≤ (1 / D) *
        ((K + N * B) * (B / r) * (N + L + (N * L) ^ (2 / 3 : ℝ)) * A) :=
      mul_le_mul_of_nonneg_left
        (block_envelope K N L D r C T G B A hK hN hL hD hr hC hT hG hA hB)
        (div_nonneg zero_le_one hD0)
    _ = _ := by
      simp only [div_eq_mul_inv]
      ring

/-- Sum actual normalized blocks while keeping both divisor ledgers.
C,T,G may vary with both divisors; A_D remains the actual column mass. -/
theorem normalized_blocks_sum_le {DIndex RIndex : Type*}
    (ds : Finset DIndex) (rs : Finset RIndex)
    (dNorm : DIndex → ℝ) (rNorm : RIndex → ℝ)
    (C T G : DIndex → RIndex → ℝ) (A : DIndex → ℝ)
    (K N L B : ℝ) (hK : 1 ≤ K) (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hD : ∀ d ∈ ds, 1 ≤ dNorm d)
    (hr : ∀ r ∈ rs, 1 ≤ rNorm r)
    (hC : ∀ d ∈ ds, ∀ r ∈ rs, 1 ≤ C d r)
    (hT : ∀ d ∈ ds, ∀ r ∈ rs, 1 ≤ T d r)
    (hG : ∀ d ∈ ds, ∀ r ∈ rs, 0 ≤ G d r)
    (hA : ∀ d ∈ ds, 0 ≤ A d)
    (hB : ∀ d ∈ ds, ∀ r ∈ rs, (T d r) ^ 2 * G d r = B) :
    (∑ d ∈ ds, ∑ r ∈ rs, (1 / dNorm d) *
      completedBlock K N L (dNorm d) (rNorm r) (C d r) (T d r) (G d r) (A d)) ≤
      (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) *
        (∑ d ∈ ds, A d / dNorm d) * (∑ r ∈ rs, 1 / rNorm r) := by
  calc
    _ ≤ ∑ d ∈ ds, ∑ r ∈ rs,
        (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) *
          (A d / dNorm d) * (1 / rNorm r) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro r hrmem
      exact normalized_block_envelope
        K N L (dNorm d) (rNorm r) (C d r) (T d r) (G d r) B (A d)
        hK hN hL (hD d hd) (hr r hrmem) (hC d hd r hrmem) (hT d hd r hrmem)
        (hG d hd r hrmem) (hA d hd) (hB d hd r hrmem)
    _ = (∑ d ∈ ds,
        (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) *
          (A d / dNorm d)) * (∑ r ∈ rs, 1 / rNorm r) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      exact (Finset.mul_sum ..).symm
    _ = _ := by rw [← Finset.mul_sum]

#print axioms cube_block_squarefree_le
#print axioms completed_quadratic_parameter_le
#print axioms completed_cubic_parameter_le
#print axioms completed_cubic_parameter_nonneg
#print axioms completed_cube_count
#print axioms block_envelope
#print axioms normalized_block_envelope
#print axioms normalized_blocks_sum_le

end
end HeckeSkeleton.LowHybrid

