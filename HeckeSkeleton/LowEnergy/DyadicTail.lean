import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Exact infinite dyadic tails and all-annulus small-power allocation

The positive Mellin line yields geometric decay in the excess dual shell.
The infinite two-variable sum, including all retained shells, is bounded by
`(M+2)^2`. The subsequent logarithmic and annular factors are explicit.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.DyadicTail
open scoped BigOperators Topology

/-- A finite flat prefix followed by the genuine geometric tail. -/
def flatGeometric (M n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n - M)

theorem hasSum_flatGeometric (M : ℕ) :
    HasSum (flatGeometric M) ((M : ℝ) + 2) := by
  have ht : HasSum (fun n : ℕ => flatGeometric M (n + M)) 2 := by
    simpa only [flatGeometric, Nat.add_sub_cancel] using hasSum_geometric_two
  have hp : (∑ n ∈ Finset.range M, flatGeometric M n) = (M : ℝ) := by
    have hfun : ∀ n ∈ Finset.range M, flatGeometric M n = 1 := by
      intro n hn
      simp [flatGeometric, Nat.sub_eq_zero_of_le (Nat.le_of_lt (Finset.mem_range.mp hn))]
    simp only [Finset.sum_congr rfl hfun, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  simpa only [hp] using ht.sum_range_add

/-- The squarefree/cube shell has weight `j+3k`. -/
def weight (M : ℕ) (i : ℕ × ℕ) : ℝ := (1 / 2 : ℝ) ^ (i.1 + 3 * i.2 - M)

theorem weight_le_product (M : ℕ) (i : ℕ × ℕ) :
    weight M i ≤ flatGeometric M i.1 * flatGeometric M i.2 := by
  unfold weight flatGeometric
  rw [← pow_add]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- This proves both actual summability and a uniform bound for the complete
infinite grid; no formal `tsum = 0` fallback can occur. -/
theorem summable_weight_and_tsum_le (M : ℕ) :
    Summable (weight M) ∧ (∑' i : ℕ × ℕ, weight M i) ≤ ((M : ℝ) + 2) ^ 2 := by
  have hs := (hasSum_flatGeometric M).summable
  have hp : Summable (fun i : ℕ × ℕ => flatGeometric M i.1 * flatGeometric M i.2) :=
    hs.mul_of_nonneg hs (fun n => by unfold flatGeometric; positivity)
      (fun n => by unfold flatGeometric; positivity)
  have hw : Summable (weight M) := Summable.of_nonneg_of_le
    (fun i => by unfold weight; positivity) (weight_le_product M) hp
  refine ⟨hw, ?_⟩
  calc
    _ ≤ ∑' i : ℕ × ℕ, flatGeometric M i.1 * flatGeometric M i.2 :=
      hw.tsum_le_tsum (weight_le_product M) hp
    _ = (∑' n : ℕ, flatGeometric M n) * ∑' n : ℕ, flatGeometric M n :=
      (hs.tsum_mul_tsum hs hp).symm
    _ = ((M : ℝ) + 2) ^ 2 := by simp only [(hasSum_flatGeometric M).tsum_eq]; ring

/-- Every finite subset of the dyadic grid obeys the same bound. -/
theorem finite_weight_sum_le (M : ℕ) (s : Finset (ℕ × ℕ)) :
    (∑ i ∈ s, weight M i) ≤ ((M : ℝ) + 2) ^ 2 := by
  obtain ⟨hs, hsum⟩ := summable_weight_and_tsum_le M
  exact (hs.sum_le_tsum s (fun i _ => by unfold weight; positivity)).trans hsum

/-- A real threshold can be enlarged to an integer threshold before any
geometric summation.  The available norm exponent is at least one. -/
theorem real_penalty_le_weight {a L : ℝ} (ha : 1 ≤ a) (M : ℕ)
    (hL : L ≤ (M : ℝ)) (i : ℕ × ℕ) :
    (2 : ℝ) ^ (-a * max ((i.1 : ℝ) + 3 * i.2 - L) 0) ≤ weight M i := by
  have hrhs : weight M i = (2 : ℝ) ^ (-((i.1 + 3 * i.2 - M : ℕ) : ℝ)) := by
    unfold weight
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    simp [one_div, inv_pow]
  rw [hrhs]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hp : 0 ≤ max ((i.1 : ℝ) + 3 * i.2 - L) 0 := le_max_right _ _
  have hm : max ((i.1 : ℝ) + 3 * i.2 - L) 0 ≤
      a * max ((i.1 : ℝ) + 3 * i.2 - L) 0 := by
    simpa using mul_le_mul_of_nonneg_right ha hp
  by_cases hcut : M ≤ i.1 + 3 * i.2
  · rw [Nat.cast_sub hcut]
    push_cast
    linarith [le_max_left ((i.1 : ℝ) + 3 * i.2 - L) 0]
  · have hz : i.1 + 3 * i.2 - M = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz]
    norm_num
    nlinarith

/-- Changing from base Z logarithmic widths to base two shell indices is
an exact identity, including the positive-part cutoff. -/
theorem real_width_penalty_eq {Z : ℝ} (hZ : 1 < Z) (a T x : ℝ) :
    Z ^ (-a * max (x * Real.log 2 / Real.log Z - T) 0) =
      (2 : ℝ) ^ (-a * max (x - T * Real.log Z / Real.log 2) 0) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hzlog : 0 < Real.log Z := Real.log_pos hZ
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have ht : 0 ≤ Real.log 2 / Real.log Z := (div_pos htwo hzlog).le
  have hmax : max (x * Real.log 2 / Real.log Z - T) 0 =
      (Real.log 2 / Real.log Z) * max (x - T * Real.log Z / Real.log 2) 0 := by
    rw [mul_max_of_nonneg _ _ ht, mul_zero]
    congr 1
    field_simp [hzlog.ne', htwo.ne']
    <;> ring
  rw [hmax, Real.rpow_def_of_pos hZp, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  field_simp [hzlog.ne']
  <;> ring

/-- The exact bridge from the full numerical exponent to the summable grid. -/
theorem real_width_penalty_le_weight {Z a T : ℝ} (hZ : 1 < Z) (ha : 1 ≤ a)
    (M : ℕ) (hcut : T * Real.log Z / Real.log 2 ≤ M) (i : ℕ × ℕ) :
    Z ^ (-a * max (((i.1 : ℝ) + 3 * i.2) * Real.log 2 / Real.log Z - T) 0) ≤
      weight M i := by
  rw [real_width_penalty_eq hZ]
  exact real_penalty_le_weight ha M hcut i

/-- A natural ceiling for a possibly negative dual threshold has no larger
than the expected affine logarithmic/annular size. -/
theorem ceiling_cutoff_affine {Z A B C k L : ℝ}
    (hZ : 1 ≤ Z) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hL : L ≤ A * Real.log Z + B * |k| + C) :
    (Nat.ceil (max L 0) : ℝ) ≤ A * Real.log Z + B * |k| + C + 1 := by
  have hb : 0 ≤ A * Real.log Z + B * |k| + C := by
    have := Real.log_nonneg hZ
    positivity
  have hm : max L 0 ≤ A * Real.log Z + B * |k| + C := max_le hL hb
  have hc := Nat.ceil_lt_add_one (le_max_right L 0)
  linarith

/-- An explicit logarithmic small-power estimate, valid for every `Z ≥ 1`. -/
theorem log_square_small_power {Z eps : ℝ} (hZ : 1 ≤ Z) (heps : 0 < eps) :
    (1 + Real.log Z) ^ 2 ≤ (1 + 2 / eps) ^ 2 * Z ^ eps := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hp : 0 < eps / 2 := by linarith
  have hl := Real.log_le_rpow_div hZp.le hp
  have hpow := Real.one_le_rpow hZ hp.le
  have hbase : 1 + Real.log Z ≤ (1 + 2 / eps) * Z ^ (eps / 2) := by
    have he : Z ^ (eps / 2) / (eps / 2) = (2 / eps) * Z ^ (eps / 2) := by ring
    rw [he] at hl
    nlinarith
  calc
    _ ≤ ((1 + 2 / eps) * Z ^ (eps / 2)) ^ 2 :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg hZ]) hbase 2
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hZp.le]
      congr 1
      congr 1
      ring

/-- Annular shifts cost a fixed exponential weight, which the actual
log-Gaussian seminorm estimates can absorb for any fixed rate. -/
theorem annulus_polynomial_le_exp (x : ℝ) :
    (1 + |x|) ^ 2 ≤ Real.exp (2 * |x|) := by
  have h := Real.add_one_le_exp |x|
  have h' : 1 + |x| ≤ Real.exp |x| := by linarith
  calc
    _ ≤ (Real.exp |x|) ^ 2 := pow_le_pow_left₀ (by positivity) h' 2
    _ = Real.exp (2 * |x|) := by rw [pow_two, ← Real.exp_add]; congr 1; ring

/-- The varying annular error is exactly an exponential weight in its index. -/
theorem log_error_power_identity {Z : ℝ} (hZ : 1 < Z) (a delta k C : ℝ) :
    Z ^ (a * (delta + (|k| + C) / Real.log Z)) =
      Z ^ (a * delta) * Real.exp (a * (|k| + C)) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hlog : Real.log Z ≠ 0 := (Real.log_pos hZ).ne'
  have he : a * (delta + (|k| + C) / Real.log Z) =
      a * delta + (a * (|k| + C)) / Real.log Z := by ring
  rw [he, Real.rpow_add hZp]
  congr 1
  rw [Real.rpow_def_of_pos hZp]
  congr 1
  field_simp [hlog]

/-- A shell cutoff affine in `log Z` and `|k|` gives one small power in Z
and one fixed exponential weight in k, uniformly over every annulus. -/
theorem affine_cutoff_square_bound {Z eps A B C k : ℝ} (M : ℕ)
    (hZ : 1 ≤ Z) (heps : 0 < eps) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hM : (M : ℝ) ≤ A * Real.log Z + B * |k| + C) :
    ((M : ℝ) + 2) ^ 2 ≤
      (A + B + C + 2) ^ 2 * (1 + 2 / eps) ^ 2 * Z ^ eps * Real.exp (2 * |k|) := by
  let D := A + B + C + 2
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hx : 0 ≤ Real.log Z := Real.log_nonneg hZ
  have hy : 0 ≤ |k| := abs_nonneg k
  have hD1 : A ≤ D := by dsimp [D]; linarith
  have hD2 : B ≤ D := by dsimp [D]; linarith
  have hD3 : C + 2 ≤ D := by dsimp [D]; linarith
  have hbase : (M : ℝ) + 2 ≤ D * (1 + Real.log Z) * (1 + |k|) := by
    have ha := mul_le_mul_of_nonneg_right hD1 hx
    have hb := mul_le_mul_of_nonneg_right hD2 hy
    have hxy : 0 ≤ D * Real.log Z * |k| := by positivity
    nlinarith
  calc
    _ ≤ (D * (1 + Real.log Z) * (1 + |k|)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hbase 2
    _ = D ^ 2 * (1 + Real.log Z) ^ 2 * (1 + |k|) ^ 2 := by ring
    _ ≤ D ^ 2 * ((1 + 2 / eps) ^ 2 * Z ^ eps) * Real.exp (2 * |k|) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (log_square_small_power hZ heps) (sq_nonneg D)
      · exact annulus_polynomial_le_exp k
      · exact sq_nonneg _
      · positivity
    _ = _ := by dsimp [D]; ring

#print axioms summable_weight_and_tsum_le
#print axioms finite_weight_sum_le
#print axioms real_width_penalty_le_weight
#print axioms ceiling_cutoff_affine
#print axioms log_square_small_power
#print axioms log_error_power_identity
#print axioms affine_cutoff_square_bound

end HeckeSkeleton.LowEnergy.DyadicTail
