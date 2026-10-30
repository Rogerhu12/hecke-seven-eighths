import PrimeCancellationPrimePowers
import PrimeCancellationLogWindow
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Absolutely convergent prime-power window series

Uniform finite counting hypotheses imply absolute summability; summability
is proved here, not assumed as an input.  Every finite subset of the product
index set is enlarged to a finite rectangle, and the previously established
finite prime-power estimate bounds the resulting nonnegative sum.

The final decomposition uses the exact logarithmic-window identity.  It
does not assume an Euler product, Mellin inversion, or a zero-free region.
-/

set_option autoImplicit false
noncomputable section

namespace PrimeCancellationPrimeSeries

open scoped Classical BigOperators
open PrimeCancellationPrimePowers PrimeCancellationLogWindow

variable {α : Type*}

structure PrimeArithmetic (ν : α → ℝ) (a : α → ℂ) (d : ℝ) : Prop where
  d_nonneg : 0 ≤ d
  norm_ge_two : ∀ p, 2 ≤ ν p
  count : ∀ (pool : Finset α) (Y : ℝ), 0 ≤ Y →
    ((pool.filter (fun p => ν p ≤ Y)).card : ℝ) ≤ d * Y
  coeff_bound : ∀ p, ‖a p‖ ≤ 1

structure WindowBound (W : ℝ → ℂ) (M : ℝ) : Prop where
  nonneg : 0 ≤ M
  support : Function.support W ⊆ Set.Icc (1 : ℝ) 2
  bound : ∀ x, ‖W x‖ ≤ M

def primeSum (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ) : ℂ :=
  ∑' p, a p * W (ν p / P)

def tailSum (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ) : ℂ :=
  ∑' np : ℕ × α, primePowerWindowTerm ν a W P np.1 np.2

def allPowerTerm (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ)
    (P : ℝ) (n : ℕ) (p : α) : ℂ :=
  a p ^ (n + 1) * W (ν p ^ (n + 1) / P) / ((n + 1 : ℕ) : ℂ)

def logWeightedPowerTerm (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ)
    (P : ℝ) (n : ℕ) (p : α) : ℂ :=
  (Real.log (ν p) : ℂ) * a p ^ (n + 1) *
    logWindow P W (ν p ^ (n + 1) / P)

def weightedSum (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ) : ℂ :=
  ∑' np : ℕ × α, logWeightedPowerTerm ν a W P np.1 np.2

/-! ## From rectangles to arbitrary finite subsets -/

theorem finite_set_norm_le_of_rectangle_bound (f : ℕ → α → ℂ) (B : ℝ)
    (hrect : ∀ (pool : Finset α) (N : ℕ),
      (∑ n ∈ Finset.range N, ∑ p ∈ pool, ‖f n p‖) ≤ B)
    (s : Finset (ℕ × α)) :
    (∑ np ∈ s, ‖f np.1 np.2‖) ≤ B := by
  let pool : Finset α := s.image Prod.snd
  let N : ℕ := s.sup Prod.fst + 1
  have hsubset : s ⊆ (Finset.range N).product pool := by
    intro np hnp
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      change np.1 < s.sup Prod.fst + 1
      exact Nat.lt_succ_of_le (Finset.le_sup hnp)
    · exact Finset.mem_image.mpr ⟨np, hnp, rfl⟩
  calc
    (∑ np ∈ s, ‖f np.1 np.2‖) ≤
        ∑ np ∈ (Finset.range N).product pool, ‖f np.1 np.2‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => norm_nonneg _)
    _ = ∑ n ∈ Finset.range N, ∑ p ∈ pool, ‖f n p‖ :=
      Finset.sum_product (Finset.range N) pool (fun np : ℕ × α => ‖f np.1 np.2‖)
    _ ≤ B := hrect pool N

theorem summable_norm_of_rectangle_bound (f : ℕ → α → ℂ) (B : ℝ)
    (hrect : ∀ (pool : Finset α) (N : ℕ),
      (∑ n ∈ Finset.range N, ∑ p ∈ pool, ‖f n p‖) ≤ B) :
    Summable (fun np : ℕ × α => ‖f np.1 np.2‖) := by
  exact summable_of_sum_le (fun _ => norm_nonneg _)
    (finite_set_norm_le_of_rectangle_bound f B hrect)

theorem tsum_norm_le_of_rectangle_bound (f : ℕ → α → ℂ) (B : ℝ)
    (hrect : ∀ (pool : Finset α) (N : ℕ),
      (∑ n ∈ Finset.range N, ∑ p ∈ pool, ‖f n p‖) ≤ B) :
    (∑' np : ℕ × α, ‖f np.1 np.2‖) ≤ B := by
  exact Real.tsum_le_of_sum_le (fun _ => norm_nonneg _)
    (finite_set_norm_le_of_rectangle_bound f B hrect)

theorem norm_tsum_le_of_rectangle_bound (f : ℕ → α → ℂ) (B : ℝ)
    (hrect : ∀ (pool : Finset α) (N : ℕ),
      (∑ n ∈ Finset.range N, ∑ p ∈ pool, ‖f n p‖) ≤ B) :
    ‖∑' np : ℕ × α, f np.1 np.2‖ ≤ B := by
  exact (norm_tsum_le_tsum_norm (summable_norm_of_rectangle_bound f B hrect)).trans
    (tsum_norm_le_of_rectangle_bound f B hrect)

/-! ## Absolute finite bounds -/

theorem sum_norm_tail_rectangle_le
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (d M P : ℝ)
    (hP : 0 < P) (hA : PrimeArithmetic ν a d) (hW : WindowBound W M)
    (pool : Finset α) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∑ p ∈ pool, ‖primePowerWindowTerm ν a W P n p‖) ≤
      M * d * (1 + Real.sqrt 2) * Real.sqrt P := by
  have hfilter (n : ℕ) :
      (∑ p ∈ pool, ‖primePowerWindowTerm ν a W P n p‖) =
        ∑ p ∈ powerCutoff pool ν (2 * P) (n + 2),
          ‖primePowerWindowTerm ν a W P n p‖ := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hcut : ¬ν p ^ (n + 2) ≤ 2 * P := by
      intro hpower
      exact hnot (Finset.mem_filter.mpr ⟨hp, hpower⟩)
    rw [primePowerWindowTerm_eq_zero_of_not_cutoff ν a W P n p hP hW.support hcut,
      norm_zero]
  have hrow (n : ℕ) :
      (∑ p ∈ powerCutoff pool ν (2 * P) (n + 2),
        ‖primePowerWindowTerm ν a W P n p‖) ≤
        ((powerCutoff pool ν (2 * P) (n + 2)).card : ℝ) * (M / 2) := by
    calc
      _ ≤ ∑ _p ∈ powerCutoff pool ν (2 * P) (n + 2), M / 2 := by
        apply Finset.sum_le_sum
        intro p _
        refine (norm_primePowerWindowTerm_le ν a W P M n p
          (hA.coeff_bound p) (hW.bound _)).trans ?_
        apply div_le_div_of_nonneg_left hW.nonneg (by norm_num : (0 : ℝ) < 2)
        exact_mod_cast (show 2 ≤ n + 2 by omega)
      _ = _ := by simp
  calc
    _ = ∑ n ∈ Finset.range N, ∑ p ∈ powerCutoff pool ν (2 * P) (n + 2),
          ‖primePowerWindowTerm ν a W P n p‖ :=
      Finset.sum_congr rfl (fun n _ => hfilter n)
    _ ≤ ∑ n ∈ Finset.range N,
        ((powerCutoff pool ν (2 * P) (n + 2)).card : ℝ) * (M / 2) :=
      Finset.sum_le_sum (fun n _ => hrow n)
    _ = (M / 2) * ∑ n ∈ Finset.range N,
        ((powerCutoff pool ν (2 * P) (n + 2)).card : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ (M / 2) * (d * Real.sqrt (2 * P) / (1 - ratio)) :=
      mul_le_mul_of_nonneg_left
        (sum_powerCutoff_cards_le pool ν d (2 * P) N hA.d_nonneg
          (mul_nonneg (by norm_num) hP.le) (fun p _ => hA.norm_ge_two p) (hA.count pool))
        (div_nonneg hW.nonneg (by norm_num))
    _ = M * d * Real.sqrt (2 * P) * (1 / (2 * (1 - ratio))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = M * d * (1 + ratio) * Real.sqrt (2 * P) := by
      rw [geometric_half_constant]
      ring
    _ = M * d * (1 + Real.sqrt 2) * Real.sqrt P := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        M * d * (1 + ratio) * (Real.sqrt 2 * Real.sqrt P) =
            M * d * ((1 + ratio) * Real.sqrt 2) * Real.sqrt P := by ring
        _ = _ := by rw [one_add_ratio_mul_sqrt_two]

theorem sum_norm_prime_le
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (d M P : ℝ)
    (hP : 0 < P) (hA : PrimeArithmetic ν a d) (hW : WindowBound W M)
    (pool : Finset α) :
    (∑ p ∈ pool, ‖a p * W (ν p / P)‖) ≤ 2 * M * d * P := by
  have hterm (p : α) : ‖a p * W (ν p / P)‖ ≤ M := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hA.coeff_bound p) (hW.bound (ν p / P))
      (norm_nonneg (W (ν p / P))) zero_le_one
  have hfilter : (∑ p ∈ pool, ‖a p * W (ν p / P)‖) =
      ∑ p ∈ pool.filter (fun p => ν p ≤ 2 * P), ‖a p * W (ν p / P)‖ := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hnorm : ¬ν p ≤ 2 * P := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨hp, h⟩)
    have harg : 2 < ν p / P := (lt_div_iff₀ hP).mpr (lt_of_not_ge hnorm)
    have hzero : W (ν p / P) = 0 := by
      by_contra hne
      exact (not_le_of_gt harg) (hW.support hne).2
    simp only [hzero, mul_zero, norm_zero]
  calc
    _ = ∑ p ∈ pool.filter (fun p => ν p ≤ 2 * P), ‖a p * W (ν p / P)‖ := hfilter
    _ ≤ ∑ _p ∈ pool.filter (fun p => ν p ≤ 2 * P), M :=
      Finset.sum_le_sum (fun p _ => hterm p)
    _ = ((pool.filter (fun p => ν p ≤ 2 * P)).card : ℝ) * M := by simp
    _ ≤ (d * (2 * P)) * M :=
      mul_le_mul_of_nonneg_right (hA.count pool (2 * P) (mul_nonneg (by norm_num) hP.le))
        hW.nonneg
    _ = 2 * M * d * P := by ring

/-! ## Infinite tails and the prime sum -/

theorem summable_norm_tail
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (d M P : ℝ)
    (hP : 0 < P) (hA : PrimeArithmetic ν a d) (hW : WindowBound W M) :
    Summable (fun np : ℕ × α => ‖primePowerWindowTerm ν a W P np.1 np.2‖) :=
  summable_norm_of_rectangle_bound (primePowerWindowTerm ν a W P)
    (M * d * (1 + Real.sqrt 2) * Real.sqrt P)
    (sum_norm_tail_rectangle_le ν a W d M P hP hA hW)

theorem norm_tailSum_le
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (d M P : ℝ)
    (hP : 0 < P) (hA : PrimeArithmetic ν a d) (hW : WindowBound W M) :
    ‖tailSum ν a W P‖ ≤ M * d * (1 + Real.sqrt 2) * Real.sqrt P :=
  norm_tsum_le_of_rectangle_bound (primePowerWindowTerm ν a W P)
    (M * d * (1 + Real.sqrt 2) * Real.sqrt P)
    (sum_norm_tail_rectangle_le ν a W d M P hP hA hW)

theorem summable_norm_prime
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (d M P : ℝ)
    (hP : 0 < P) (hA : PrimeArithmetic ν a d) (hW : WindowBound W M) :
    Summable (fun p : α => ‖a p * W (ν p / P)‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _)
    (sum_norm_prime_le ν a W d M P hP hA hW)

/-- The requested all-P trivial estimate, in particular for the small-P
part of an analytic estimate. It is not a cancellation estimate. -/
theorem norm_primeSum_le
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (d M P : ℝ)
    (hP : 0 < P) (hA : PrimeArithmetic ν a d) (hW : WindowBound W M) :
    ‖primeSum ν a W P‖ ≤ 2 * M * d * P := by
  exact (norm_tsum_le_tsum_norm (summable_norm_prime ν a W d M P hP hA hW)).trans
    (Real.tsum_le_of_sum_le (fun _ => norm_nonneg _)
      (sum_norm_prime_le ν a W d M P hP hA hW))

/-! ## Splitting off exponent one -/

theorem allPowerTerm_zero (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ) (p : α) :
    allPowerTerm ν a W P 0 p = a p * W (ν p / P) := by
  simp only [allPowerTerm, zero_add, pow_one, Nat.cast_one, div_one]

theorem allPowerTerm_add_one (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ)
    (P : ℝ) (n : ℕ) (p : α) :
    allPowerTerm ν a W P (n + 1) p = primePowerWindowTerm ν a W P n p := by
  simp only [allPowerTerm, primePowerWindowTerm, Nat.add_assoc]

theorem logWeightedPowerTerm_eq_allPowerTerm
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ) (n : ℕ) (p : α)
    (hP : 0 < P) (hnorm : 2 ≤ ν p) :
    logWeightedPowerTerm ν a W P n p = allPowerTerm ν a W P n p := by
  exact prime_power_log_cancellation P (ν p) (a p) W (n + 1) hP
    (by linarith) (by omega)

theorem summable_norm_allPowerTerm
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (d M P : ℝ)
    (hP : 0 < P) (hA : PrimeArithmetic ν a d) (hW : WindowBound W M) :
    Summable (fun np : ℕ × α => ‖allPowerTerm ν a W P np.1 np.2‖) := by
  have htail := summable_norm_tail ν a W d M P hP hA hW
  have hprime := summable_norm_prime ν a W d M P hP hA hW
  have hrows : ∀ n : ℕ, Summable (fun p : α => ‖allPowerTerm ν a W P n p‖) := by
    intro n
    cases n with
    | zero => simpa only [allPowerTerm_zero] using hprime
    | succ n => simpa only [Nat.succ_eq_add_one, allPowerTerm_add_one] using htail.prod_factor n
  have houter : Summable (fun n : ℕ => ∑' p : α, ‖allPowerTerm ν a W P n p‖) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [allPowerTerm_add_one] using htail.prod
  exact (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨hrows, houter⟩

theorem summable_norm_logWeightedPowerTerm
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (d M P : ℝ)
    (hP : 0 < P) (hA : PrimeArithmetic ν a d) (hW : WindowBound W M) :
    Summable (fun np : ℕ × α => ‖logWeightedPowerTerm ν a W P np.1 np.2‖) := by
  have heq : (fun np : ℕ × α => ‖logWeightedPowerTerm ν a W P np.1 np.2‖) =
      (fun np : ℕ × α => ‖allPowerTerm ν a W P np.1 np.2‖) := by
    funext np
    rw [logWeightedPowerTerm_eq_allPowerTerm ν a W P np.1 np.2 hP (hA.norm_ge_two np.2)]
  rw [heq]
  exact summable_norm_allPowerTerm ν a W d M P hP hA hW

theorem weightedSum_eq_primeSum_add_tailSum
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (d M P : ℝ)
    (hP : 0 < P) (hA : PrimeArithmetic ν a d) (hW : WindowBound W M) :
    weightedSum ν a W P = primeSum ν a W P + tailSum ν a W P := by
  have hfull : Summable (fun np : ℕ × α => allPowerTerm ν a W P np.1 np.2) :=
    (summable_norm_allPowerTerm ν a W d M P hP hA hW).of_norm
  have htail : Summable (fun np : ℕ × α => primePowerWindowTerm ν a W P np.1 np.2) :=
    (summable_norm_tail ν a W d M P hP hA hW).of_norm
  calc
    weightedSum ν a W P = ∑' np : ℕ × α, allPowerTerm ν a W P np.1 np.2 := by
      apply tsum_congr
      intro np
      exact logWeightedPowerTerm_eq_allPowerTerm ν a W P np.1 np.2 hP (hA.norm_ge_two np.2)
    _ = ∑' n : ℕ, ∑' p : α, allPowerTerm ν a W P n p := hfull.tsum_prod
    _ = primeSum ν a W P + tailSum ν a W P := by
      rw [← hfull.prod.sum_add_tsum_nat_add 1]
      simp only [Finset.sum_range_one, allPowerTerm_zero, allPowerTerm_add_one]
      rw [← htail.tsum_prod]
      rfl

#print axioms finite_set_norm_le_of_rectangle_bound
#print axioms summable_norm_of_rectangle_bound
#print axioms tsum_norm_le_of_rectangle_bound
#print axioms norm_tsum_le_of_rectangle_bound
#print axioms sum_norm_tail_rectangle_le
#print axioms sum_norm_prime_le
#print axioms summable_norm_tail
#print axioms norm_tailSum_le
#print axioms summable_norm_prime
#print axioms norm_primeSum_le
#print axioms allPowerTerm_zero
#print axioms allPowerTerm_add_one
#print axioms logWeightedPowerTerm_eq_allPowerTerm
#print axioms summable_norm_allPowerTerm
#print axioms summable_norm_logWeightedPowerTerm
#print axioms weightedSum_eq_primeSum_add_tailSum

end PrimeCancellationPrimeSeries
