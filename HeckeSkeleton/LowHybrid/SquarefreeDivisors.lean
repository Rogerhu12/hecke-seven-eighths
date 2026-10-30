import HeckeSkeleton.LowHybrid.Losses
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Squarefree divisor counts have a uniform small-power bound

Every squarefree divisor chooses a subset of prime support. Separate the
finitely many primes whose eta-th norm power is below 2. All other support
choices are paid for by the eta-th norm power itself. This establishes the
needed divisor loss without importing a divisor-function asymptotic theorem.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators
noncomputable section

/-- The finite small-prime argument, before choosing a norm cutoff. -/
theorem support_power_two_le_product
    {P : Type*} [DecidableEq P] (q : P → ℝ) (bad s : Finset P) (eta : ℝ)
    (heta : 0 ≤ eta) (hq : ∀ p : P, 1 ≤ q p)
    (hgood : ∀ p : P, p ∉ bad → 2 ≤ q p ^ eta) :
    (2 : ℝ) ^ s.card ≤
      (2 : ℝ) ^ bad.card * ∏ p ∈ s, q p ^ eta := by
  let cost : P → ℝ := fun p => if p ∈ bad then 2 else 1
  have hpoint (p : P) : (2 : ℝ) ≤ cost p * q p ^ eta := by
    by_cases hp : p ∈ bad
    · simp only [cost, if_pos hp]
      have := Real.one_le_rpow (hq p) heta
      nlinarith
    · simpa only [cost, if_neg hp, one_mul] using hgood p hp
  have hcost : (∏ p ∈ s, cost p) ≤ (2 : ℝ) ^ bad.card := by
    calc
      (∏ p ∈ s, cost p) = (2 : ℝ) ^ (s ∩ bad).card := by
        simp only [cost, Finset.prod_ite_mem, Finset.prod_const]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Finset.card_le_card Finset.inter_subset_right)
  have hprod0 : 0 ≤ ∏ p ∈ s, q p ^ eta := by
    apply Finset.prod_nonneg
    intro p hp
    exact Real.rpow_nonneg (le_trans zero_le_one (hq p)) eta
  calc
    (2 : ℝ) ^ s.card = ∏ _p ∈ s, (2 : ℝ) := by simp
    _ ≤ ∏ p ∈ s, cost p * q p ^ eta :=
      Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun p _ => hpoint p)
    _ = (∏ p ∈ s, cost p) * ∏ p ∈ s, q p ^ eta := Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_right hcost hprod0

/-- Primes outside the cutoff q < 2^(1/eta) have enough norm to pay for
their binary choice in a squarefree divisor. -/
theorem prime_power_ge_two_outside_cutoff
    {P : Type*} (q : P → ℝ) (bad : Finset P) (eta : ℝ) (heta : 0 < eta)
    (hbad : ∀ p : P, q p < (2 : ℝ) ^ (1 / eta) → p ∈ bad) :
    ∀ p : P, p ∉ bad → 2 ≤ q p ^ eta := by
  intro p hp
  have hbase : (2 : ℝ) ^ (1 / eta) ≤ q p := by
    by_contra h
    exact hp (hbad p (lt_of_not_ge h))
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) (1 / eta))
    hbase (le_of_lt heta)
  have heq : ((2 : ℝ) ^ (1 / eta)) ^ eta = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have he : (1 / eta) * eta = 1 := by field_simp [ne_of_gt heta]
    rw [he, Real.rpow_one]
  simpa only [heq] using h

/-- Finiteness of bounded prime norms implies the squarefree-support
small-power bound, with its constant chosen before the support. -/
theorem squarefree_support_subpower
    {P : Type*} (q : P → ℝ) (hq : ∀ p : P, 1 ≤ q p)
    (hfinite : ∀ X : ℝ, Set.Finite {p : P | q p ≤ X})
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset P,
      (2 : ℝ) ^ s.card ≤ C * (∏ p ∈ s, q p) ^ eta := by
  classical
  let bad := (hfinite ((2 : ℝ) ^ (1 / eta))).toFinset
  have hbad : ∀ p : P, q p < (2 : ℝ) ^ (1 / eta) → p ∈ bad := by
    intro p hp
    exact (hfinite _).mem_toFinset.mpr (le_of_lt hp)
  have hgood := prime_power_ge_two_outside_cutoff q bad eta heta hbad
  refine ⟨(2 : ℝ) ^ bad.card, pow_pos (by norm_num) _, ?_⟩
  intro s
  have h := support_power_two_le_product q bad s eta (le_of_lt heta) hq hgood
  rw [Real.finsetProd_rpow s q (fun p _ => le_trans zero_le_one (hq p)) eta] at h
  exact h

/-- A cutoff-finset formulation of the same small-prime argument. -/
theorem squarefree_support_subpower_of_cutoffs
    {P : Type*} (q : P → ℝ) (hq : ∀ p : P, 1 ≤ q p)
    (cutoff : ℝ → Finset P)
    (hmem : ∀ X : ℝ, ∀ p : P, q p ≤ X → p ∈ cutoff X)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset P,
      (2 : ℝ) ^ s.card ≤ C * (∏ p ∈ s, q p) ^ eta := by
  exact squarefree_support_subpower q hq
    (fun X => (cutoff X).finite_toSet.subset (fun p hp => hmem X p hp)) eta heta

/-- The powerset bound for divisors and the prime-product lower bound for
the norm give a genuine uniform divisor-count small-power theorem. -/
theorem squarefree_divisor_count_subpower
    {I P : Type*} (support : I → Finset P) (divisors : I → Finset I)
    (primeNorm : P → ℝ) (normI : I → ℝ)
    (hp : ∀ p : P, 1 ≤ primeNorm p)
    (hfinite : ∀ X : ℝ, Set.Finite {p : P | primeNorm p ≤ X})
    (hcard : ∀ i : I, ((divisors i).card : ℝ) ≤ (2 : ℝ) ^ (support i).card)
    (hnorm : ∀ i : I, (∏ p ∈ support i, primeNorm p) ≤ normI i)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : I, ((divisors i).card : ℝ) ≤ C * normI i ^ eta := by
  obtain ⟨C, hC, hb⟩ := squarefree_support_subpower primeNorm hp hfinite eta heta
  refine ⟨C, hC, ?_⟩
  intro i
  have hprod : 0 ≤ ∏ p ∈ support i, primeNorm p :=
    Finset.prod_nonneg (fun p _ => le_trans zero_le_one (hp p))
  calc
    ((divisors i).card : ℝ) ≤ (2 : ℝ) ^ (support i).card := hcard i
    _ ≤ C * (∏ p ∈ support i, primeNorm p) ^ eta := hb (support i)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hprod (hnorm i) (le_of_lt heta)) (le_of_lt hC)

#print axioms support_power_two_le_product
#print axioms prime_power_ge_two_outside_cutoff
#print axioms squarefree_support_subpower
#print axioms squarefree_divisor_count_subpower

end
end HeckeSkeleton.LowHybrid
