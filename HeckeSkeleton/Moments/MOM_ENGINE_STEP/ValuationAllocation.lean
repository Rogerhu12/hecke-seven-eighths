module

public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic

/-!
# Exact valuation allocations for the three amplification errors

The valuation of the entire product is partitioned among all factor
occurrences.  This is a disjoint exact-valuation partition, separate
from the squarefree divisor inclusion-exclusion.  The whole coefficient
is unchanged and the number of depth-at-most-seven allocations is at
most eight to the number of occurrences.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep.ValuationAllocation

def choices (k j : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ : Fin k => Finset.range (j + 1))).filter (fun n => ∑ i, n i = j)

theorem mem_choices_of_sum {k j : ℕ} (n : Fin k → ℕ) (hn : ∑ i, n i = j) :
    n ∈ choices k j := by
  apply Finset.mem_filter.mpr
  refine ⟨Fintype.mem_piFinset.mpr ?_, hn⟩
  intro i
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  rw [← hn]
  exact Finset.single_le_sum (fun l _ => Nat.zero_le (n l)) (Finset.mem_univ i)

theorem sum_of_mem_choices {k j : ℕ} {n : Fin k → ℕ} (hn : n ∈ choices k j) :
    ∑ i, n i = j := (Finset.mem_filter.mp hn).2

theorem card_choices_le (k j : ℕ) : (choices k j).card ≤ (j + 1) ^ k := by
  calc
    _ ≤ (Fintype.piFinset (fun _ : Fin k => Finset.range (j + 1))).card :=
      Finset.card_filter_le _ _
    _ = _ := by simp

theorem card_choices_le_eight (k j : ℕ) (hj : j ≤ 7) :
    (choices k j).card ≤ 8 ^ k :=
  (card_choices_le k j).trans (Nat.pow_le_pow_left (by omega) k)

section Monoid

variable {M : Type*} [CommMonoidWithZero M] [Nontrivial M]
  [NormalizationMonoid M] [UniqueFactorizationMonoid M]

open UniqueFactorizationMonoid

theorem count_product {ι : Type*} (s : Finset ι) (a : ι → M) (p : M)
    (ha : ∀ i ∈ s, a i ≠ 0) :
    (normalizedFactors (∏ i ∈ s, a i)).count p =
      ∑ i ∈ s, (normalizedFactors (a i)).count p := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self _ _)
    have has : ∀ j ∈ s, a j ≠ 0 :=
      fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,
      normalizedFactors_mul hai (Finset.prod_ne_zero_iff.mpr has),
      Multiset.count_add, ih has, Finset.sum_insert hi]

theorem whole_polynomial {X : Type*} (columns : Finset X) (k j : ℕ)
    (p : M) (a : X → Fin k → M) (C : X → ℂ)
    (ha : ∀ x ∈ columns, ∀ i, a x i ≠ 0) :
    (∑ x ∈ columns with (normalizedFactors (∏ i, a x i)).count p = j, C x) =
      ∑ n ∈ choices k j,
        ∑ x ∈ columns with ∀ i, (normalizedFactors (a x i)).count p = n i, C x := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm (s := choices k j) (t := columns)]
  apply Finset.sum_congr rfl
  intro x hx
  let ν : Fin k → ℕ := fun i => (normalizedFactors (a x i)).count p
  have hc : (normalizedFactors (∏ i, a x i)).count p = ∑ i, ν i :=
    count_product Finset.univ (a x) p (fun i _ => ha x hx i)
  change (if (normalizedFactors (∏ i, a x i)).count p = j then C x else 0) =
    ∑ n ∈ choices k j, if ∀ i, ν i = n i then C x else 0
  rw [hc]
  by_cases he : ∑ i, ν i = j
  · rw [if_pos he]
    have hm := mem_choices_of_sum ν he
    have hp (n : Fin k → ℕ) : (∀ i, ν i = n i) ↔ n = ν := by
      constructor
      · intro h
        funext i
        exact (h i).symm
      · rintro rfl i
        rfl
    simp only [hp, Finset.sum_ite_eq', hm, if_true]
  · rw [if_neg he]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    apply if_neg
    intro h
    apply he
    calc
      (∑ i, ν i) = ∑ i, n i := Finset.sum_congr rfl (fun i _ => h i)
      _ = j := sum_of_mem_choices hn

theorem cartesian_filter {P : Type*} {k : ℕ} (S : Fin k → Finset P)
    (p : M) (a : Fin k → P → M) (n : Fin k → ℕ) :
    (Fintype.piFinset S).filter
        (fun x => ∀ i, (normalizedFactors (a i (x i))).count p = n i) =
      Fintype.piFinset (fun i => (S i).filter
        (fun x => (normalizedFactors (a i x)).count p = n i)) := by
  ext x
  simp only [Finset.mem_filter, Fintype.mem_piFinset, forall_and]

theorem whole_cartesian {P : Type*} (k j : ℕ) (S : Fin k → Finset P)
    (p : M) (a : Fin k → P → M) (C : (Fin k → P) → ℂ)
    (ha : ∀ i, ∀ x ∈ S i, a i x ≠ 0) :
    (∑ x ∈ Fintype.piFinset S with
      (normalizedFactors (∏ i, a i (x i))).count p = j, C x) =
      ∑ n ∈ choices k j,
        ∑ x ∈ Fintype.piFinset (fun i => (S i).filter
          (fun x => (normalizedFactors (a i x)).count p = n i)), C x := by
  simpa only [cartesian_filter] using
    whole_polynomial (Fintype.piFinset S) k j p (fun x i => a i (x i)) C
      (fun x hx i => ha i (x i) (Fintype.mem_piFinset.mp hx i))

end Monoid
end HeckeSkeleton.Moments.EngineStep.ValuationAllocation

#print axioms HeckeSkeleton.Moments.EngineStep.ValuationAllocation.whole_polynomial
#print axioms HeckeSkeleton.Moments.EngineStep.ValuationAllocation.whole_cartesian
