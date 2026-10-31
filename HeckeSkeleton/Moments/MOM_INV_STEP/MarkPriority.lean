module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Ordered priority for the actual ideal divisibility marks

The source coefficient is written literally as a product of prime sums,
the divisibility form of the existing
`HeckePort.Moments.ideal_primeMark_eq_divisibility` interface. The proof
uses prime divisibility of a product directly on the extracted ideals.

Every extraction retains the original coefficient function. A prime
shared by several extracted factors is assigned at its first occurrence;
later slot lists delete it. The two copies in a squared column choose
their assigned slots independently. The final theorem specializes to the
actual integral ideals of an arbitrary number field.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep

open scoped Classical BigOperators NumberField

variable {σ M : Type*} [DecidableEq σ] [DecidableEq M] [CommMonoidWithZero M]

/-- The manuscript's literal product of prime divisibility sums. -/
def divisorMark (I : Finset σ) (L : σ → Finset M) (a : σ → M → ℂ) (n : M) : ℂ :=
  ∏ i ∈ I, ∑ P ∈ L i, if P ∣ n then a i P else 0

def residualDivisorLists (D : M) (L : σ → Finset M) : σ → Finset M :=
  fun i => (L i).filter (fun P => ¬ P ∣ D)

theorem slot_priority (L : Finset M) (a : M → ℂ) (D n : M)
    (hL : ∀ P ∈ L, Prime P) :
    (∑ P ∈ L, if P ∣ D * n then a P else 0) =
      (∑ P ∈ L, if P ∣ D then a P else 0) +
        ∑ P ∈ L.filter (fun P => ¬ P ∣ D), if P ∣ n then a P else 0 := by
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P hP
  rw [(hL P hP).dvd_mul]
  by_cases hD : P ∣ D <;> by_cases hn : P ∣ n <;> simp [hD, hn]

theorem mark_priority (I : Finset σ) (L : σ → Finset M)
    (a : σ → M → ℂ) (D n : M) (hL : ∀ i ∈ I, ∀ P ∈ L i, Prime P) :
    divisorMark I L a (D * n) =
      ∑ J ∈ I.powerset, divisorMark J L a D *
        divisorMark (I \ J) (residualDivisorLists D L) a n := by
  unfold divisorMark
  calc
    _ = ∏ i ∈ I,
        ((∑ P ∈ L i, if P ∣ D then a i P else 0) +
          ∑ P ∈ residualDivisorLists D L i, if P ∣ n then a i P else 0) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact slot_priority (L i) (a i) D n (hL i hi)
    _ = _ := Finset.prod_add _ _ I

/-- Each extracted factor receives a slot at the first stage at which its
prime divides. Every remaining slot uses the original coefficient function. -/
def priorityMarkExpansion (Ds : List M) (I : Finset σ) (L : σ → Finset M)
    (a : σ → M → ℂ) (n : M) : ℂ :=
  match Ds with
  | [] => divisorMark I L a n
  | D :: Ds => ∑ J ∈ I.powerset, divisorMark J L a D *
      priorityMarkExpansion Ds (I \ J) (residualDivisorLists D L) a n

theorem primeMark_priority_list (Ds : List M) (I : Finset σ) (L : σ → Finset M)
    (a : σ → M → ℂ) (n : M) (hL : ∀ i ∈ I, ∀ P ∈ L i, Prime P) :
    divisorMark I L a (Ds.prod * n) = priorityMarkExpansion Ds I L a n := by
  induction Ds generalizing I L with
  | nil => simp [priorityMarkExpansion]
  | cons D Ds ih =>
      rw [List.prod_cons, mul_assoc, mark_priority I L a D (Ds.prod * n) hL,
        priorityMarkExpansion]
      apply Finset.sum_congr rfl
      intro J hJ
      congr 1
      apply ih
      intro i hi P hP
      exact hL i (Finset.mem_sdiff.mp hi).1 P (Finset.mem_filter.mp hP).1

theorem residual_lists_preserve (I J : Finset σ) (D : M)
    (L : σ → Finset M) (a : σ → M → ℂ) (hJI : J ⊆ I)
    (hdis : (I : Set σ).PairwiseDisjoint L)
    (ha : ∀ i ∈ I, ∀ P ∈ L i, ‖a i P‖ ≤ 1) :
    (J : Set σ).PairwiseDisjoint (residualDivisorLists D L) ∧
      (∀ i ∈ J, ∀ P ∈ residualDivisorLists D L i, ‖a i P‖ ≤ 1) ∧
      (∀ i ∈ J, ∀ P ∈ residualDivisorLists D L i, ¬ P ∣ D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj hij
    exact (hdis (hJI hi) (hJI hj) hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  · intro i hi P hP
    exact ha i (hJI hi) P (Finset.mem_filter.mp hP).1
  · intro i hi P hP
    exact (Finset.mem_filter.mp hP).2

def residualPrimeLists (Ds : List M) (L : σ → Finset M) : σ → Finset M :=
  match Ds with
  | [] => L
  | D :: Ds => residualPrimeLists Ds (residualDivisorLists D L)

theorem mem_residualPrimeLists (Ds : List M) (L : σ → Finset M) (i : σ) (P : M) :
    P ∈ residualPrimeLists Ds L i ↔ P ∈ L i ∧ ∀ D ∈ Ds, ¬ P ∣ D := by
  induction Ds generalizing L with
  | nil => simp [residualPrimeLists]
  | cons D Ds ih =>
      rw [residualPrimeLists, ih]
      simp only [residualDivisorLists, Finset.mem_filter, List.forall_mem_cons, and_assoc]

theorem residualPrimeLists_subset (Ds : List M) (L : σ → Finset M) (i : σ) :
    residualPrimeLists Ds L i ⊆ L i := by
  intro P hP
  exact ((mem_residualPrimeLists Ds L i P).mp hP).1

theorem residual_prime_lists (Ds : List M) (I J : Finset σ)
    (L : σ → Finset M) (a : σ → M → ℂ) (hJI : J ⊆ I)
    (hdis : (I : Set σ).PairwiseDisjoint L)
    (ha : ∀ i ∈ I, ∀ P ∈ L i, ‖a i P‖ ≤ 1) :
    (J : Set σ).PairwiseDisjoint (residualPrimeLists Ds L) ∧
      (∀ i ∈ J, ∀ P ∈ residualPrimeLists Ds L i, ‖a i P‖ ≤ 1) ∧
      (∀ i ∈ J, ∀ P ∈ residualPrimeLists Ds L i, ∀ D ∈ Ds, ¬ P ∣ D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj hij
    exact (hdis (hJI hi) (hJI hj) hij).mono
      (residualPrimeLists_subset Ds L i) (residualPrimeLists_subset Ds L j)
  · intro i hi P hP
    exact ha i (hJI hi) P (residualPrimeLists_subset Ds L i hP)
  · intro i hi P hP
    exact ((mem_residualPrimeLists Ds L i P).mp hP).2

/-- The two occurrences of each slot make independent choices in an
expanded square. No coprimality between extracted factors is required. -/
theorem primeMark_priority_two_columns (I : Finset σ) (L : σ → Finset M)
    (a : σ → M → ℂ) (D₁ D₂ n₁ n₂ : M)
    (hL : ∀ i ∈ I, ∀ P ∈ L i, Prime P) :
    divisorMark I L a (D₁ * n₁) * star (divisorMark I L a (D₂ * n₂)) =
      ∑ J₁ ∈ I.powerset, ∑ J₂ ∈ I.powerset,
        (divisorMark J₁ L a D₁ * divisorMark (I \ J₁) (residualDivisorLists D₁ L) a n₁) *
        star (divisorMark J₂ L a D₂ * divisorMark (I \ J₂) (residualDivisorLists D₂ L) a n₂) := by
  rw [mark_priority I L a D₁ n₁ hL, mark_priority I L a D₂ n₂ hL]
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- Ordered priority for the actual integral ideals and literal mark
coefficients appearing in the canonical source. -/
theorem ideal_divisibility_mark_priority_list {K : Type*} [Field K] [NumberField K]
    (Ds : List (Ideal (𝓞 K))) (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (n : Ideal (𝓞 K))
    (hL : ∀ i ∈ I, ∀ P ∈ L i, Prime P) :
    (∏ i ∈ I, ∑ P ∈ L i, if P ∣ Ds.prod * n then a i P else 0) =
      priorityMarkExpansion Ds I L a n :=
  primeMark_priority_list Ds I L a n hL

end HeckeSkeleton.Moments.MOMInvStep

end
