import HeckeSkeleton.HighBinSupport.HighNormFormSlots
import Mathlib.Topology.Algebra.InfiniteSum.Basic
/-!
General finite-mark Euler algebra for the full correction.

Only the selected H factors are divided out, and their nonvanishing is an
explicit local premise.  It follows in the application from |H_p-1|<1 at
the prime-window cutoff.  No Gauss polynomial is divided out.  Arbitrary
zeros in unselected H factors or in compensated factors are retained.
-/

noncomputable section
namespace HighBinVerified.NormForm
open scoped BigOperators

/-- A finite set of actual whole-index marks replaces only its own local
Euler factors. -/
def markedEulerProduct {Prime : Type*} [DecidableEq Prime]
    (H marked : Prime → ℂ) (Q : Finset Prime) : ℂ :=
  ∏' p, if p ∈ Q then marked p else H p

/-- Finite local replacement inside a genuinely convergent Euler product.
No nonvanishing premise is imposed away from Q. -/
theorem markedEulerProduct_eq {Prime : Type*} [DecidableEq Prime]
    (H marked : Prime → ℂ) (total : ℂ) (hH : HasProd H total)
    (Q : Finset Prime) (hne : ∀ p ∈ Q, H p ≠ 0) :
    markedEulerProduct H marked Q = total * ∏ p ∈ Q, marked p / H p := by
  have hfinite : HasProd
      (fun p => if p ∈ Q then marked p / H p else 1)
      (∏ p ∈ Q, marked p / H p) := by
    have hh := hasProd_prod_of_ne_finset_one (s := Q)
      (f := fun p => if p ∈ Q then marked p / H p else (1 : ℂ))
      (L := SummationFilter.unconditional Prime)
      (fun p hp => if_neg hp)
    simpa only [Finset.prod_ite_mem, Finset.inter_self] using hh
  have hp := hH.mul hfinite
  have hfun : (fun p => H p * (if p ∈ Q then marked p / H p else 1)) =
      (fun p => if p ∈ Q then marked p else H p) := by
    funext p
    by_cases hp : p ∈ Q
    · simp only [if_pos hp]
      field_simp [hne p hp]
    · simp [hp]
  rw [hfun] at hp
  exact hp.tprod_eq

/-- Every marked/unmarked subset of one prime tuple is exactly a product
of its complete compensated local factors. -/
theorem finite_compensation_factorization {Prime : Type*} [DecidableEq Prime]
    (H marked A B : Prime → ℂ) (total : ℂ) (hH : HasProd H total)
    (S : Finset Prime) (hne : ∀ p ∈ S, H p ≠ 0) :
    (∑ Q ∈ S.powerset,
      (∏ p ∈ Q, A p) * (∏ p ∈ S \ Q, -B p) * markedEulerProduct H marked Q) =
      total * ∏ p ∈ S, (A p * marked p - B p * H p) / H p := by
  have hterm : ∀ Q ∈ S.powerset,
      (∏ p ∈ Q, A p) * (∏ p ∈ S \ Q, -B p) * markedEulerProduct H marked Q =
        total * ((∏ p ∈ Q, A p * (marked p / H p)) * ∏ p ∈ S \ Q, -B p) := by
    intro Q hQ
    have hQS : Q ⊆ S := Finset.mem_powerset.mp hQ
    rw [markedEulerProduct_eq H marked total hH Q (fun p hp => hne p (hQS hp)),
      Finset.prod_mul_distrib]
    ring
  calc
    _ = ∑ Q ∈ S.powerset,
        total * ((∏ p ∈ Q, A p * (marked p / H p)) * ∏ p ∈ S \ Q, -B p) :=
      Finset.sum_congr rfl hterm
    _ = total * ∏ p ∈ S, (A p * (marked p / H p) + -B p) := by
      rw [← Finset.mul_sum, ← Finset.prod_add]
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      field_simp [hne p hp]
      ring

/-- Complete prime-window tuples separate into genuine finite prime sums.
Pairwise-disjoint windows are needed only when transporting each tuple
to the distinct-prime Euler identity above. -/
theorem finite_prime_windows_separate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Prime : ι → Type*) [∀ i, Fintype (Prime i)]
    (total : ℂ) (factor : ∀ i, Prime i → ℂ) :
    (∑ tuple : (∀ i, Prime i), total * ∏ i, factor i (tuple i)) =
      total * ∏ i, ∑ p : Prime i, factor i p := by
  classical
  rw [← Finset.mul_sum]
  congr 1
  exact (Fintype.prod_sum factor).symm

end HighBinVerified.NormForm

#print axioms HighBinVerified.NormForm.markedEulerProduct_eq
#print axioms HighBinVerified.NormForm.finite_compensation_factorization
#print axioms HighBinVerified.NormForm.finite_prime_windows_separate
