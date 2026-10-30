import HeckeSkeleton.LowHybrid.BlockAdmissible
import Mathlib.Algebra.BigOperators.Field

/-!
# Exact accounting of the original column mass

Extracting D from a mark P preserves its normalized squared coefficient:
the factors 1/N(D) and 1/N(P/D) multiply to 1/N(P).  Interchanging the two
finite sums therefore charges each original mark only by the number of its
divisors.  Quotient reconstruction suffices; no cancellation hypothesis is
needed for this mass calculation.
-/

namespace HeckeSkeleton.LowHybrid.NormalForm

open scoped BigOperators Classical
noncomputable section

variable {I : Type*} [CommMonoid I]

namespace Arithmetic

variable (S : Arithmetic I)

/-- The divisor-extracted column mass equals the original normalized mass
restricted to marks divisible by that divisor. -/
theorem columnMass_div_eq (a : I → ℂ) (marks : Finset I) (d : I) :
    S.columnMass a marks d / S.normI d =
      ∑ p ∈ marks with d ∣ p, ‖a p‖ ^ 2 / S.normI p := by
  unfold columnMass markQuotients
  rw [Finset.sum_div, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    have hdp : d ∣ p := (Finset.mem_filter.mp hp).2
    rw [div_div, mul_comm (S.normI (S.quotient d p)) (S.normI d),
      ← S.norm_mul, S.quotient_spec d p hdp]
  · intro p hp q hq hpq
    rw [← S.quotient_spec d p (Finset.mem_filter.mp hp).2,
      ← S.quotient_spec d q (Finset.mem_filter.mp hq).2, hpq]

/-- The full D-column mass is controlled by the divisor count of each
original mark. Completeness is required only for divisors of those marks,
and is automatic for squarefree marks in the prime-coordinate instance. -/
theorem columnMass_sum_le_divisors
    (a : I → ℂ) (marks ds : Finset I) (D : ℝ)
    (hcomplete : ∀ p ∈ marks, ∀ d : I, d ∣ p → d ∈ S.divisors p)
    (hcount : ∀ p ∈ marks, ((S.divisors p).card : ℝ) ≤ D) :
    (∑ d ∈ ds, S.columnMass a marks d / S.normI d) ≤
      D * ∑ p ∈ marks, ‖a p‖ ^ 2 / S.normI p := by
  calc
    _ = ∑ d ∈ ds, ∑ p ∈ marks, if d ∣ p then ‖a p‖ ^ 2 / S.normI p else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [S.columnMass_div_eq, Finset.sum_filter]
    _ = ∑ p ∈ marks, ∑ d ∈ ds, if d ∣ p then ‖a p‖ ^ 2 / S.normI p else 0 :=
      Finset.sum_comm
    _ ≤ ∑ p ∈ marks, D * (‖a p‖ ^ 2 / S.normI p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hsubset : (ds.filter fun d => d ∣ p) ⊆ S.divisors p := by
        intro d hd
        exact hcomplete p hp d (Finset.mem_filter.mp hd).2
      have hcard : ((ds.filter fun d => d ∣ p).card : ℝ) ≤ D :=
        (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans (hcount p hp)
      calc
        _ = ∑ d ∈ ds with d ∣ p, ‖a p‖ ^ 2 / S.normI p :=
          (Finset.sum_filter ..).symm
        _ = ((ds.filter fun d => d ∣ p).card : ℝ) * (‖a p‖ ^ 2 / S.normI p) := by
          simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard
          (div_nonneg (sq_nonneg _) (S.norm_nonneg p))
    _ = _ := (Finset.mul_sum ..).symm

end Arithmetic

#print axioms Arithmetic.columnMass_div_eq
#print axioms Arithmetic.columnMass_sum_le_divisors

end
end HeckeSkeleton.LowHybrid.NormalForm
