import HeckeSkeleton.LowFrozenCube.FrozenCounts

/-!
# The positive partition of original rows by their actual frozen factors

Every row belongs to exactly one pair of canonical powerful and supported
factors. Thus summing the fixed-block estimates costs the number of actual
frozen pairs, with no further Cauchy--Schwarz factor.
-/

namespace HeckeSkeleton.LowFrozenCube

open scoped BigOperators Classical
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates

noncomputable section

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

theorem sum_rows_eq_frozen_blocks
    {R : Type*} [AddCommMonoid R] (support : Finset ι)
    (rows : Finset A) (F : A → R) :
    (∑ k ∈ rows, F k) =
      ∑ pair ∈ frozenRowPairs coords support rows,
        ∑ k ∈ rowBlock coords support pair.1 pair.2 rows, F k := by
  have hm : ∀ k ∈ rows,
      (powerfulRowFactor coords k, supportedRowFactor coords support k) ∈
        frozenRowPairs coords support rows := by
    intro k hk
    exact Finset.mem_image_of_mem _ hk
  calc
    (∑ k ∈ rows, F k) =
        ∑ pair ∈ frozenRowPairs coords support rows,
          ∑ k ∈ rows with
            (powerfulRowFactor coords k, supportedRowFactor coords support k) = pair,
            F k := (Finset.sum_fiberwise_of_maps_to hm F).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro pair hpair
      apply Finset.sum_congr
      · ext k
        simp [rowBlock, Prod.ext_iff]
      · intro k hk
        rfl

/-- A uniform fixed-block bound is summed positively. The multiplier is
the cardinality already bounded by the powerful and supported counts. -/
theorem sum_rows_le_frozen_card_mul
    (support : Finset ι) (rows : Finset A) (F : A → ℝ) (E : ℝ)
    (hblock : ∀ pair ∈ frozenRowPairs coords support rows,
      (∑ k ∈ rowBlock coords support pair.1 pair.2 rows, F k) ≤ E) :
    (∑ k ∈ rows, F k) ≤ ((frozenRowPairs coords support rows).card : ℝ) * E := by
  rw [sum_rows_eq_frozen_blocks coords support rows F]
  calc
    _ ≤ ∑ _pair ∈ frozenRowPairs coords support rows, E :=
      Finset.sum_le_sum hblock
    _ = _ := by simp

#print axioms sum_rows_eq_frozen_blocks
#print axioms sum_rows_le_frozen_card_mul

end
end HeckeSkeleton.LowFrozenCube
