import HeckeSkeleton.LowFrozenCube.FrozenPartition

/-!
# Adding frozen powerful primes does not change the residual row

On a block with powerful factor pow, every prime of pow has row valuation
at least two. Such a prime cannot occur in either valuation-one factor.
Thus the fixed exclusion set may include the support of pow without
changing the actual supported/residual factor or the original row block.
-/

namespace HeckeSkeleton.LowFrozenCube.PrimeCoordinates

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

def extendedFrozenSupport (base : Finset ι) (pow : A) : Finset ι :=
  base ∪ (valuation coords pow).support

theorem valuation_ne_one_of_mem_powerful_support (k pow : A)
    (hk : powerfulRowFactor coords k = pow) (p : ι)
    (hp : p ∈ (valuation coords pow).support) : valuation coords k p ≠ 1 := by
  have hp0 := Finsupp.mem_support_iff.mp hp
  have heq := congrArg (fun a => valuation coords a p) hk
  rw [valuation_powerfulRowFactor] at heq
  intro h1
  have hz : valuation coords pow p = 0 := by
    simpa [powerfulRowPart, h1] using heq.symm
  exact hp0 hz

theorem supportedRowFactor_extended (base : Finset ι) (k pow : A)
    (hk : powerfulRowFactor coords k = pow) :
    supportedRowFactor coords (extendedFrozenSupport coords base pow) k =
      supportedRowFactor coords base k := by
  apply valuation_injective coords
  ext p
  simp only [valuation_supportedRowFactor]
  by_cases hp : p ∈ (valuation coords pow).support
  · have hne := valuation_ne_one_of_mem_powerful_support coords k pow hk p hp
    simp [supportedRowPart, hne]
  · simp [supportedRowPart, extendedFrozenSupport, hp]

theorem residualRowFactor_extended (base : Finset ι) (k pow : A)
    (hk : powerfulRowFactor coords k = pow) :
    residualRowFactor coords (extendedFrozenSupport coords base pow) k =
      residualRowFactor coords base k := by
  apply valuation_injective coords
  ext p
  simp only [valuation_residualRowFactor]
  by_cases hp : p ∈ (valuation coords pow).support
  · have hne := valuation_ne_one_of_mem_powerful_support coords k pow hk p hp
    simp [residualRowPart, hne]
  · simp [residualRowPart, extendedFrozenSupport, hp]

/-- The actual original-row block is unchanged by the powerful-prime
exclusions attached to that block. -/
theorem rowBlock_extended (base : Finset ι) (pow sup : A) (rows : Finset A) :
    rowBlock coords (extendedFrozenSupport coords base pow) pow sup rows =
      rowBlock coords base pow sup rows := by
  ext k
  simp only [rowBlock, Finset.mem_filter]
  constructor
  · rintro ⟨hk, hpow, hsup⟩
    exact ⟨hk, hpow, (supportedRowFactor_extended coords base k pow hpow).symm.trans hsup⟩
  · rintro ⟨hk, hpow, hsup⟩
    exact ⟨hk, hpow, (supportedRowFactor_extended coords base k pow hpow).trans hsup⟩

#print axioms supportedRowFactor_extended
#print axioms residualRowFactor_extended
#print axioms rowBlock_extended

end
end HeckeSkeleton.LowFrozenCube.PrimeCoordinates
