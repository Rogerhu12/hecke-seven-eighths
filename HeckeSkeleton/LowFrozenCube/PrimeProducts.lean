import HeckeSkeleton.LowFrozenCube.PrimeCoordinates

/-!
# Prime products and multiplicative norms from canonical coordinates

The finite product formula is derived from the prime-coordinate equivalence.
It applies to every finite support containing the element's valuations and
does not require any chosen enumeration of the prime type.
-/

namespace HeckeSkeleton.LowFrozenCube.PrimeCoordinates

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

def primeElement (p : ι) : A :=
  coords.symm (Multiplicative.ofAdd (Finsupp.single p 1))

@[simp] theorem valuation_primeElement (p : ι) :
    valuation coords (primeElement coords p) = Finsupp.single p 1 := by
  simp [valuation, primeElement]

theorem primeElement_injective : Function.Injective (primeElement coords) := by
  intro p q hpq
  by_contra hne
  have h := congrArg (fun a => valuation coords a p) hpq
  simpa [Finsupp.single_apply, hne, Ne.symm hne] using h

theorem valuation_prod_apply {κ : Type*} (s : Finset κ) (f : κ → A) (p : ι) :
    valuation coords (∏ i ∈ s, f i) p = ∑ i ∈ s, valuation coords (f i) p := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi, valuation_mul_apply, ih]

theorem supported_support (a : A) :
    Supported coords (valuation coords a).support a := by
  intro p hp
  by_contra h
  exact hp (Finsupp.mem_support_iff.mpr h)

/-- The unique-prime coordinates reconstruct the actual monoid element. -/
theorem factorization (s : Finset ι) (a : A) (ha : Supported coords s a) :
    a = ∏ p ∈ s, primeElement coords p ^ valuation coords a p := by
  apply valuation_injective coords
  ext p
  rw [valuation_prod_apply, Finset.sum_eq_single p]
  · simp
  · intro q hq hqp
    simp [Finsupp.single_apply, hqp]
  · intro hp
    simp [ha p hp]

theorem norm_factorization (s : Finset ι) (a : A)
    (ha : Supported coords s a) (normI : A →* ℝ) :
    normI a = ∏ p ∈ s, normI (primeElement coords p) ^ valuation coords a p := by
  calc
    normI a = normI (∏ p ∈ s, primeElement coords p ^ valuation coords a p) :=
      congrArg normI (factorization coords s a ha)
    _ = _ := by simp only [map_prod, map_pow]

/-- The exact norm formula on the element's own finite prime support. -/
theorem norm_eq_prod (normI : A →* ℝ) (a : A) :
    normI a = ∏ p ∈ (valuation coords a).support,
      normI (primeElement coords p) ^ valuation coords a p :=
  norm_factorization coords (valuation coords a).support a
    (supported_support coords a) normI

end

end HeckeSkeleton.LowFrozenCube.PrimeCoordinates
