import HeckeSkeleton.LowHybrid.PrimeArithmetic
import HeckeSkeleton.LowHybrid.DivisorEnvelope
import HeckeSkeleton.LowFrozenCube.PrimeProducts

/-!
# Divisor loss from actual prime coordinates

The squarefree divisors used in the Mobius expansion are precisely images of
subsets of the actual prime support. Their cardinality is therefore an exact
power of two. Multiplicativity of the norm and finite norm cutoffs supply the
arithmetic hypotheses of the small-prime argument.
-/

namespace HeckeSkeleton.LowHybrid.PrimeArithmetic

open scoped BigOperators Classical
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates

noncomputable section

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

/-- Every subset of prime support gives a distinct squarefree divisor. -/
theorem card_divisors (a : A) :
    (divisors coords a).card = 2 ^ (support coords a).card := by
  unfold divisors
  rw [Finset.card_image_of_injective _ (fromSupport_injective coords),
    Finset.card_powerset]

theorem card_divisors_real (a : A) :
    ((divisors coords a).card : ℝ) = (2 : ℝ) ^ (support coords a).card := by
  rw [card_divisors]
  simp

/-- Positive integral-type norms are monotone under divisibility. -/
theorem norm_le_of_dvd (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a)
    {a b : A} (hab : a ∣ b) : normI a ≤ normI b := by
  obtain ⟨c, rfl⟩ := hab
  rw [map_mul]
  exact le_mul_of_one_le_right (le_trans zero_le_one (hn a)) (hn c)

/-- The product of the distinct prime factors divides the original element. -/
theorem norm_fromSupport_le (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a)
    (a : A) : normI (fromSupport coords (support coords a)) ≤ normI a := by
  apply norm_le_of_dvd normI hn
  exact (fromSupport_dvd_iff coords _ a).mpr (Finset.Subset.refl _)

theorem singleton_fromSupport_injective :
    Function.Injective (fun p : ι => fromSupport coords {p}) := by
  intro p q h
  exact Finset.singleton_injective (fromSupport_injective coords h)

/-- Finite ideal norm cutoffs already imply finite prime norm cutoffs. -/
theorem finite_singleton_prime_norms
    (normI : A → ℝ) (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X})
    (X : ℝ) : Set.Finite {p : ι | normI (fromSupport coords {p}) ≤ X} := by
  exact (hfinite X).preimage (singleton_fromSupport_injective coords).injOn

/-- Complete finite norm cutoffs give the finiteness needed by the prime
argument, without a separately assumed prime-counting theorem. -/
theorem finite_norms_of_cutoffs
    (normI : A → ℝ) (cutoff : ℝ → Finset A)
    (hcomplete : ∀ X : ℝ, ∀ a : A, normI a ≤ X → a ∈ cutoff X)
    (X : ℝ) : Set.Finite {a : A | normI a ≤ X} :=
  (cutoff X).finite_toSet.subset (fun a ha => hcomplete X a ha)

/-- Each prime occurring in the support has positive integral exponent.
Its first norm power is therefore bounded by its full norm contribution. -/
theorem prime_product_le_norm
    (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a) (a : A) :
    (∏ p ∈ support coords a, normI (primeElement coords p)) ≤ normI a := by
  rw [norm_eq_prod coords normI a]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact le_trans zero_le_one (hn _)
  · intro p hp
    have hv : valuation coords a p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hv1 : 1 ≤ valuation coords a p := by omega
    calc
      normI (primeElement coords p) = normI (primeElement coords p) ^ 1 := by simp
      _ ≤ _ := pow_le_pow_right₀ (hn _) hv1

/-- The canonical prime elements embed in the ambient ideal monoid, so
their bounded norm sets are finite as soon as ideal norm sets are finite. -/
theorem finite_prime_norms
    (normI : A → ℝ) (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X})
    (X : ℝ) : Set.Finite {p : ι | normI (primeElement coords p) ≤ X} := by
  exact (hfinite X).preimage (primeElement_injective coords).injOn

/-- Uniform small-power bounds for the actual squarefree divisors used in
the Mobius formula. The constant is chosen before the element itself. -/
theorem divisor_count_subpower
    (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X})
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A,
      ((divisors coords a).card : ℝ) ≤ C * normI a ^ eta := by
  exact squarefree_divisor_count_subpower (support coords) (divisors coords)
    (fun p => normI (primeElement coords p)) normI
    (fun p => hn _) (finite_prime_norms coords normI hfinite)
    (fun a => le_of_eq (card_divisors_real coords a))
    (prime_product_le_norm coords normI hn) eta heta

/-- A complete finite norm cutoff may be used in place of a finiteness
predicate; no separate divisor or prime asymptotic is an input. -/
theorem divisor_count_subpower_of_cutoffs
    (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a) (cutoff : ℝ → Finset A)
    (hcomplete : ∀ X : ℝ, ∀ a : A, normI a ≤ X → a ∈ cutoff X)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A,
      ((divisors coords a).card : ℝ) ≤ C * normI a ^ eta := by
  exact divisor_count_subpower coords normI hn
    (finite_norms_of_cutoffs normI cutoff hcomplete) eta heta

/-- Every finite norm cutoff of actual divisors inherits the uniform
small-power bound from the prime-coordinate argument. -/
theorem divisor_envelope_subpower
    (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X})
    (cutoff : ℝ → Finset A)
    (hcutoff : ∀ X : ℝ, 1 ≤ X → ∀ a ∈ cutoff X, normI a ≤ X) :
    SubpowerBound (divisorCountEnvelope cutoff (divisors coords)) := by
  exact divisorCountEnvelope_subpower cutoff (divisors coords) normI
    (fun a => le_trans zero_le_one (hn a)) hcutoff
    (divisor_count_subpower coords normI hn hfinite)

/-- The actual finite set of all elements in a norm cutoff. -/
def normCutoff (normI : A → ℝ)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X}) (X : ℝ) : Finset A :=
  (hfinite X).toFinset

@[simp] theorem mem_normCutoff (normI : A → ℝ)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X}) (X : ℝ) (a : A) :
    a ∈ normCutoff normI hfinite X ↔ normI a ≤ X := by
  exact (hfinite X).mem_toFinset

/-- The divisor loss Delta(X), defined as the actual maximum divisor count
over all elements of norm at most X. -/
def actualDivisorEnvelope (normI : A → ℝ)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X}) : ℝ → ℝ :=
  divisorCountEnvelope (normCutoff normI hfinite) (divisors coords)

theorem actualDivisorEnvelope_nonneg (normI : A → ℝ)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X}) (X : ℝ) :
    0 ≤ actualDivisorEnvelope coords normI hfinite X :=
  divisorCountEnvelope_nonneg _ _ X

theorem divisor_count_le_actual_envelope (normI : A → ℝ)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X})
    (X : ℝ) (a : A) (ha : normI a ≤ X) :
    ((divisors coords a).card : ℝ) ≤ actualDivisorEnvelope coords normI hfinite X := by
  exact divisor_count_le_envelope (normCutoff normI hfinite) (divisors coords)
    X a ((mem_normCutoff normI hfinite X a).mpr ha)

/-- The actual Delta has the exact constant-before-scale quantifiers
required by the final arbitrary-epsilon loss absorption. -/
theorem actualDivisorEnvelope_subpower
    (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X}) :
    SubpowerBound (actualDivisorEnvelope coords normI hfinite) := by
  apply divisor_envelope_subpower coords normI hn hfinite (normCutoff normI hfinite)
  intro X hX a ha
  exact (mem_normCutoff normI hfinite X a).mp ha

#print axioms card_divisors
#print axioms norm_fromSupport_le
#print axioms finite_singleton_prime_norms
#print axioms prime_product_le_norm
#print axioms divisor_count_subpower
#print axioms divisor_envelope_subpower
#print axioms actualDivisorEnvelope_subpower

end
end HeckeSkeleton.LowHybrid.PrimeArithmetic
