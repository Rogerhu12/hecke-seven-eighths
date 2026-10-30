import HeckePort.CenteredMoment.IdealMobius

/-!
# The redundant primes of a natural primitive character

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/NaturalPrimitive.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

The ideal-theoretic part (`redundantSet`, `redundantIdeal` and their coprimality, divisibility and
norm properties, `coprime_original_iff`) is a direct port.  In openai the character data is the
`HeckeFamily.Character` structure (modulus, residue character, `idealCoeff`,
`Character.excludePrimes`).  That structure, and `exists_primitive_character` built on
`IdealCharacter.exists_primitive_associate`, do not belong to S0, so the character theorems are
stated for abstract coefficient functions on ideals:

* `idealCoeff_natural_deletion` is openai's `idealCoeff_natural_deletion`, with `idealCoeff χ`,
  `idealCoeff ψ` replaced by functions `a b : Ideal (𝓞 K) → ℂ` and the facts it used
  (`hmask`, `idealCoeff_source_mask ψ`, `idealCoeff_excludePrimes`) written out;
  `a I = if IsCoprime I M then b I else 0`, `b I = 0` unless `I` is prime to `C`.
* `polynomial_natural_deletion` (a `tsum_congr` through `HeckeDyadic.polynomial`) and
  `exists_natural_primitive` (needs `exists_primitive_character`) are not ported.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open HeckePort.IdealMobiusDivisorSum UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

def redundantSet (M C : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) := primeSupport M \ primeSupport C

def redundantIdeal (M C : Ideal (𝓞 K)) : Ideal (𝓞 K) := ∏ P ∈ redundantSet M C, P

lemma redundantSet_prime (M C : Ideal (𝓞 K)) : ∀ P ∈ redundantSet M C, Prime P :=
  fun _ h => support_prime (Finset.mem_sdiff.mp h).1

lemma redundantSet_subset (M C : Ideal (𝓞 K)) : redundantSet M C ⊆ primeSupport M :=
  Finset.sdiff_subset

lemma prime_mem_support_iff (M P : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hP : Prime P) :
    P ∈ primeSupport M ↔ P ∣ M := by
  simp only [primeSupport, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hM]
  exact ⟨fun h => Ideal.dvd_iff_le.mpr h.2, fun h => ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp h⟩⟩

lemma mem_redundantSet (M C P : Ideal (𝓞 K)) (hC : C ≠ ⊥) :
    P ∈ redundantSet M C ↔ P ∈ primeSupport M ∧ ¬P ∣ C := by
  constructor
  · intro h
    obtain ⟨hp, hc⟩ := Finset.mem_sdiff.mp h
    exact ⟨hp, fun hd => hc ((prime_mem_support_iff C P hC (support_prime hp)).mpr hd)⟩
  · rintro ⟨hp, hc⟩
    exact Finset.mem_sdiff.mpr
      ⟨hp, fun h => hc ((prime_mem_support_iff C P hC (support_prime hp)).mp h)⟩

lemma redundantIdeal_squarefree (M C : Ideal (𝓞 K)) : Squarefree (redundantIdeal M C) :=
  squarefree_support_product (redundantSet_subset M C)

lemma redundantIdeal_ne_zero (M C : Ideal (𝓞 K)) : redundantIdeal M C ≠ ⊥ :=
  support_product_ne_zero (redundantSet_subset M C)

lemma redundantIdeal_support (M C : Ideal (𝓞 K)) :
    primeSupport (redundantIdeal M C) = redundantSet M C := by
  unfold primeSupport redundantIdeal
  rw [factors_support_product (redundantSet_subset M C)]
  exact Finset.val_toFinset _

/-- openai `IdealCoprimeSieveOperator.primeSupport_disjoint_iff`. -/
theorem primeSupport_disjoint_iff {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    Disjoint (primeSupport I) (primeSupport J) ↔ IsCoprime I J := by
  constructor
  · intro h
    have hr : IsRelPrime I J := (isRelPrime_iff_no_prime_factors hI).mpr (by
      intro P hPI hPJ hP
      apply Finset.disjoint_left.mp h
      · apply Multiset.mem_toFinset.mpr
        exact (Ideal.mem_normalizedFactors_iff hI).mpr
          ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp hPI⟩
      · apply Multiset.mem_toFinset.mpr
        exact (Ideal.mem_normalizedFactors_iff hJ).mpr
          ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp hPJ⟩)
    apply Ideal.isCoprime_iff_gcd.mpr
    exact associated_iff_eq.mp (associated_one_iff_isUnit.mpr (gcd_isUnit_iff_isRelPrime.mpr hr))
  · intro h
    exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors h.isRelPrime)

lemma redundantIdeal_coprime (M C : Ideal (𝓞 K)) (hC : C ≠ ⊥) :
    IsCoprime (redundantIdeal M C) C := by
  apply (primeSupport_disjoint_iff (redundantIdeal_ne_zero M C) hC).mp
  rw [redundantIdeal_support]
  exact Finset.disjoint_left.mpr (fun P hp hc => (Finset.mem_sdiff.mp hp).2 hc)

lemma primitive_redundant_dvd (M C : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hC : C ≠ ⊥) (hCM : C ∣ M) :
    C * redundantIdeal M C ∣ M := by
  exact (redundantIdeal_coprime M C hC).symm.mul_dvd hCM
    (support_product_dvd hM (redundantSet_subset M C))

lemma primitive_redundant_norm (M C : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hC : C ≠ ⊥) (hCM : C ∣ M) :
    C.absNorm * (redundantIdeal M C).absNorm ≤ M.absNorm := by
  have h := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hM))
    (map_dvd Ideal.absNorm (primitive_redundant_dvd M C hM hC hCM))
  simpa only [map_mul] using h

lemma coprime_support_iff (I M : Ideal (𝓞 K)) (hM : M ≠ ⊥) :
    IsCoprime I M ↔ ∀ P ∈ primeSupport M, IsCoprime I P := by
  have hprod (s : Multiset (Ideal (𝓞 K))) : IsCoprime I s.prod ↔ ∀ P ∈ s, IsCoprime I P := by
    induction s using Multiset.induction_on with
    | empty => simpa using (isCoprime_one_right : IsCoprime I (1 : Ideal (𝓞 K)))
    | cons a s ih => simp only [Multiset.prod_cons, IsCoprime.mul_right_iff, Multiset.mem_cons,
        forall_eq_or_imp, ih]
  calc
    _ ↔ IsCoprime I (normalizedFactors M).prod := by rw [Ideal.prod_normalizedFactors_eq_self hM]
    _ ↔ _ := by simpa only [primeSupport, Multiset.mem_toFinset] using hprod (normalizedFactors M)

lemma coprime_original_iff (I M C : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hC : C ≠ ⊥) (hCM : C ∣ M) :
    IsCoprime I M ↔ IsCoprime I C ∧ ∀ P ∈ redundantSet M C, IsCoprime I P := by
  constructor
  · intro h
    refine ⟨h.of_isCoprime_of_dvd_right hCM, ?_⟩
    intro P hP
    exact (coprime_support_iff I M hM).mp h P ((redundantSet_subset M C) hP)
  · rintro ⟨hIC, hIR⟩
    apply (coprime_support_iff I M hM).mpr
    intro P hP
    by_cases hPC : P ∈ primeSupport C
    · exact (coprime_support_iff I C hC).mp hIC P hPC
    · exact hIR P (Finset.mem_sdiff.mpr ⟨hP, hPC⟩)

/-- openai `idealCoeff_natural_deletion`, for abstract coefficient functions.  Here `a` plays
`idealCoeff χ` (modulus `M`), `b` plays `idealCoeff ψ` (modulus `C ∣ M`); the conclusion says
`a` equals `b` with the redundant primes excluded. -/
theorem idealCoeff_natural_deletion (M C : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hC : C ≠ ⊥)
    (hCM : C ∣ M) (a b : Ideal (𝓞 K) → ℂ)
    (hmask : ∀ I, a I = if IsCoprime I M then b I else 0)
    (hsrc : ∀ I, b I = if IsCoprime I C then b I else 0) (I : Ideal (𝓞 K)) :
    a I = if ∀ P ∈ redundantSet M C, IsCoprime I P then b I else 0 := by
  rw [hmask I]
  have hm := coprime_original_iff I M C hM hC hCM
  by_cases hI : IsCoprime I C
  · by_cases hR : ∀ P ∈ redundantSet M C, IsCoprime I P
    · have : IsCoprime I M := hm.mpr ⟨hI, hR⟩
      exact (ite_eq_left_iff.mpr (fun h => absurd this h)).trans
        (ite_eq_left_iff.mpr (fun h => absurd hR h)).symm
    · have : ¬ IsCoprime I M := fun h => hR (hm.mp h).2
      exact (ite_eq_right_iff.mpr (fun h => absurd h this)).trans
        (ite_eq_right_iff.mpr (fun h => absurd h hR)).symm
  · have hz : b I = 0 := by simpa only [hI, ite_false] using hsrc I
    simp only [hz, ite_self]

end HeckePort.Moments

end
