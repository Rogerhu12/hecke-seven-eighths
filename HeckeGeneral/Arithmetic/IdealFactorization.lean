import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# Nonzero integral ideals as finitely supported prime exponents

This construction uses unique factorization of ideals in a Dedekind domain,
not unique factorization of elements or a principal ideal assumption.
The inverse is the actual finite product of prime ideal powers.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open IsDedekindDomain UniqueFactorizationMonoid
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The multiplicity of each nonzero prime ideal in a nonzero integral ideal. -/
def primeExponents (I : (Ideal R)⁰) : HeightOneSpectrum R →₀ ℕ :=
  (factorization I.val).comapDomain HeightOneSpectrum.asIdeal
    HeightOneSpectrum.asIdeal_injective.injOn

@[simp] theorem primeExponents_apply (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    primeExponents I p = (normalizedFactors I.val).count p.asIdeal := rfl

private theorem factorization_support_range (I : Ideal R) :
    ↑(factorization I).support ⊆ Set.range (HeightOneSpectrum.asIdeal (R := R)) := by
  intro P hP
  have hmem : P ∈ normalizedFactors I := by
    simpa only [support_factorization, Finset.mem_coe, Multiset.mem_toFinset] using hP
  exact ⟨HeightOneSpectrum.ofPrime (prime_of_normalized_factor P hmem), rfl⟩

/-- The product of the prime powers indexed by an exponent vector. -/
def idealOfPrimeExponents (e : HeightOneSpectrum R →₀ ℕ) : (Ideal R)⁰ :=
  ⟨e.prod (fun p n => p.asIdeal ^ n), mem_nonZeroDivisors_of_ne_zero
    (Finsupp.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ p.ne_bot))⟩

@[simp] theorem idealOfPrimeExponents_val (e : HeightOneSpectrum R →₀ ℕ) :
    (idealOfPrimeExponents e).val = e.prod (fun p n => p.asIdeal ^ n) := rfl

@[simp] theorem idealOfPrimeExponents_zero :
    idealOfPrimeExponents (0 : HeightOneSpectrum R →₀ ℕ) = 1 := by
  apply Subtype.ext
  simp [idealOfPrimeExponents]

theorem idealOfPrimeExponents_add (e f : HeightOneSpectrum R →₀ ℕ) :
    idealOfPrimeExponents (e + f) = idealOfPrimeExponents e * idealOfPrimeExponents f := by
  apply Subtype.ext
  exact Finsupp.prod_add_index' (fun p => pow_zero p.asIdeal)
    (fun p n m => pow_add p.asIdeal n m)

@[simp] theorem idealOfPrimeExponents_single (p : HeightOneSpectrum R) (n : ℕ) :
    (idealOfPrimeExponents (Finsupp.single p n)).val = p.asIdeal ^ n := by
  exact Finsupp.prod_single_index (pow_zero p.asIdeal)

@[simp] theorem primeExponents_one : primeExponents (1 : (Ideal R)⁰) = 0 := by
  ext p
  change factorization (1 : Ideal R) p.asIdeal = 0
  rw [factorization_one]
  rfl

theorem primeExponents_mul (I J : (Ideal R)⁰) :
    primeExponents (I * J) = primeExponents I + primeExponents J := by
  ext p
  simp only [primeExponents, Finsupp.comapDomain_apply, Submonoid.coe_mul,
    factorization_mul (nonZeroDivisors.coe_ne_zero I) (nonZeroDivisors.coe_ne_zero J),
    Finsupp.add_apply]

/-- Reconstruction from the multiplicities of the actual prime ideal factors. -/
@[simp] theorem idealOfPrimeExponents_primeExponents (I : (Ideal R)⁰) :
    idealOfPrimeExponents (primeExponents I) = I := by
  apply Subtype.ext
  change (primeExponents I).prod (fun p n => p.asIdeal ^ n) = I.val
  rw [← Finsupp.prod_mapDomain_index_inj HeightOneSpectrum.asIdeal_injective]
  rw [primeExponents, Finsupp.mapDomain_comapDomain _ HeightOneSpectrum.asIdeal_injective
    _ (factorization_support_range I.val)]
  rw [← Finsupp.prod_toMultiset]
  simpa only [factorization, Multiset.toFinsupp_toMultiset] using
    Ideal.prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)

@[simp] theorem primeExponents_idealOfPrimeExponents_single
    (p : HeightOneSpectrum R) (n : ℕ) :
    primeExponents (idealOfPrimeExponents (Finsupp.single p n)) = Finsupp.single p n := by
  ext q
  simp only [primeExponents_apply, idealOfPrimeExponents_single,
    normalizedFactors_pow, normalizedFactors_irreducible p.irreducible, normalize_eq,
    Multiset.nsmul_singleton, Multiset.count_replicate]
  by_cases h : p = q
  · subst q
    simp
  · have hpq : p.asIdeal ≠ q.asIdeal := fun he => h
      (HeightOneSpectrum.asIdeal_injective he)
    simp [hpq, Ne.symm h]

/-- Every finite exponent vector is recovered exactly from its prime-power product. -/
@[simp] theorem primeExponents_idealOfPrimeExponents (e : HeightOneSpectrum R →₀ ℕ) :
    primeExponents (idealOfPrimeExponents e) = e := by
  induction e using Finsupp.induction with
  | zero => simp
  | @single_add p n e _ _ ih =>
    rw [idealOfPrimeExponents_add, primeExponents_mul, ih]
    simp

/-- The bijection used to reindex ideal sums by finite prime exponent vectors. -/
def primeExponentEquiv : (Ideal R)⁰ ≃ (HeightOneSpectrum R →₀ ℕ) where
  toFun := primeExponents
  invFun := idealOfPrimeExponents
  left_inv := idealOfPrimeExponents_primeExponents
  right_inv := primeExponents_idealOfPrimeExponents

@[simp] theorem primeExponentEquiv_apply (I : (Ideal R)⁰) :
    primeExponentEquiv I = primeExponents I := rfl

@[simp] theorem primeExponentEquiv_symm_apply (e : HeightOneSpectrum R →₀ ℕ) :
    primeExponentEquiv.symm e = idealOfPrimeExponents e := rfl

/-- Every multiplicative ideal weight is the finite product of its prime-power weights. -/
theorem map_idealOfPrimeExponents {M : Type*} [CommMonoid M]
    (f : Ideal R →* M) (e : HeightOneSpectrum R →₀ ℕ) :
    f (idealOfPrimeExponents e).val = e.prod (fun p n => f p.asIdeal ^ n) := by
  rw [idealOfPrimeExponents_val, map_finsuppProd]
  simp only [map_pow]

end HeckeGeneral.Arithmetic
