import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Analysis.Complex.Basic

/-!
# The actual prime-ideal mask, independently of the Hecke project

The mask tested here is exactly the arithmetic expression appearing in the
supplied `originalMomentMask`: exclusion of S and primes containing 6, AND
coprimality with the row ideal.  Theorems in this file need only Mathlib.
-/

noncomputable section

namespace HeckeSkeleton.PrimeCancellationIdealMask

open IsDedekindDomain
open scoped Classical

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def originalMask (S : Set (HeightOneSpectrum R)) (u I : Ideal R) : Bool :=
  if (∀ p : HeightOneSpectrum R, p.asIdeal ∣ I →
    p ∉ S ∧ (6 : R) ∉ p.asIdeal) ∧ IsCoprime I u then true else false

def fixedMask (S : Set (HeightOneSpectrum R)) (I : Ideal R) : Bool :=
  if ∀ p : HeightOneSpectrum R, p.asIdeal ∣ I →
    p ∉ S ∧ (6 : R) ∉ p.asIdeal then true else false

theorem prime_eq_of_asIdeal_dvd {p q : HeightOneSpectrum R}
    (h : q.asIdeal ∣ p.asIdeal) : q = p := by
  apply HeightOneSpectrum.asIdeal_injective
  exact (p.isMaximal.eq_of_le q.isPrime.ne_top (Ideal.dvd_iff_le.mp h)).symm

theorem prime_divisor_condition_iff (S : Set (HeightOneSpectrum R))
    (p : HeightOneSpectrum R) :
    (∀ q : HeightOneSpectrum R, q.asIdeal ∣ p.asIdeal →
      q ∉ S ∧ (6 : R) ∉ q.asIdeal) ↔ p ∉ S ∧ (6 : R) ∉ p.asIdeal := by
  constructor
  · intro h
    exact h p dvd_rfl
  · intro h q hqp
    have heq : q = p := prime_eq_of_asIdeal_dvd hqp
    simpa only [heq] using h

theorem prime_isCoprime_iff_not_dvd (p : HeightOneSpectrum R) (I : Ideal R) :
    IsCoprime p.asIdeal I ↔ ¬p.asIdeal ∣ I := by
  rw [Ideal.isCoprime_iff_sup_eq]
  constructor
  · intro hcop hdvd
    have hsup : p.asIdeal ⊔ I = p.asIdeal := sup_eq_left.mpr (Ideal.dvd_iff_le.mp hdvd)
    exact p.isPrime.ne_top (hsup.symm.trans hcop)
  · intro hnot
    by_contra hsup
    have heq : p.asIdeal = p.asIdeal ⊔ I := p.isMaximal.eq_of_le hsup le_sup_left
    apply hnot
    apply Ideal.dvd_iff_le.mpr
    exact le_sup_right.trans heq.ge

theorem originalMask_prime (S : Set (HeightOneSpectrum R)) (u : Ideal R)
    (p : HeightOneSpectrum R) :
    originalMask S u p.asIdeal =
      if p ∉ S ∧ (6 : R) ∉ p.asIdeal ∧ ¬p.asIdeal ∣ u then true else false := by
  simp only [originalMask, prime_divisor_condition_iff,
    prime_isCoprime_iff_not_dvd, and_assoc]

theorem deleted_prime_cases (S : Set (HeightOneSpectrum R)) (u : Ideal R)
    (p : HeightOneSpectrum R) (hdeleted : originalMask S u p.asIdeal = false) :
    p ∈ S ∨ (6 : R) ∈ p.asIdeal ∨ p.asIdeal ∣ u := by
  by_cases hS : p ∈ S
  · exact Or.inl hS
  by_cases hsix : (6 : R) ∈ p.asIdeal
  · exact Or.inr (Or.inl hsix)
  by_cases hu : p.asIdeal ∣ u
  · exact Or.inr (Or.inr hu)
  have hkept : originalMask S u p.asIdeal = true := by
    rw [originalMask_prime]
    simp only [hS, hsix, hu, not_false_eq_true, and_self, ite_true]
  have hbad : (false : Bool) = true := hdeleted.symm.trans hkept
  cases hbad

theorem deleted_prime_dvd_fixed_mul_row
    (S : Set (HeightOneSpectrum R)) (D u : Ideal R)
    (hS : ∀ p : HeightOneSpectrum R, p ∈ S → p.asIdeal ∣ D)
    (hsix : ∀ p : HeightOneSpectrum R, (6 : R) ∈ p.asIdeal → p.asIdeal ∣ D)
    (p : HeightOneSpectrum R) (hdeleted : originalMask S u p.asIdeal = false) :
    p.asIdeal ∣ D * u := by
  rcases deleted_prime_cases S u p hdeleted with hpS | hp6 | hpu
  · exact dvd_mul_of_dvd_left (hS p hpS) u
  · exact dvd_mul_of_dvd_left (hsix p hp6) u
  · exact dvd_mul_of_dvd_right hpu D

omit [IsDedekindDomain R] in
theorem coefficient_mul_originalMask_eq_fixedMask
    (S : Set (HeightOneSpectrum R)) (u I : Ideal R) (a : ℂ)
    (hzero : ¬IsCoprime I u → a = 0) :
    a * (if originalMask S u I then 1 else 0) =
      a * (if fixedMask S I then 1 else 0) := by
  by_cases hcop : IsCoprime I u
  · by_cases hgood : ∀ p : HeightOneSpectrum R, p.asIdeal ∣ I →
        p ∉ S ∧ (6 : R) ∉ p.asIdeal
    · simp [originalMask, fixedMask, hcop]
    · simp [originalMask, fixedMask, hcop, hgood]
  · rw [hzero hcop]
    simp

#print axioms prime_eq_of_asIdeal_dvd
#print axioms prime_divisor_condition_iff
#print axioms prime_isCoprime_iff_not_dvd
#print axioms originalMask_prime
#print axioms deleted_prime_cases
#print axioms deleted_prime_dvd_fixed_mul_row
#print axioms coefficient_mul_originalMask_eq_fixedMask

end HeckeSkeleton.PrimeCancellationIdealMask
