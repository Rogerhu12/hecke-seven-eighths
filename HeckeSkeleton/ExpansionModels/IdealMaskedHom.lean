import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The complete ideal mask is compatible with multiplication

This Mathlib-only module uses actual ideals and height-one primes.  It
retains all fixed exceptional primes, primes above a chosen element q, and
every prime dividing the complete moving row ideal u.  The construction
never asks those primes to ramify in a character.
-/

set_option autoImplicit false
noncomputable section

namespace ExpansionRecipe.IdealMask

open IsDedekindDomain
open scoped Classical

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The same fixed-prime/element/coprimality predicate as the source mask. -/
def Allowed (S : Set (HeightOneSpectrum R)) (q : R) (u I : Ideal R) : Prop :=
  (∀ p : HeightOneSpectrum R, p.asIdeal ∣ I → p ∉ S ∧ q ∉ p.asIdeal) ∧ IsCoprime I u

lemma allowed_one (S : Set (HeightOneSpectrum R)) (q : R) (u : Ideal R) :
    Allowed S q u 1 := by
  constructor
  · intro p hp
    exact (p.prime.not_isUnit (isUnit_of_dvd_one hp)).elim
  · exact isCoprime_one_left

lemma allowed_mul_iff (S : Set (HeightOneSpectrum R)) (q : R) (u I J : Ideal R) :
    Allowed S q u (I * J) ↔ Allowed S q u I ∧ Allowed S q u J := by
  constructor
  · intro h
    exact ⟨⟨fun p hp => h.1 p (dvd_mul_of_dvd_left hp J),
      (IsCoprime.mul_left_iff.mp h.2).1⟩,
      ⟨fun p hp => h.1 p (dvd_mul_of_dvd_right hp I),
      (IsCoprime.mul_left_iff.mp h.2).2⟩⟩
  · rintro ⟨hI, hJ⟩
    refine ⟨?_, hI.2.mul_left hJ.2⟩
    intro p hp
    rcases p.prime.dvd_mul.mp hp with h | h
    · exact hI.1 p h
    · exact hJ.1 p h

/-- Mask an actual multiplicative ideal coefficient without altering any
nonzero coefficient or any original zero. -/
def maskedHom (S : Set (HeightOneSpectrum R)) (q : R) (u : Ideal R)
    (w : Ideal R →*₀ ℂ) : Ideal R →*₀ ℂ where
  toFun I := if Allowed S q u I then w I else 0
  map_zero' := by
    split_ifs
    · exact map_zero w
    · rfl
  map_one' := by rw [ite_eq_left (allowed_one S q u), map_one]
  map_mul' I J := by
    by_cases hI : Allowed S q u I <;> by_cases hJ : Allowed S q u J <;>
      simp [allowed_mul_iff, hI, hJ, map_mul]

theorem maskedHom_eq (S : Set (HeightOneSpectrum R)) (q : R) (u : Ideal R)
    (w : Ideal R →*₀ ℂ) (I : Ideal R) :
    maskedHom S q u w I = w I * (if decide (Allowed S q u I) then (1 : ℂ) else 0) := by
  by_cases h : Allowed S q u I <;> simp [maskedHom, h]

theorem maskedHom_norm_le (S : Set (HeightOneSpectrum R)) (q : R) (u : Ideal R)
    (w : Ideal R →*₀ ℂ) (I : Ideal R) (hw : ‖w I‖ ≤ 1) :
    ‖maskedHom S q u w I‖ ≤ 1 := by
  by_cases h : Allowed S q u I <;> simp [maskedHom, h, hw]

/-- The whole complete-row coprimality mask survives arbitrary sixth powers
of a column ideal: a bad prime never becomes good through exponentiation. -/
theorem allowed_pow_iff (S : Set (HeightOneSpectrum R)) (q : R) (u I : Ideal R)
    (n : ℕ) (hn : 0 < n) :
    Allowed S q u (I ^ n) ↔ Allowed S q u I := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, allowed_mul_iff, ih (Nat.succ_pos k)]
    simp

theorem maskedHom_pow (S : Set (HeightOneSpectrum R)) (q : R) (u I : Ideal R)
    (w : Ideal R →*₀ ℂ) (n : ℕ) :
    maskedHom S q u w (I ^ n) = (maskedHom S q u w I) ^ n :=
  map_pow (maskedHom S q u w) I n

end ExpansionRecipe.IdealMask

#print axioms ExpansionRecipe.IdealMask.allowed_mul_iff
#print axioms ExpansionRecipe.IdealMask.maskedHom
#print axioms ExpansionRecipe.IdealMask.allowed_pow_iff
