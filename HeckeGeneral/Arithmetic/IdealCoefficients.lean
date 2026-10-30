import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Multiplicative ideal coefficients from local prime values

The primes are the actual height-one spectrum of a Dedekind domain. The
unique factorization is that of integral ideals, without any PID hypothesis.
Arbitrary complex prime values extend to a multiplicative ideal coefficient.
The zero ideal is explicitly assigned zero; restriction to nonzero ideals
therefore gives the ideal-indexed coefficients used by Dirichlet series.

No assertion that arbitrary prime values are Hecke-character values is made.
The final norm-twist identity uses the actual absolute ideal norm over a
number field, not a separate norm supplied as an assumption.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical nonZeroDivisors

section DedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- A total extension used to evaluate the multiset of prime ideal factors.
The nonprime branch is never used by a nonzero ideal's factorization. -/
def primeIdealValue (a : HeightOneSpectrum R → ℂ) (P : Ideal R) : ℂ :=
  if h : Prime P then a (HeightOneSpectrum.ofPrime h) else 1

@[simp] theorem primeIdealValue_asIdeal (a : HeightOneSpectrum R → ℂ) (p : HeightOneSpectrum R) :
    primeIdealValue a p.asIdeal = a p := by
  simp [primeIdealValue, p.prime]

/-- The unique-factorization extension, with a zero extension at the zero ideal. -/
def idealCoefficient (a : HeightOneSpectrum R → ℂ) (I : Ideal R) : ℂ :=
  if I = ⊥ then 0 else ((normalizedFactors I).map (primeIdealValue a)).prod

@[simp] theorem idealCoefficient_zero (a : HeightOneSpectrum R → ℂ) :
    idealCoefficient a ⊥ = 0 := by simp [idealCoefficient]

@[simp] theorem idealCoefficient_one (a : HeightOneSpectrum R → ℂ) :
    idealCoefficient a 1 = 1 := by
  rw [idealCoefficient, ite_eq_right (show (1 : Ideal R) ≠ ⊥ from one_ne_zero),
    normalizedFactors_one]
  simp

theorem idealCoefficient_mul (a : HeightOneSpectrum R → ℂ) (I J : Ideal R) :
    idealCoefficient a (I * J) = idealCoefficient a I * idealCoefficient a J := by
  by_cases hI : I = ⊥
  · subst I
    simp
  by_cases hJ : J = ⊥
  · subst J
    simp
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  simp only [idealCoefficient, ite_eq_right hI, ite_eq_right hJ, ite_eq_right hIJ,
    normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

/-- A genuine monoid-with-zero homomorphism on actual integral ideals. -/
def idealCoefficientHom (a : HeightOneSpectrum R → ℂ) : Ideal R →*₀ ℂ where
  toFun := idealCoefficient a
  map_zero' := idealCoefficient_zero a
  map_one' := idealCoefficient_one a
  map_mul' := idealCoefficient_mul a

@[simp] theorem idealCoefficient_prime (a : HeightOneSpectrum R → ℂ) (p : HeightOneSpectrum R) :
    idealCoefficient a p.asIdeal = a p := by
  simp [idealCoefficient, p.ne_bot, normalizedFactors_irreducible p.irreducible, normalize_eq]

theorem idealCoefficient_prime_pow (a : HeightOneSpectrum R → ℂ)
    (p : HeightOneSpectrum R) (n : ℕ) :
    idealCoefficient a (p.asIdeal ^ n) = a p ^ n := by
  calc
    idealCoefficient a (p.asIdeal ^ n) = idealCoefficient a p.asIdeal ^ n :=
      (idealCoefficientHom a).map_pow p.asIdeal n
    _ = a p ^ n := by rw [idealCoefficient_prime]

private theorem multiset_prod_norm_le_one (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ ≤ 1) :
    ‖s.prod‖ ≤ 1 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons z s ih =>
    have hz := hs z (Multiset.mem_cons_self z s)
    have htail := ih (fun w hw => hs w (Multiset.mem_cons_of_mem hw))
    rw [Multiset.prod_cons, norm_mul]
    exact (mul_le_mul hz htail (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem norm_idealCoefficient_le_one (a : HeightOneSpectrum R → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (I : Ideal R) : ‖idealCoefficient a I‖ ≤ 1 := by
  have hvalue (P : Ideal R) : ‖primeIdealValue a P‖ ≤ 1 := by
    unfold primeIdealValue
    split_ifs with h
    · exact ha _
    · simp
  unfold idealCoefficient
  split_ifs with hI
  · simp
  apply multiset_prod_norm_le_one
  intro z hz
  obtain ⟨P, _, rfl⟩ := Multiset.mem_map.mp hz
  exact hvalue P

/-- The same coefficient function on precisely the nonzero integral ideals. -/
def nonzeroIdealCoefficient (a : HeightOneSpectrum R → ℂ) (I : (Ideal R)⁰) : ℂ :=
  idealCoefficient a I.val

theorem norm_nonzeroIdealCoefficient_le_one (a : HeightOneSpectrum R → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (I : (Ideal R)⁰) : ‖nonzeroIdealCoefficient a I‖ ≤ 1 :=
  norm_idealCoefficient_le_one a ha I.val

end DedekindDomain

section NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- A norm phase on ideals. Only its nonzero-ideal values are used in ideal series. -/
def idealNormPhase (t : ℝ) : Ideal (𝓞 K) →* ℂ where
  toFun I := (Ideal.absNorm I : ℂ) ^ ((t : ℂ) * Complex.I)
  map_one' := by simp
  map_mul' I J := by
    rw [map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

/-- Twist each local prime coefficient by its actual ideal norm raised to `it`. -/
def primeNormTwistedCoefficients (a : HeightOneSpectrum (𝓞 K) → ℂ) (t : ℝ)
    (p : HeightOneSpectrum (𝓞 K)) : ℂ := a p * idealNormPhase K t p.asIdeal

/-- Twisting prime values extends to the expected norm twist on every nonzero ideal.
The statement also holds for the explicitly zero-extended coefficient at the zero ideal. -/
theorem idealCoefficient_primeNormTwist (a : HeightOneSpectrum (𝓞 K) → ℂ) (t : ℝ)
    (I : Ideal (𝓞 K)) :
    idealCoefficient (primeNormTwistedCoefficients K a t) I =
      idealCoefficient a I * (Ideal.absNorm I : ℂ) ^ ((t : ℂ) * Complex.I) := by
  by_cases hI : I = ⊥
  · subst I
    simp
  have hmap :
      (normalizedFactors I).map (primeIdealValue (primeNormTwistedCoefficients K a t)) =
      (normalizedFactors I).map (fun P => primeIdealValue a P * idealNormPhase K t P) := by
    apply Multiset.map_congr rfl
    intro P hP
    have hp := prime_of_normalized_factor P hP
    simp [primeIdealValue, hp, primeNormTwistedCoefficients]
  simp only [idealCoefficient, ite_eq_right hI]
  rw [hmap, Multiset.prod_map_mul, ← map_multiset_prod (idealNormPhase K t),
    Ideal.prod_normalizedFactors_eq_self hI]
  rfl

theorem nonzeroIdealCoefficient_primeNormTwist (a : HeightOneSpectrum (𝓞 K) → ℂ) (t : ℝ)
    (I : (Ideal (𝓞 K))⁰) :
    nonzeroIdealCoefficient (primeNormTwistedCoefficients K a t) I =
      nonzeroIdealCoefficient a I * (Ideal.absNorm I.val : ℂ) ^ ((t : ℂ) * Complex.I) :=
  idealCoefficient_primeNormTwist K a t I.val

end NumberField

end HeckeGeneral.Arithmetic
