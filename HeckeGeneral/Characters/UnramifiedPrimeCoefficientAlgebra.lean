import HeckeGeneral.Characters.PrimeCoefficients
import Mathlib.Algebra.Field.GeomSum

/-!
Arithmetic of the actual local Euler coefficients when one factor is
unramified. All statements use the existing localComponent and its literal
ramified zero extension. Multiplication is only asserted when one factor
is unramified: two ramified characters can have an unramified product.

The cyclic average is over an actual finite-order character unramified at
the place. Its background character may be ramified. No new arithmetic
input structure or source-calibration predicate is introduced.

-/

noncomputable section
namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]

/-- Every natural power of an unramified actual local component is
unramified, including the zeroth power. -/
theorem UnramifiedAt.pow {χ : HeckeCharacter K} {p : HeightOneSpectrum (𝓞 K)}
    (hχ : UnramifiedAt K χ p) (n : ℕ) : UnramifiedAt K (χ ^ n) p := by
  induction n with
  | zero => simpa only [pow_zero] using unramifiedAt_one K p
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul K hχ

/-- Multiplication by an unramified character cannot create or cancel
ramification of the other factor. -/
theorem unramifiedAt_mul_iff (χ ψ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hψ : UnramifiedAt K ψ p) :
    UnramifiedAt K (χ * ψ) p ↔ UnramifiedAt K χ p := by
  constructor
  · intro h u hu
    have hh := h u hu
    change localComponent K p χ u * localComponent K p ψ u = 1 at hh
    rw [hψ u hu, mul_one] at hh
    exact hh
  · intro hχ
    exact hχ.mul K hψ

/-- This includes a possibly ramified left factor, with its genuine zero
Euler coefficient. Only the right factor is assumed unramified. -/
theorem primeCoefficient_mul_right_unramified (χ ψ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hψ : UnramifiedAt K ψ p) :
    primeCoefficient K (χ * ψ) p = primeCoefficient K χ p * primeCoefficient K ψ p := by
  by_cases hχ : UnramifiedAt K χ p
  · rw [primeCoefficient_of_unramified K (χ * ψ) p (hχ.mul K hψ),
      primeCoefficient_of_unramified K χ p hχ,
      primeCoefficient_of_unramified K ψ p hψ]
    rfl
  · have hprod : ¬UnramifiedAt K (χ * ψ) p :=
      fun h => hχ ((unramifiedAt_mul_iff K χ ψ p hψ).mp h)
    rw [primeCoefficient_of_ramified K (χ * ψ) p hprod,
      primeCoefficient_of_ramified K χ p hχ, zero_mul]

@[simp] theorem primeCoefficient_one (p : HeightOneSpectrum (𝓞 K)) :
    primeCoefficient K 1 p = 1 := by
  rw [primeCoefficient_of_unramified K 1 p (unramifiedAt_one K p)]
  rfl

/-- The unramified hypothesis is retained even for powers: a power of a
ramified character could become unramified and hence have a nonzero value. -/
theorem primeCoefficient_pow_of_unramified (χ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hχ : UnramifiedAt K χ p) (n : ℕ) :
    primeCoefficient K (χ ^ n) p = (primeCoefficient K χ p) ^ n := by
  induction n with
  | zero => simp only [pow_zero, primeCoefficient_one]
  | succ n ih =>
    calc
      primeCoefficient K (χ ^ (n + 1)) p =
          primeCoefficient K (χ ^ n * χ) p := by rw [pow_succ]
      _ = primeCoefficient K (χ ^ n) p * primeCoefficient K χ p :=
        primeCoefficient_mul_right_unramified K (χ ^ n) χ p hχ
      _ = (primeCoefficient K χ p) ^ n * primeCoefficient K χ p := by rw [ih]
      _ = (primeCoefficient K χ p) ^ (n + 1) := (pow_succ _ n).symm

theorem primeCoefficient_pow_eq_one_of_unramified
    (χ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (hχ : UnramifiedAt K χ p) {n : ℕ} (hχn : χ ^ n = 1) :
    (primeCoefficient K χ p) ^ n = 1 := by
  rw [← primeCoefficient_pow_of_unramified K χ p hχ n, hχn,
    primeCoefficient_one]

/-- An exact finite sum identity before division by the cyclic order.
The background psi may be ramified; each chi^j is unramified. -/
theorem sum_primeCoefficient_mul_powers_of_unramified
    (ψ χ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (hχ : UnramifiedAt K χ p) (n : ℕ) :
    (∑ j ∈ Finset.range n, primeCoefficient K (ψ * χ ^ j) p) =
      primeCoefficient K ψ p * ∑ j ∈ Finset.range n, (primeCoefficient K χ p) ^ j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [primeCoefficient_mul_right_unramified K ψ (χ ^ j) p (hχ.pow K j),
    primeCoefficient_pow_of_unramified K χ p hχ j]

/-- Cyclic character averaging gives the literal identity-ray indicator
at an unramified place. No assumption is made on the background psi's
ramification, and n need not be the exact order of chi. -/
theorem primeCoefficient_cyclic_average_of_unramified
    (ψ χ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (hχ : UnramifiedAt K χ p) {n : ℕ} (hn : 0 < n) (hχn : χ ^ n = 1) :
    (∑ j ∈ Finset.range n, primeCoefficient K (ψ * χ ^ j) p) / (n : ℂ) =
      primeCoefficient K ψ p * (if primeCoefficient K χ p = 1 then 1 else 0) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hz : (primeCoefficient K χ p) ^ n = 1 :=
    primeCoefficient_pow_eq_one_of_unramified K χ p hχ hχn
  rw [sum_primeCoefficient_mul_powers_of_unramified K ψ χ p hχ n]
  by_cases hq : primeCoefficient K χ p = 1
  · have hgeom : (∑ j ∈ Finset.range n, (primeCoefficient K χ p) ^ j) = (n : ℂ) := by
      simp [hq]
    rw [hgeom, mul_div_cancel_right₀ _ hnC, if_pos hq, mul_one]
  · have hgeom : (∑ j ∈ Finset.range n, (primeCoefficient K χ p) ^ j) = 0 := by
      rw [geom_sum_eq hq n, hz, sub_self, zero_div]
    rw [hgeom, mul_zero, zero_div, if_neg hq, mul_zero]

end HeckeGeneral.Characters
