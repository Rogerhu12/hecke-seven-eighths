import HeckeGeneral.Characters.Unramified
import HeckeGeneral.Characters.LocalUniformizer

/-!
# Genuine local Euler coefficients of a unitary Hecke character

At an unramified place the coefficient is the actual local character evaluated
at a uniformizer. At a ramified place it is zero. The chosen uniformizer is
proved irrelevant, and a unitary norm twist changes the coefficient by q^(it).
No finite-conductor or analytic-continuation assertion is used here.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

/-- The actual Euler coefficient, with the standard zero extension at ramified places. -/
def primeCoefficient (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if UnramifiedAt K χ v then
    (localComponent K v χ (localUniformizerUnit K v) : ℂ) else 0

theorem primeCoefficient_of_unramified (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (hχ : UnramifiedAt K χ v) :
    primeCoefficient K χ v = (localComponent K v χ (localUniformizerUnit K v) : ℂ) :=
  ite_eq_left hχ

theorem primeCoefficient_of_ramified (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (hχ : ¬UnramifiedAt K χ v) :
    primeCoefficient K χ v = 0 := ite_eq_right hχ

theorem norm_primeCoefficient_le_one (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    ‖primeCoefficient K χ v‖ ≤ 1 := by
  unfold primeCoefficient
  split_ifs <;> simp

/-- Every local element with the uniformizer norm gives the same unramified coefficient. -/
theorem primeCoefficient_eq_of_norm (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (hχ : UnramifiedAt K χ v)
    (u : (v.adicCompletion K)ˣ) (hu : ‖u.val‖ = (residueCard K v : ℝ)⁻¹) :
    primeCoefficient K χ v = (localComponent K v χ u : ℂ) := by
  rw [primeCoefficient_of_unramified K χ v hχ]
  exact congrArg (fun z : Circle => (z : ℂ))
    (hχ.eq_of_norm_eq K (localUniformizerUnit K v) u
      ((localUniformizerUnit_norm K v).trans hu.symm))

theorem primeCoefficient_eq_of_isUniformizer (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (hχ : UnramifiedAt K χ v)
    (u : (v.adicCompletion K)ˣ)
    (hu : (Valued.v : Valuation (v.adicCompletion K)
      (WithZero (Multiplicative ℤ))).IsUniformizer u.val) :
    primeCoefficient K χ v = (localComponent K v χ u : ℂ) :=
  primeCoefficient_eq_of_norm K χ v hχ u
    (localNorm_eq_inv_residueCard_of_isUniformizer K v u.val hu)

theorem heckeNormTwist_uniformizer_cpow (v : HeightOneSpectrum (𝓞 K)) (t : ℝ) :
    (localComponent K v (heckeNormTwist K t) (localUniformizerUnit K v) : ℂ) =
      (residueCard K v : ℂ) ^ ((t : ℂ) * Complex.I) := by
  have hq : (residueCard K v : ℂ) ≠ 0 := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (one_lt_residueCard K v)).ne'
  rw [heckeNormTwist_uniformizer, Circle.coe_exp, Complex.cpow_def_of_ne_zero hq,
    ← Complex.natCast_log, Complex.ofReal_mul]
  congr 1
  ring

/-- Ramification is unchanged by the norm twist, and the Euler value gains q^(it). -/
theorem primeCoefficient_normTwist (χ : HeckeCharacter K) (t : ℝ)
    (v : HeightOneSpectrum (𝓞 K)) :
    primeCoefficient K (χ * heckeNormTwist K t) v =
      primeCoefficient K χ v * (residueCard K v : ℂ) ^ ((t : ℂ) * Complex.I) := by
  unfold primeCoefficient
  rw [unramifiedAt_mul_normTwist_iff]
  split_ifs with hχ
  · change (localComponent K v χ (localUniformizerUnit K v) : ℂ) *
      (localComponent K v (heckeNormTwist K t) (localUniformizerUnit K v) : ℂ) = _
    rw [heckeNormTwist_uniformizer_cpow]
  · simp

end HeckeGeneral.Characters
