import HeckeGeneral.Characters.SexticRootReduction
import HeckeGeneral.Arithmetic.FiniteFieldSexticCharacter

/-!
# Sextic residue characters normalized by one global root

The finite-field root is the actual reduction of the specified global
root, and the complex root is its image under the specified embedding.
Evaluation on algebraic integers is a function, not a multiplicative
character of the integer ring: a nonunit can have nonzero reduction.
No associated-modulus identification or reciprocity law is asserted.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (p : HeightOneSpectrum (𝓞 K)) (hp : (6 : 𝓞 K) ∉ p.asIdeal)

local instance : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
local instance : Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _

/-- The actual prime-ideal residue character, with both roots obtained from
the same specified global sixth root. -/
def sexticResidueCharacter : MulChar (𝓞 K ⧸ p.asIdeal) ℂ :=
  Arithmetic.FiniteFieldSexticCharacter.character (𝓞 K ⧸ p.asIdeal)
    (six_dvd_card_residue_sub_one K ζ hζ p hp)
    (sexticResidueRootUnit K ζ hζ p) (sexticComplexRootUnit K ζ hζ σ)
    (isPrimitiveRoot_sexticResidueRootUnit K ζ hζ p hp)
    (isPrimitiveRoot_sexticComplexRootUnit K ζ hζ σ)

@[simp] theorem sexticResidueCharacter_zero :
    sexticResidueCharacter K ζ hζ σ p hp 0 = 0 := by
  exact MulChar.map_nonunit _ (by simp)

theorem sexticResidueCharacter_norm (x : 𝓞 K ⧸ p.asIdeal) (hx : x ≠ 0) :
    ‖sexticResidueCharacter K ζ hζ σ p hp x‖ = 1 := by
  exact Arithmetic.FiniteFieldSexticCharacter.character_unit_norm
    _ _ _ _ _ _ (Units.mk0 x hx)

theorem sexticResidueCharacter_order :
    orderOf (sexticResidueCharacter K ζ hζ σ p hp) = 6 :=
  Arithmetic.FiniteFieldSexticCharacter.character_order _ _ _ _ _ _

theorem sexticResidueCharacter_ne_one :
    sexticResidueCharacter K ζ hζ σ p hp ≠ 1 :=
  Arithmetic.FiniteFieldSexticCharacter.character_ne_one _ _ _ _ _ _

/-- The literal power-residue formula; the specified root pairing is part
of the definition, rather than an existence assertion about a character. -/
theorem sexticResidueCharacter_power_residue (u : (𝓞 K ⧸ p.asIdeal)ˣ) :
    sexticResidueCharacter K ζ hζ σ p hp (u : 𝓞 K ⧸ p.asIdeal) =
      (((Arithmetic.FiniteFieldSexticCharacter.rootPair
          (sexticResidueRootUnit K ζ hζ p) (sexticComplexRootUnit K ζ hζ σ)
          (isPrimitiveRoot_sexticResidueRootUnit K ζ hζ p hp)
          (isPrimitiveRoot_sexticComplexRootUnit K ζ hζ σ))
        (Arithmetic.FiniteFieldSexticCharacter.powerResidueHom
          (𝓞 K ⧸ p.asIdeal) (six_dvd_card_residue_sub_one K ζ hζ p hp)
          (sexticResidueRootUnit K ζ hζ p)
          (isPrimitiveRoot_sexticResidueRootUnit K ζ hζ p hp) u) :
        Subgroup.zpowers (sexticComplexRootUnit K ζ hζ σ)) : ℂˣ) :=
  Arithmetic.FiniteFieldSexticCharacter.character_power_residue _ _ _ _ _ _ u

/-- If the actual power residue is the ith power of the reduced global
root, its value is the ith power of the image of that very global root. -/
theorem sexticResidueCharacter_of_power_residue (u : (𝓞 K ⧸ p.asIdeal)ˣ) (i : ℕ)
    (hu : u ^ ((Fintype.card (𝓞 K ⧸ p.asIdeal) - 1) / 6) =
      sexticResidueRootUnit K ζ hζ p ^ i) :
    sexticResidueCharacter K ζ hζ σ p hp (u : 𝓞 K ⧸ p.asIdeal) = (σ ζ) ^ i := by
  have he : Arithmetic.FiniteFieldSexticCharacter.powerResidueHom
      (𝓞 K ⧸ p.asIdeal) (six_dvd_card_residue_sub_one K ζ hζ p hp)
      (sexticResidueRootUnit K ζ hζ p)
      (isPrimitiveRoot_sexticResidueRootUnit K ζ hζ p hp) u =
        (⟨sexticResidueRootUnit K ζ hζ p ^ i, i, by simp⟩ :
          Subgroup.zpowers (sexticResidueRootUnit K ζ hζ p)) := by
    apply Subtype.ext
    exact hu
  rw [sexticResidueCharacter_power_residue, he,
    Arithmetic.FiniteFieldSexticCharacter.rootPair_pow]
  simp only [Units.val_pow_eq_pow_val, val_sexticComplexRootUnit]

/-- Evaluation on the original algebraic integers, retaining zero at the
prime and allowing nonunits of the integer ring outside that prime. -/
def sexticResidueEvaluation (a : 𝓞 K) : ℂ :=
  sexticResidueCharacter K ζ hζ σ p hp (Ideal.Quotient.mk p.asIdeal a)

theorem sexticResidueEvaluation_eq_zero_of_mem (a : 𝓞 K) (ha : a ∈ p.asIdeal) :
    sexticResidueEvaluation K ζ hζ σ p hp a = 0 := by
  unfold sexticResidueEvaluation
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, sexticResidueCharacter_zero]

theorem sexticResidueEvaluation_norm_of_not_mem (a : 𝓞 K) (ha : a ∉ p.asIdeal) :
    ‖sexticResidueEvaluation K ζ hζ σ p hp a‖ = 1 := by
  apply sexticResidueCharacter_norm
  exact fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h)

theorem sexticResidueEvaluation_mul (a b : 𝓞 K) :
    sexticResidueEvaluation K ζ hζ σ p hp (a * b) =
      sexticResidueEvaluation K ζ hζ σ p hp a *
        sexticResidueEvaluation K ζ hζ σ p hp b := by
  simp only [sexticResidueEvaluation, map_mul]

/-- Ordinary integer units reduce to units, so their sixth powers are in
the kernel without any restriction on the second argument. -/
theorem sexticResidueEvaluation_sixth_power_unit (u : (𝓞 K)ˣ) :
    sexticResidueEvaluation K ζ hζ σ p hp ((u : 𝓞 K) ^ 6) = 1 := by
  unfold sexticResidueEvaluation sexticResidueCharacter
  rw [map_pow]
  exact Arithmetic.FiniteFieldSexticCharacter.character_sixth_power
    _ _ _ _ _ _ (Units.map (Ideal.Quotient.mk p.asIdeal).toMonoidHom u)

theorem sexticResidueEvaluation_mul_sixth_power_unit (u : (𝓞 K)ˣ) (a : 𝓞 K) :
    sexticResidueEvaluation K ζ hζ σ p hp ((u : 𝓞 K) ^ 6 * a) =
      sexticResidueEvaluation K ζ hζ σ p hp a := by
  rw [sexticResidueEvaluation_mul, sexticResidueEvaluation_sixth_power_unit, one_mul]

end HeckeGeneral.Characters
