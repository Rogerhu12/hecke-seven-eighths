import HeckeGeneral.Characters.SexticResidueCharacter
import HeckeGeneral.Arithmetic.SIntegerResidue

/-!
# Actual S-integer evaluation of the normalized sextic residue character

The exterior residue map is constructed from the proved localization
residue equivalence. Its denominator is genuinely invertible modulo the
prime. The sixth-power condition on the original subgroup is explicit;
it is not inferred from finite index. Evaluation is a function on the
S-integer ring, not a zero-extension character of that ring.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)

local instance : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
local instance : Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _

include hpS in
theorem sIntegerSexticResidue_coprime :
    ∀ v ∈ S, p.asIdeal ⊔ v.asIdeal = ⊤ := by
  intro v hv
  have hne : p ≠ v := fun h => hpS (h.symm ▸ hv)
  simpa only [pow_one] using (p.isCoprime_pow_of_ne v hne 1 1).sup_eq

include hpS in
/-- The denominator invertibility used by the actual residue equivalence. -/
theorem sIntegerSexticResidue_denominator_isUnit :
    IsUnit (Ideal.Quotient.mk p.asIdeal (finiteSIntegerDenominator K S)) := by
  exact isUnit_quotient_of_sup_span_eq_top (finiteSIntegerDenominator K S) p.asIdeal
    (sup_span_finiteSIntegerDenominator_eq_top K S p.asIdeal
      (sIntegerSexticResidue_coprime K S p hpS))

/-- Actual exterior reduction of all S-integers, including those with
nontrivial denominators. -/
def sIntegerSexticResidueMap : S.integer K →+* (𝓞 K ⧸ p.asIdeal) :=
  (sIntegerResidueEquiv K S p.asIdeal
    (sIntegerSexticResidue_coprime K S p hpS)).symm.toRingHom.comp
      (Ideal.Quotient.mk (p.asIdeal.map (algebraMap (𝓞 K) (S.integer K))))

@[simp] theorem sIntegerSexticResidueMap_algebraMap (a : 𝓞 K) :
    sIntegerSexticResidueMap K S p hpS (algebraMap (𝓞 K) (S.integer K) a) =
      Ideal.Quotient.mk p.asIdeal a :=
  sIntegerResidueEquiv_symm_mk K S p.asIdeal
    (sIntegerSexticResidue_coprime K S p hpS) a

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hp : (6 : 𝓞 K) ∉ p.asIdeal)

/-- Reduction followed by the actual power-residue character normalized
using the reduction and complex image of the same global root ζ. -/
def sIntegerSexticEvaluation (a : S.integer K) : ℂ :=
  sexticResidueCharacter K ζ hζ σ p hp (sIntegerSexticResidueMap K S p hpS a)

@[simp] theorem sIntegerSexticEvaluation_algebraMap (a : 𝓞 K) :
    sIntegerSexticEvaluation K S p hpS ζ hζ σ hp
        (algebraMap (𝓞 K) (S.integer K) a) =
      sexticResidueEvaluation K ζ hζ σ p hp a := by
  simp only [sIntegerSexticEvaluation, sIntegerSexticResidueMap_algebraMap,
    sexticResidueEvaluation]

theorem sIntegerSexticEvaluation_mul (a b : S.integer K) :
    sIntegerSexticEvaluation K S p hpS ζ hζ σ hp (a * b) =
      sIntegerSexticEvaluation K S p hpS ζ hζ σ hp a *
        sIntegerSexticEvaluation K S p hpS ζ hζ σ hp b := by
  simp only [sIntegerSexticEvaluation, map_mul]

@[simp] theorem sIntegerSexticEvaluation_zero :
    sIntegerSexticEvaluation K S p hpS ζ hζ σ hp 0 = 0 := by
  simp only [sIntegerSexticEvaluation, map_zero, sexticResidueCharacter_zero]

/-- S-units reduce to actual residue units by applying the constructed
ring hom to their unit in the S-integer ring. -/
def sUnitSexticResidueUnit (u : S.unit K) : (𝓞 K ⧸ p.asIdeal)ˣ :=
  Units.map (sIntegerSexticResidueMap K S p hpS).toMonoidHom
    (S.unitEquivUnitsInteger K u)

@[simp] theorem sUnitSexticResidueUnit_val (u : S.unit K) :
    (sUnitSexticResidueUnit K S p hpS u : 𝓞 K ⧸ p.asIdeal) =
      sIntegerSexticResidueMap K S p hpS (S.unitEquivUnitsInteger K u).val := rfl

theorem sIntegerSexticEvaluation_sixth_power_unit (u : S.unit K) :
    sIntegerSexticEvaluation K S p hpS ζ hζ σ hp
      ((S.unitEquivUnitsInteger K u).val ^ 6) = 1 := by
  unfold sIntegerSexticEvaluation sexticResidueCharacter
  rw [map_pow]
  exact Arithmetic.FiniteFieldSexticCharacter.character_sixth_power
    _ _ _ _ _ _ (sUnitSexticResidueUnit K S p hpS u)

theorem sIntegerSexticEvaluation_mul_sixth_power_unit (u : S.unit K) (a : S.integer K) :
    sIntegerSexticEvaluation K S p hpS ζ hζ σ hp
      ((S.unitEquivUnitsInteger K u).val ^ 6 * a) =
        sIntegerSexticEvaluation K S p hpS ζ hζ σ hp a := by
  rw [sIntegerSexticEvaluation_mul, sIntegerSexticEvaluation_sixth_power_unit, one_mul]

/-- Literal invariance for the original subgroup, with its actual
sixth-power inclusion supplied explicitly. Zero and nonunits are included. -/
theorem sIntegerSexticEvaluation_literal_invariant
    (Γ : Subgroup (S.unit K))
    (hΓ : Γ ≤ (powMonoidHom 6 : S.unit K →* S.unit K).range) :
    ∀ γ : Γ, ∀ a : S.integer K,
      sIntegerSexticEvaluation K S p hpS ζ hζ σ hp
        ((S.unitEquivUnitsInteger K γ.val).val * a) =
          sIntegerSexticEvaluation K S p hpS ζ hζ σ hp a := by
  intro γ a
  obtain ⟨u, hu⟩ := hΓ γ.property
  have hu' : u ^ 6 = γ.val := hu
  rw [← hu', map_pow, Units.val_pow_eq_pow_val]
  exact sIntegerSexticEvaluation_mul_sixth_power_unit K S p hpS ζ hζ σ hp u a

end HeckeGeneral.Characters
