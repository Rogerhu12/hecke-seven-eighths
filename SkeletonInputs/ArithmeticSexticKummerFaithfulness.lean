import ArithmeticSexticKummerCharacter
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic

/-!
Faithfulness of the actual arithmetic-Artin/simple-Kummer character.
The global Artin map is the actual surjective arithmetic norm-residue map.
Triviality of the constructed character therefore forces the chosen root
to be fixed by every Galois automorphism, hence to lie in the base field.
No character-faithfulness premise or abstract Artin datum is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeGeneral.Characters.ArithmeticKummerFaithfulness

open NumberField KummerTheory
open HeckeGeneral.Characters HeckeGeneral.Characters.ArithmeticKummerDraft

variable (K : Type) [Field K] [NumberField K]

private theorem six_ne_zero : (6 : K) ≠ 0 := by norm_num

theorem sixthRootsToCircle_injective (embedding : K →+* ℂ) :
    Function.Injective (sixthRootsToCircle K embedding) := by
  intro r s h
  apply Subtype.ext
  apply Units.ext
  apply embedding.injective
  exact congrArg (fun z : Circle => (z : ℂ)) h

theorem simpleSexticCircleHom_injective (embedding : K →+* ℂ)
    (hmu : (primitiveRoots 6 K).Nonempty) (a : Kˣ) :
    Function.Injective (simpleSexticCircleHom K embedding hmu a) := by
  exact (sixthRootsToCircle_injective K embedding).comp
    ((nthRootsSubgroupEquivOfPrimitiveRoots K (sexticExtension K a)
      (6 : ℕ+) hmu).symm.injective.comp
        (chosenSimpleKummerRootCharacter_injective K (6 : ℕ+) (six_ne_zero K) hmu a))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem gal_eq_one_of_arithmeticSexticKummerCharacter_eq_one
    (embedding : K →+* ℂ) (hmu : (primitiveRoots 6 K).Nonempty) (a : Kˣ)
    (hχ : arithmeticSexticKummerCharacter K embedding hmu a = 1) :
    ∀ σ : Gal((sexticExtension K a)/K), σ = 1 := by
  let E := sexticExtension K a
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K (6 : ℕ+) (six_ne_zero K) a
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K (6 : ℕ+) (six_ne_zero K) hmu a
  intro σ
  obtain ⟨c, hc⟩ :=
    GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_surjective K E σ
  have hvalue := congrArg (fun η : HeckeCharacter K =>
    η ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K) c)) hχ
  change simpleSexticCircleHom K embedding hmu a
      (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K E
        ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm
          ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K) c))) = 1 at hvalue
  rw [ContinuousMulEquiv.symm_apply_apply, hc] at hvalue
  apply simpleSexticCircleHom_injective K embedding hmu a
  rw [map_one]
  exact hvalue

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem exists_field_sixthRoot_of_arithmeticSexticKummerCharacter_eq_one
    (embedding : K →+* ℂ) (hmu : (primitiveRoots 6 K).Nonempty) (a : Kˣ)
    (hχ : arithmeticSexticKummerCharacter K embedding hmu a = 1) :
    ∃ b : K, b ^ 6 = (a : K) := by
  let E := sexticExtension K a
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K (6 : ℕ+) (six_ne_zero K) a
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K (6 : ℕ+) (six_ne_zero K) hmu a
  let r : E := chosenSimpleKummerRootUnit K (6 : ℕ+) (six_ne_zero K) a
  have hfixed : ∀ σ : Gal(E/K), σ r = r := by
    intro σ
    rw [gal_eq_one_of_arithmeticSexticKummerCharacter_eq_one K embedding hmu a hχ σ]
    rfl
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed r).mpr hfixed
  have hr : r ^ 6 = algebraMap K E (a : K) := by
    have h := congrArg (fun u : Eˣ => (u : E))
      (chosenSimpleKummerRootUnit_pow K (6 : ℕ+) (six_ne_zero K) a)
    exact h
  refine ⟨b, ?_⟩
  apply (algebraMap K E).injective
  rw [map_pow, hb, hr]

end HeckeGeneral.Characters.ArithmeticKummerFaithfulness
