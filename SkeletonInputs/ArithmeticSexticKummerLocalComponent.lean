import ArithmeticSexticKummerCharacter
import HeckeGeneral.Characters.LocalComponent
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibComparison

/-!
UNCOMPILED cache candidate, 2026-10-11. No Lean/Lake invocation was made.

Literal one-place transport for the actual arithmetic Artin/Kummer character.
The first import is the independent cache candidate of that bare module name;
its artifact must be available before this candidate can be checked.

This proves neither unramifiedness nor a residue-symbol coefficient formula.
It assumes no RowCharacterInput, coefficient identity, or reciprocity identity.
ArithmeticNormalization and MathlibTopologyComparison are already imported by
ArithmeticSexticKummerCharacter; MathlibComparison is listed explicitly here
because its one-place comparison theorem is used below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Characters.ArithmeticKummerDraft

open NumberField IsDedekindDomain KummerTheory

variable (K : Type) [Field K] [NumberField K]

/-- The project's continuous one-place map is Mathlib's literal quotient map. -/
theorem localIdeleClassMap_eq_mathlibOfAdicCompletion
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    localIdeleClassMap K v u =
      NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u := by
  rfl

/-- Transport the actual one-place class back to the upstream presentation. -/
theorem comparison_symm_localIdeleClassMap
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm
        (localIdeleClassMap K v u) =
      _root_.IdeleGroup.finitePlaceIdeleClass v u := by
  let comparison := _root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K
  have hforward : comparison (_root_.IdeleGroup.finitePlaceIdeleClass v u) =
      localIdeleClassMap K v u := by
    rw [localIdeleClassMap_eq_mathlibOfAdicCompletion]
    change _root_.IdeleGroup.ideleClassGroupEquivMathlib K
        (_root_.IdeleGroup.finitePlaceIdeleClass v u) = _
    exact _root_.IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass K v u
  change comparison.symm (localIdeleClassMap K v u) = _
  calc
    comparison.symm (localIdeleClassMap K v u) =
        comparison.symm (comparison (_root_.IdeleGroup.finitePlaceIdeleClass v u)) :=
      congrArg comparison.symm hforward.symm
    _ = _ := comparison.symm_apply_apply _

/-- Actual arithmetic local-global compatibility in the project's presentation.
The extension hypotheses are standard algebraic typeclasses, not a supplied
local-global compatibility conclusion. -/
theorem arithmeticArtin_localIdeleClassMap
    (L : Type) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L
        ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm
          (localIdeleClassMap K v u)) =
      GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
        K L v u := by
  rw [comparison_symm_localIdeleClassMap]
  simpa only [MonoidHom.comp_apply] using
    DFunLike.congr_fun
      (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
        K L v) u

private theorem localSixNeZero : (6 : K) ≠ 0 := by norm_num

/-- The actual local arithmetic Artin map followed by the same Kummer root and
Circle transport used in the global character. Its continuity is not needed
for the monoid-hom equality below. -/
def arithmeticSexticLocalArtinHom (embedding : K →+* ℂ)
    (hmu : (primitiveRoots 6 K).Nonempty) (a : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* Circle := by
  let E := sexticExtension K a
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K (6 : ℕ+) (localSixNeZero K) a
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K (6 : ℕ+) (localSixNeZero K) hmu a
  exact (simpleSexticCircleHom K embedding hmu a).comp
    (GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom K E v)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
/-- The actual local component agrees pointwise with the actual arithmetic
local Artin/Kummer construction. No inversion is inserted in this transport:
both global and local Artin maps already have arithmetic normalization. -/
theorem arithmeticSexticKummerCharacter_localComponent_apply
    (embedding : K →+* ℂ) (hmu : (primitiveRoots 6 K).Nonempty) (a : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    localComponent K v (arithmeticSexticKummerCharacter K embedding hmu a) u =
      arithmeticSexticLocalArtinHom K embedding hmu a v u := by
  let E := sexticExtension K a
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K (6 : ℕ+) (localSixNeZero K) a
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K (6 : ℕ+) (localSixNeZero K) hmu a
  change simpleSexticCircleHom K embedding hmu a
      (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K E
        ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm
          (localIdeleClassMap K v u))) =
    simpleSexticCircleHom K embedding hmu a
      (GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
        K E v u)
  exact congrArg (simpleSexticCircleHom K embedding hmu a)
    (arithmeticArtin_localIdeleClassMap K E v u)

/-- The same equality as an equality of monoid homomorphisms, retaining the
already constructed continuous local component on the left. -/
theorem arithmeticSexticKummerCharacter_localComponent
    (embedding : K →+* ℂ) (hmu : (primitiveRoots 6 K).Nonempty) (a : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    (localComponent K v (arithmeticSexticKummerCharacter K embedding hmu a)).toMonoidHom =
      arithmeticSexticLocalArtinHom K embedding hmu a v := by
  apply MonoidHom.ext
  intro u
  exact arithmeticSexticKummerCharacter_localComponent_apply K embedding hmu a v u

end HeckeGeneral.Characters.ArithmeticKummerDraft
