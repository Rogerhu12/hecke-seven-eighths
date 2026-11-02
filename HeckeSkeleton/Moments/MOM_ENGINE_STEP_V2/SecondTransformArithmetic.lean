import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondTransformRaw
import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.ProbeRowCharacters

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original arithmetic dictionary for the second source

The auxiliary coefficient record uses the existing allowed generators,
principal sextic characters and field-trace character. Its recipe proof
is constructed here; the source task does not assume a new arithmetic
comparison or a second-source identity.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open PrincipalProbeConstruction

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

def originalPrincipalCharacter (a : A.R) :
    MulChar (FiniteTransform.Residue A.R.toSubring a) ℂ :=
  if ha : a = 0 then 1 else
    GlobalPairCancel.principalCharacter A σ (Inputs.rowIdeal A a ha) a
      (Inputs.rowIdeal_generates A a ha)

theorem originalPrincipalCharacter_eq (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) :
    originalPrincipalCharacter (σ := σ) a =
      GlobalPairCancel.principalCharacter A σ I a ha := by
  rw [originalPrincipalCharacter, dif_neg ha.1]
  have hI : Inputs.rowIdeal A a ha.1 = I :=
    generatedIdeal_unique (Inputs.rowIdeal_generates A a ha.1) ha
  have he (I J : A.Exterior) (hIJ : I = J)
      (h₁ : A.Generates I a) (h₂ : A.Generates J a) :
      GlobalPairCancel.principalCharacter A σ I a h₁ =
        GlobalPairCancel.principalCharacter A σ J a h₂ := by
    subst J
    rfl
  exact he _ _ hI _ _

def originalPoissonData (C : A.GeneralArithmeticContext σ η hS) :
    ComparisonPoissonCoefficientData K A where
  generator := engineAllowedGenerator C
  generates := engineAllowedGenerator_generates C
  finiteResidue := Inputs.finiteResidue A
  character := originalPrincipalCharacter (σ := σ)
  additiveCharacter := {
    toFun := fun x => (A.fieldTraceCharacter x : ℂ)
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by
      intro x y
      exact congrArg Circle.coeHom (A.fieldTraceCharacter.map_add_eq_mul x y) }
  gammaTwo I := A.idealGauss σ hS I.val (engineAllowedGenerator C I.val)
    (engineAllowedGenerator_generates C I.val) 2
  theta a := if ha : a ≠ 0 then
    (A.correctionLS C.correction.Λ C.correction.G 1
      (A.diagonal (Units.mk0 (a : K) (by exact_mod_cast ha))) : ℂ) else 0

theorem originalPoissonData_recipes (C : A.GeneralArithmeticContext σ η hS) :
    GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B
      (originalPoissonData C) := by
  refine ⟨engineAllowedGenerator_allowed C, ?_, ?_, ?_⟩
  · intro I a ha
    exact originalPrincipalCharacter_eq I a ha
  · intro x
    rfl
  · intro I
    rfl

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate.originalPoissonData_recipes
