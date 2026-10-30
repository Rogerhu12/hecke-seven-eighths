module

public import ThetaGlobal.FiniteSkeletonSource
public import ThetaGlobal.GlobalActualFrequency
public import ThetaGlobal.GlobalGeneratorPeriod
public import HeckeAxiom.ArithmeticAdapter

@[expose] public section

/-!
# The skeleton and theta source use the same generators and embedding

These identities specialize the construction to `Base.axiomChoice`.
They discharge the arithmetic identification needed by the literal
coefficient dictionary, without choosing another arithmetic context.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

theorem thetaRecipe_allowed :
    (thetaRecipe K c).probe.allowed =
      HeckeAxiom.recipeOfContext (axiomChoice K c).A (axiomChoice K c).C :=
  ThetaGlobal.GlobalSameChoice.recipe_allowed (axiomChoice K c) (axiomChoice_modulus_top K c)

theorem thetaRecipe_embedding :
    (thetaRecipe K c).σ = (arithmeticData K c).embedding := rfl

theorem thetaRecipe_root12 :
    (thetaRecipe K c).A.zeta12 = (arithmeticData K c).root12 := rfl

/-- Equality in the field's actual unit group, not only equality of
ideals or a new representative modulo sixth powers. -/
theorem thetaRecipe_generator (I : ExteriorIdeal K (places K c)) :
    ThetaGlobal.GlobalActualFrequency.generatorUnit K (places K c) (arithmeticData K c) I =
      (thetaRecipe K c).probe.allowed.generator
        ((HeckeAxiom.exteriorEquiv (thetaRecipe K c).A).symm I) := by
  rw [thetaRecipe_allowed]
  apply Units.ext
  exact HeckeAxiom.thetaArithmeticData_generator (axiomChoice K c).A
    (HeckeAxiom.recipeOfContext (axiomChoice K c).A (axiomChoice K c).C)
    (complexEmbedding K c) (axiomChoice K c).different I

/-- The fixed row unit, rather than a fresh quotient representative,
appears in the literal periodValue of the marked coefficient. -/
theorem thetaRecipe_period_generator
    (θ : HeckeGeneral.Characters.HeckeCharacter K)
    (hS : HeckeGeneral.Characters.conductorPlaces K θ ⊆ (thetaRecipe K c).A.Sf)
    (d : MarkedDatum K (places K c)) (I : ExteriorIdeal K (places K c)) :
    ThetaGlobal.GlobalTargetPeriod.period (thetaRecipe K c) θ
      (QuotientGroup.mk d.rowUnit)
      ((thetaRecipe K c).A.diagonal
        (ThetaGlobal.GlobalActualFrequency.generatorUnit K (places K c)
          (arithmeticData K c) I)) =
      periodValue K (places K c) (arithmeticData K c) d θ I := by
  rw [thetaRecipe_generator, ThetaGlobal.GlobalGeneratorPeriod.period_generator
    (thetaRecipe K c) θ hS,
    ThetaGlobal.GlobalGeneratorPeriod.sexticResidue_unitRepresentative]
  rw [periodValue, (axiomChoice K c).idealSymbol_eq I]
  simp only [Equiv.apply_symm_apply] <;> rfl

theorem thetaRecipe_period_representative
    (θ : HeckeGeneral.Characters.HeckeCharacter K)
    (hS : HeckeGeneral.Characters.conductorPlaces K θ ⊆ (thetaRecipe K c).A.Sf)
    (d : MarkedDatum K (places K c)) (i : ReflectionIndex K (places K c) d) :
    ThetaGlobal.GlobalTargetPeriod.period (thetaRecipe K c) θ
      (QuotientGroup.mk d.rowUnit)
      ((thetaRecipe K c).A.diagonal
        (ThetaGlobal.GlobalActualFrequency.representative K (places K c)
          (arithmeticData K c) d i)) =
      periodValue K (places K c) (arithmeticData K c) d θ i.numeratorFrozen *
      periodValue K (places K c) (arithmeticData K c) d θ i.c *
      periodValue K (places K c) (arithmeticData K c) d θ i.n ^ 3 *
      periodValue K (places K c) (arithmeticData K c) d θ d.moving ^ (-2 : ℤ) *
      periodValue K (places K c) (arithmeticData K c) d θ
        (activeFrozenIdeal K (places K c) d i) ^ (-2 : ℤ) *
      periodValue K (places K c) (arithmeticData K c) d θ
        (activeMarkedIdeal K (places K c) d i) ^ (-2 : ℤ) := by
  simp only [ThetaGlobal.GlobalActualFrequency.representative, map_mul, map_pow, map_zpow,
    ThetaGlobal.GlobalGeneratorPeriod.period_diagonal_unit (thetaRecipe K c) θ hS,
    thetaRecipe_period_generator K c θ hS d, one_mul]

end HeckeSkeleton
