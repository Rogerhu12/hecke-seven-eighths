import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualChildPrimitive
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualRecipeTheta
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.EngineOutputBudget
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ParameterTransport

/-!
# The actual source output enters the recursive labels

This adapter consumes the owner's literal children with their proved
prime supports and scheduled profile controls. It reconstructs the full
complete-recipe primitive, freezes the same child at its zero evaluation
time, pays only the fixed scalar and exponent budgets, and embeds the
same positive kernel into the common strict/reflection parameter space.

The recursive labels are then built from these actual children by the
existing universal-node constructor. No child moment estimate is used.
The actual single-step source constructor remains the producer of the
input output record; this transport does not assert that it is inhabited.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open Expansion.Project EngineStep

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]
variable {Ωengine : Type} [MeasurableSpace Ωengine]
variable {Q : Type*} {rowDomain : Set (NonzeroIdeal K)} {window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)}

/-- The same actual children and positive kernels enter the common
parameter space with the original recipe's complete primitive. -/
def actualRecipeEngineOutput
    (n : Node K c.family.omega (targetCharacter K c))
    (sourceParent : MomentData K c.family.omega (targetCharacter K c))
    (U delta beta coefficient control commonCoefficient : ℝ)
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (A Cp Hp lower upper T : ℝ)
    (out : n.EngineOutput (Ω := Ωengine) U (recipeInductionSigma c)
      delta beta coefficient control
      (MovingEngineChildAdmissible (axiomChoice K c).A
        (probeData K c) (momentRowCharacters K c) Q sourceParent rowDomain window orders U))
    (htheta : n.data.theta = canonicalDetectorTheta K (targetCharacter K c))
    (hkappa : n.parameters.κ = 2 * c.family.B - 1)
    (hmesh : sourceParent.geometry.fitsMesh (momentMesh K c.family).val)
    (hleftPrime : ∀ b xi, PrimeProfileSupport (out.leftData b xi))
    (hrightPrime : ∀ b xi, PrimeProfileSupport (out.rightData b xi))
    (hleftProfile : ∀ b xi, admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection (recipeInductionSigma c) 2
        (recipeInductionSigma c / 16) A (profileFamilyBudget Cp Hp T) lower upper)
      (freezeMomentTime (out.leftData b xi) 0) (out.leftParameters b))
    (hrightProfile : ∀ b xi, admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection (recipeInductionSigma c) 2
        (recipeInductionSigma c / 16) A (profileFamilyBudget Cp Hp T) lower upper)
      (freezeMomentTime (out.rightData b xi) 0) (out.rightParameters b))
    (hU : 1 ≤ U) (hcommon : 0 ≤ commonCoefficient)
    (hbudget : coefficient * control ≤ commonCoefficient)
    (hdelta : delta ≤ recipeInductionEdgeLoss c)
    (hbeta : beta ≤ recipeInductionTerminalLoss c)
    (original : Ωengine) :
    n.EngineOutput (Ω := RecipeMellinParameter Ωengine)
      U (recipeInductionSigma c) (recipeInductionEdgeLoss c) (recipeInductionTerminalLoss c)
      commonCoefficient 1
      (admissibleOfInvariant
        (recipeDataReflectionPrimitive c (recipeThetaFamily (expansionRecipeRaw K c))
          (actualCompleteSourceBudgetPrimitive c) ground engine reflection
          (recipeInductionSigma c) (recipeInductionSigma c / 16)
          A Cp Hp lower upper U T)) := by
  let actual := frozenCompleteRecipeEngineOutput n sourceParent
    (recipeInductionSigma c) delta beta coefficient control (recipeInductionSigma c / 16)
    A Cp Hp lower upper T ground engine reflection out htheta hkappa hmesh
    hleftPrime hrightPrime hleftProfile hrightProfile
  let paid := enlargeEngineOutputBudget actual hU
    (show coefficient * control ≤ commonCoefficient * 1 by simpa only [mul_one] using hbudget)
    (show 0 ≤ commonCoefficient * 1 by simpa only [mul_one] using hcommon) hdelta hbeta
  let embedded := paid.mapParameter
    (Sum.inl : Ωengine → RecipeMellinParameter Ωengine) measurableEmbedding_parameterInl
    (parameterInlRetraction original) (parameterInlRetraction_leftInverse original)
  simpa only [actualRecipeThetaFamily] using embedded

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualRecipeEngineOutput
