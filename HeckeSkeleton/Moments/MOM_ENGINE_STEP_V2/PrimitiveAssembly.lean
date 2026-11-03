import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CallData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The five exact components of the original recursive primitive

The arithmetic dictionary, both complete-source budgets, original mesh
and scheduled profile control all refer to the displayed child. This
lemma merely assembles their unchanged conjunction; it proves no new
analytic estimate and selects no replacement child.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}

theorem recursiveAdmissible (call : Call c)
    (d : MomentData K c.family.omega (targetCharacter K c)) (a : RealParameters)
    (hkappa : a.κ = 2 * c.family.B - 1)
    (hsource : actualCompleteSourceBudgetPrimitive c call.base d
      (pairedInvariantParameters a))
    (hmesh : d.geometry.fitsMesh (momentMesh K c.family).val)
    (harithmetic : admissibleOfInvariant
      (reflectionArithmeticPrimitive (places K c) (probeData K c)
        (momentRowCharacters K c) (recipeThetaFamily (expansionRecipeRaw K c)) call.base) d a)
    (hprofiles : admissibleOfInvariant
      (rankedAnnulusProfilePrimitive 1 call.schedule.engine call.frame.reflection
        (recipeInductionSigma c) 2 (recipeInductionSigma c / 16) call.frame.decay
        (profileFamilyBudget call.Cp call.Hp call.request.height)
        call.frame.lower call.frame.upper) d a) :
    admissibleOfInvariant call.primitive d a :=
  ⟨hkappa, hsource, hmesh, harithmetic, hprofiles⟩

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.recursiveAdmissible
