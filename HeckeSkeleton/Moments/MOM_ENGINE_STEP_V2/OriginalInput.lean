import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourcePrimitive
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOriginalAtlas

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original complete arithmetic source of a strict call

Only the complete moving-row dictionary and the original norm-profile
identity enter this record.  The actual finite coefficient, its two
rectangles, and all prime slots are computed from those inputs.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ActualSIntegerMoments
open EngineStep EngineInduction

variable {K : Type} [Field K] [NumberField K]

structure OriginalInput (c : TargetContext K)
    (n : Node K c.family.omega (targetCharacter K c)) (Z : ℝ) where
  theta : Finset (HeckeCharacter K)
  source : CompleteSourceData c theta n.data
  normProfiles : NormProfileRecipe (fun _ : PUnit.{1} => n.data)

namespace OriginalInput

variable {c : TargetContext K}
variable {n : Node K c.family.omega (targetCharacter K c)} {Z : ℝ}

def raw (input : OriginalInput c n Z) :
    ParentRawAtoms (ActualSIntegerOrbit K (places K c)) n.data n.parameters
      Z 0 (Z ^ n.comparison₁) (Z ^ n.comparison₂) :=
  (input.source.arithmeticAtoms.constantAtoms input.normProfiles n.parameters Z 0).raw
    (Z ^ n.comparison₁) (Z ^ n.comparison₂)

end OriginalInput
end HeckeSkeleton.Moments.EngineStepV2
