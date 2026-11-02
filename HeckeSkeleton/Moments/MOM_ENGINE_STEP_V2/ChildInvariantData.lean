import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PrimitiveAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.EstimateData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The separate invariant tasks name the same actual children

The arithmetic part includes both complete-source budgets and the
reflection arithmetic primitive. The profile part is the exact
scheduled annulus primitive. Kappa and mesh are supplied by the real
capacity construction. None of these definitions chooses a child.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineInduction EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

def Call.childWindow (call : Call c) : Set ℝ :=
  Set.Icc ((call.prepared.lower / 2) / (2 * call.prepared.upper))
    (2 * call.prepared.upper)

namespace NormalizedData

variable (N : NormalizedData call)

def childData (side : Bool) (b : N.Active) (ξ : EngineParameter) :
    MomentData K c.family.omega (targetCharacter K c) :=
  if side then N.family.rightData N.labels b ξ else N.family.leftData N.labels b ξ

def childParameters (side : Bool) (b : N.Active) : RealParameters :=
  if side then N.family.rightParameters N.labels b else N.family.leftParameters N.labels b

def KappaMeshInvariant : Prop :=
  ∀ side b ξ,
    (N.childParameters side b).κ = 2 * c.family.B - 1 ∧
      (N.childData side b ξ).geometry.fitsMesh (momentMesh K c.family).val

def ArithmeticInvariant : Prop :=
  ∀ side b ξ,
    actualCompleteSourceBudgetPrimitive c call.base (N.childData side b ξ)
      (pairedInvariantParameters (N.childParameters side b)) ∧
    admissibleOfInvariant
      (reflectionArithmeticPrimitive (places K c) (probeData K c)
        (momentRowCharacters K c) (recipeThetaFamily (expansionRecipeRaw K c)) call.base)
      (N.childData side b ξ) (N.childParameters side b)

def ProfileInvariant : Prop :=
  ∀ side b ξ, admissibleOfInvariant
    (rankedAnnulusProfilePrimitive 1 call.schedule.engine call.frame.reflection
      (recipeInductionSigma c) 2 (recipeInductionSigma c / 16) call.frame.decay
      (profileFamilyBudget call.Cp call.Hp call.request.height)
      call.frame.lower call.frame.upper)
    (N.childData side b ξ) (N.childParameters side b)

/-- The positive lower endpoint is the actual clipping enlargement
used by the strict rank schedule. The public children are already
frozen; no new profile is substituted in this predicate. -/
def UnitWindows : Prop :=
  ∀ side b ξ, EngineStep.InFixedProfileWindow Set.univ Set.univ
    call.childWindow call.childOrders (N.childData side b ξ)

end NormalizedData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField HeckeGeneral.ThetaSkeleton.Global Blueprint

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

theorem recursiveAdmissible_of_parts (N : NormalizedData call)
    (geometry : N.KappaMeshInvariant) (arithmetic : N.ArithmeticInvariant)
    (profiles : N.ProfileInvariant) : N.RecursiveAdmissible := by
  have hside (side : Bool) (b : N.Active) (ξ : EngineParameter) :=
    recursiveAdmissible call (N.childData side b ξ) (N.childParameters side b)
      (geometry side b ξ).1 (arithmetic side b ξ).1 (geometry side b ξ).2
      (arithmetic side b ξ).2 (profiles side b ξ)
  exact ⟨fun b ξ => hside false b ξ, fun b ξ => hside true b ξ⟩

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.recursiveAdmissible_of_parts
