import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PreparedCall
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinSourcePreparation

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original input of one blueprint call

This record contains the original recursive request and its literal
Mellin preprocessing. No transformed source, leaf, child, terminal or
kernel estimate is a field. Stage parameters and their input conditions
are selected by the separate uniform tasks before such a call is used.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

local instance callReflectionMeasurable : MeasurableSpace (ℕ × Bool) := ⊤
local instance callReflectionSingleton : MeasurableSingletonClass (ℕ × Bool) := by
  constructor
  intro x
  trivial

structure Call (c : TargetContext K) where
  frame : SourceFrame
  schedule : OrderSchedule
  Cp : ℝ
  Hp : ℝ
  bounds : UniformBounds
  request : SourceRequest c frame schedule Cp Hp bounds
  prepared : PreparedCall request.parent
  frequency : ℝ × ℝ

namespace Call

variable {c : TargetContext K} (call : Call c)

def node : Node K c.family.omega (targetCharacter K c) :=
  call.prepared.model call.frequency

def base : ℝ := call.request.base

def primitive : MomentData K c.family.omega (targetCharacter K c) →
    PairedInvariantParameters → Prop := call.request.primitive

/-- The original complete recipe, including its prime support and both
arithmetic budgets, is transported by the merged Mellin constructor. -/
def source : CompleteSourceBudgetData c
    (Expansion.Project.canonicalDetectorTheta K (targetCharacter K c))
    call.base call.node.data (pairedInvariantParameters call.node.parameters) :=
  call.request.preparedSourceData call.prepared call.frequency

def normProfiles : EngineStep.NormProfileRecipe (fun _ : PUnit.{1} => call.node.data) :=
  (call.request.preparedNormProfiles call.prepared).at call.frequency

def original : OriginalInput c call.node call.base :=
  call.request.originalInput call.prepared call.frequency

/-- Restricting to the actual paired rows changes only the row
predicate; the complete dictionary and original profiles are retained. -/
def localizedData : MomentData K c.family.omega (targetCharacter K c) :=
  EngineStep.localizeOriginalParent call.node.data call.node.parameters call.base

def localizedSource : CompleteSourceBudgetData c
    (Expansion.Project.canonicalDetectorTheta K (targetCharacter K c))
    call.base call.localizedData (pairedInvariantParameters call.node.parameters) :=
  call.source.localized

def localizedNormProfiles :
    EngineStep.NormProfileRecipe (fun _ : PUnit.{1} => call.localizedData) :=
  EngineStep.localizedNormProfileRecipe call.normProfiles call.node.parameters call.base

/-- Geometric eligibility is inherited from the unchanged original
parameters, comparison lengths and slot geometry. -/
def domain : EngineStep.PairedEngineDomain call.node.centered call.node.data
    call.node.parameters call.base
    (call.base ^ call.node.comparison₁) (call.base ^ call.node.comparison₂)
    (16 * recipeInductionSigma c) (recipeInductionSigma c / 16) :=
  call.request.parent.mellinStrictModel_domain (Ω := CombinedParameter)
    call.prepared.cap call.prepared.order call.prepared.weight
    call.prepared.lower call.prepared.upper call.prepared.weight_nonneg
    call.prepared.lower_pos call.prepared.interval call.prepared.profileBudget
    call.prepared.profileBudget_one_le call.frequency call.request.domain

theorem base_pos : 0 < call.base := zero_lt_one.trans call.domain.scale

theorem fitsMesh : call.node.data.geometry.fitsMesh (momentMesh K c.family).val :=
  call.request.fitsMesh

theorem kappa : call.node.parameters.κ = 2 * c.family.B - 1 :=
  call.request.kappa

theorem width_le : call.node.parameters.m + call.node.parameters.q ≤ 2 :=
  call.request.node.down.property.width_le

theorem slots_le : call.node.data.geometry.slotCount ≤ c.geometry.slots :=
  call.request.node.down.property.slot_count

end Call
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
