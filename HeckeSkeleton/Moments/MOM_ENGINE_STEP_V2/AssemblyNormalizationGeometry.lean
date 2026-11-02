import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedMassContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildArithmeticContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildProfileContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildProfileAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RemainingMaskRadical
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RowBudgetPreservation

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Geometry and recursive invariants of the same N4/N6 children

The capacities are the literal N6 results in the canonical packets.
The original N4 length binding supplies strict width decrease and the
mesh. The calibration supplies the parent slot dictionary and kappa.
N7b supplies the positive unit windows of those same children; the
complete mask budget is transported directly from N4's source conditions.
No family, child or capacity is selected again in this assembly.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source Blueprint

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

section Side

variable {H Row ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
variable {rows : ActualSecondCorrelationRows
  (Arithmetic.data c) (Arithmetic.embedding c) H ι}
variable {side : Bool}
variable {source : ActualAllocatedSource
  (Arithmetic.data c) EngineParameter Row k}
variable {D : OriginalCalibration call source}
variable {loss B : ℝ} {J₁ J₂ : ℕ}
variable {choices : FullKappaChoices c loss}
variable {G : SideGeometryData rows side source D}
variable {windows : FullKappaWindows D B J₁ J₂}

/-- The support reparameterization preserves the parent width exactly. -/
theorem fullKappaChild_width
    (result : FullKappaSideResult choices G windows)
    (child : result.capacity.Child) :
    child.parameters.m + child.parameters.q ≤
      call.node.parameters.m + call.node.parameters.q - recipeInductionSigma c / 2 := by
  have bound := child.parameters_width_drop
  change child.parameters.m + child.parameters.q ≤
    call.workingParameters.m + call.workingParameters.q -
      recipeInductionSigma c / 2 at bound
  dsimp only [Call.workingParameters] at bound
  linarith

theorem fullKappaChild_mesh
    (result : FullKappaSideResult choices G windows)
    (child : result.capacity.Child) (ξ : EngineParameter) :
    (child.frozenData ξ).geometry.fitsMesh (momentMesh K c.family).val :=
  child.frozen_mesh ξ

end Side

/-- The full original mask, including its remaining ideal, pays the
row budget after clipping, normalization, restriction and freezing. -/
theorem normalizedChild_rowMask
    {Row : Type} {k : ℕ}
    {source : ActualAllocatedSource
      (Arithmetic.data c) EngineParameter Row k}
    (D : OriginalCalibration call source)
    {capacity : D.calibration.NormalizedCapacityData}
    (child : capacity.Child) (conditions : D.SourceConditions)
    (ξ : EngineParameter) :
    ActualRowMaskAdmissible (Arithmetic.data c)
      (child.frozenData ξ) child.parameters call.base := by
  have budget := D.recipe.effectiveMovingMaskRecipe_jointBudget source.base
    (D.calibration.parameters.m + D.calibration.parameters.q) conditions.joint
  have result := child.rowMaskAdmissible D.recipe.effectiveMovingMaskRecipe budget ξ
  rw [D.base_eq] at result
  exact result

section Family

variable {p : SourceParameters c} {F : FirstPresentation call p}
variable {family : FirstCauchyFamily F} {expansion : PoolExpansion family}
variable {second : SecondFamily expansion} {geometry : GeometryFamily second}
variable (raw : RawFamily geometry) (input : ProfileInput call)
variable (choices : FullKappaChoices c p.loss)
variable (packets : ∀ j : Fin raw.count, CanonicalMassPacket (raw.packet j) input choices)

local notation "N" => canonicalMassData raw input choices packets

set_option maxHeartbeats 1000000 in
/-- The kappa and mesh fields use the exact already selected child. -/
theorem canonicalKappaMesh : (N).KappaMeshInvariant := by
  intro side b ξ
  cases side with
  | false =>
    let D := (packets b.val.1).calibrations.side false b.val.2.1 b.val.2.2.2.1
    let result := (packets b.val.1).normalization false b.val.2.1 b.val.2.2.2.1
    let child := (N).family.leftChild (N).labels b
    exact ⟨child.kappa_eq.trans (D.kappa_eq.trans call.kappa),
      fullKappaChild_mesh result child ξ⟩
  | true =>
    let D := (packets b.val.1).calibrations.side true b.val.2.2.1 b.val.2.2.2.2
    let result := (packets b.val.1).normalization true b.val.2.2.1 b.val.2.2.2.2
    let child := (N).family.rightChild (N).labels b
    exact ⟨child.kappa_eq.trans (D.kappa_eq.trans call.kappa),
      fullKappaChild_mesh result child ξ⟩

set_option maxHeartbeats 1000000 in
/-- All output geometry comes from N4/N6 and the original N7b windows.
In particular no completed engine output is used as an input. -/
def canonicalOutputGeometry (windows : (N).UnitWindows) :
    (N).family.OutputGeometry (N).labels call.node.data call.node.parameters
      (recipeInductionSigma c) Set.univ call.childWindow call.childOrders where
  left_width b :=
    fullKappaChild_width
      ((packets b.val.1).normalization false b.val.2.1 b.val.2.2.2.1)
      ((N).family.leftChild (N).labels b)
  right_width b :=
    fullKappaChild_width
      ((packets b.val.1).normalization true b.val.2.2.1 b.val.2.2.2.2)
      ((N).family.rightChild (N).labels b)
  left_width_nonneg b := ((N).family.leftChild (N).labels b).parameters_width_nonneg
  right_width_nonneg b := ((N).family.rightChild (N).labels b).parameters_width_nonneg
  left_plain_left_nonneg b := ((N).family.leftChild (N).labels b).plain_left_nonneg
  left_plain_right_nonneg b := ((N).family.leftChild (N).labels b).plain_right_nonneg
  right_plain_left_nonneg b := ((N).family.rightChild (N).labels b).plain_left_nonneg
  right_plain_right_nonneg b := ((N).family.rightChild (N).labels b).plain_right_nonneg
  left_length b ξ := ((N).family.leftChild (N).labels b).frozen_total_length ξ
  right_length b ξ := ((N).family.rightChild (N).labels b).frozen_total_length ξ
  left_kappa b := ((N).family.leftChild (N).labels b).kappa_eq.trans
    ((packets b.val.1).calibrations.side false b.val.2.1 b.val.2.2.2.1).kappa_eq
  right_kappa b := ((N).family.rightChild (N).labels b).kappa_eq.trans
    ((packets b.val.1).calibrations.side true b.val.2.2.1 b.val.2.2.2.2).kappa_eq
  left_slots b ξ := by
    let D := (packets b.val.1).calibrations.side false b.val.2.1 b.val.2.2.2.1
    exact ((N).family.leftChild (N).labels b).frozen_slot_count_of_original_indices
      ξ _ D.originalSlots.index D.originalSlots.index.injective
  right_slots b ξ := by
    let D := (packets b.val.1).calibrations.side true b.val.2.2.1 b.val.2.2.2.2
    exact ((N).family.rightChild (N).labels b).frozen_slot_count_of_original_indices
      ξ _ D.originalSlots.index D.originalSlots.index.injective
  left_theta b ξ := (((N).family.leftChild (N).labels b).frozen_theta_eq ξ).trans
    (((packets b.val.1).calibrations.side false b.val.2.1 b.val.2.2.2.1).theta_eq ξ)
  right_theta b ξ := (((N).family.rightChild (N).labels b).frozen_theta_eq ξ).trans
    (((packets b.val.1).calibrations.side true b.val.2.2.1 b.val.2.2.2.2).theta_eq ξ)
  left_slot_characters b ξ i := by
    have h := ((N).family.leftChild (N).labels b).frozen_slot_in_theta ξ i
    have htheta : (((N).family.leftCalibration b.val).data ξ).theta =
        call.node.data.theta :=
      ((packets b.val.1).calibrations.side false b.val.2.1 b.val.2.2.2.1).theta_eq ξ
    rw [htheta] at h
    exact h
  right_slot_characters b ξ i := by
    have h := ((N).family.rightChild (N).labels b).frozen_slot_in_theta ξ i
    have htheta : (((N).family.rightCalibration b.val).data ξ).theta =
        call.node.data.theta :=
      ((packets b.val.1).calibrations.side true b.val.2.2.1 b.val.2.2.2.2).theta_eq ξ
    rw [htheta] at h
    exact h
  left_admissible b ξ :=
    ⟨windows false b ξ, normalizedChild_rowMask
      ((packets b.val.1).calibrations.side false b.val.2.1 b.val.2.2.2.1)
      ((N).family.leftChild (N).labels b)
      ((packets b.val.1).geometry.conditions false b.val.2.1 b.val.2.2.2.1) ξ⟩
  right_admissible b ξ :=
    ⟨windows true b ξ, normalizedChild_rowMask
      ((packets b.val.1).calibrations.side true b.val.2.2.1 b.val.2.2.2.2)
      ((N).family.rightChild (N).labels b)
      ((packets b.val.1).geometry.conditions true b.val.2.2.1 b.val.2.2.2.2) ξ⟩
  left_capacity b := ((N).family.leftChild (N).labels b).capacity
  right_capacity b := ((N).family.rightChild (N).labels b).capacity

end Family

/-- Consume the two N7 task statements on the same canonical family.
The scheduled invariant follows from the original strict-rank bridge. -/
theorem canonicalOutputAndRecursive
    {p : SourceParameters c}
    (arithmeticTask : ChildArithmeticTask c p)
    (profileTask : ChildProfileTask c p)
    (input : ProfileInput call)
    (trace : SourceTrace call p) (htrace : trace.Realizes)
    (geometry : GeometryFamily trace.second) (hgeometry : geometry.Realizes)
    (raw : RawFamily geometry) (hraw : raw.Realizes)
    (choices : FullKappaChoices c p.loss)
    (packets : ∀ j : Fin raw.count, CanonicalMassPacket (raw.packet j) input choices) :
    let N := canonicalMassData raw input choices packets
    N.family.OutputGeometry N.labels call.node.data call.node.parameters
      (recipeInductionSigma c) Set.univ call.childWindow call.childOrders ∧
      N.RecursiveAdmissible := by
  let O := fun j => (packets j).seed.ordinary
  let R := fun j => (packets j).seed.refinement input (packets j).support
  let C := fun j => (packets j).calibrations
  let G := fun j => (packets j).capacities
  let N := canonicalMassData raw input choices packets
  have sourceConditions : ∀ j, (C j).SourceConditions :=
    fun j => (packets j).geometry.conditions
  have childProfiles : ∀ j, (C j).ChildProfileInputs (G j) := by
    intro j side a rectangle
    exact ((packets j).normalization side a rectangle).childProfiles
  have arithmetic : N.ArithmeticInvariant :=
    arithmeticTask call input trace htrace geometry hgeometry raw hraw O R C G sourceConditions
  have windows : N.UnitWindows :=
    profileTask call input trace htrace geometry hgeometry raw hraw O R C G childProfiles
  have outputGeometry := canonicalOutputGeometry raw input choices packets windows
  refine ⟨outputGeometry, ?_⟩
  exact recursiveAdmissible_of_parts N
    (canonicalKappaMesh raw input choices packets) arithmetic
    (profileInvariant_of_windows N input.regular outputGeometry windows)

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.fullKappaChild_width
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.normalizedChild_rowMask
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.canonicalOutputGeometry
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.canonicalOutputAndRecursive

