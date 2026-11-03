import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildProfileContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N7bProfileTransport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N7b: preserve positive profile support on the actual active child

Paper: Section 4.8, the normalization and final child-profile passage.
Use the original nonzero source to bound both clipping dilations, then
retain the same representatives, pre-removal radius, fixed removed-slot
set and frozen time. The base active-child annulus theorem performs
the local support argument. This task supplies its exact identification
through the two passive labels, comparison rectangles and dependent
family aggregation. The scheduled rank implication is already proved
in ChildProfileAssembly and is not assumed by this statement.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global
open EngineStep

variable {K : Type} [Field K] [NumberField K]

theorem child_profiles (c : TargetContext K) (p : SourceParameters c) :
    ChildProfileTask c p := by
  classical
  intro call input trace _ geometry _ raw _ O R C G profiles
  let N := Assembly.refinedNormalizedData raw O R C G
  change N.UnitWindows
  intro side b ξ
  have hactive := Finset.mem_filter.mp b.property
  have hupper := N7bProfileTransport.upper_bound input
  cases side with
  | false =>
    change InFixedProfileWindow Set.univ Set.univ call.childWindow call.childOrders
      (N.family.leftData N.labels b ξ)
    exact N7bProfileTransport.active_windows
      (D := (C b.val.1).side false b.val.2.1 b.val.2.2.2.1)
      (G := (G b.val.1).side false b.val.2.1 b.val.2.2.2.1)
      (profiles b.val.1 false b.val.2.1 b.val.2.2.2.1).original
      (profiles b.val.1 false b.val.2.1 b.val.2.2.2.1).clipped
      (N.family.leftChild N.labels b) hupper hactive.2.1 ξ
  | true =>
    change InFixedProfileWindow Set.univ Set.univ call.childWindow call.childOrders
      (N.family.rightData N.labels b ξ)
    exact N7bProfileTransport.active_windows
      (D := (C b.val.1).side true b.val.2.2.1 b.val.2.2.2.2)
      (G := (G b.val.1).side true b.val.2.2.1 b.val.2.2.2.2)
      (profiles b.val.1 true b.val.2.2.1 b.val.2.2.2.2).original
      (profiles b.val.1 true b.val.2.2.1 b.val.2.2.2.2).clipped
      (N.family.rightChild N.labels b) hupper hactive.2.2 ξ

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.child_profiles

