module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S5RowWindow
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S5SupportWindow

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S5: independent source proof task

Paper: Section 4.8, lines 2895--2906. The complete statement and
its original-source data are in GeometryContracts. The proof constructs
both nominal sides from a single actual live frequency and the original
source trace, then supplies the physical row and paid-support windows.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem nominalGeometry (c : TargetContext K) (p : SourceParameters c) :
    NominalGeometryTask c p := by
  intro call trace realized
  let geometry : GeometryFamily trace.second := {
    geometry := fun key active => S5Proof.classGeometry trace realized key active }
  refine ⟨geometry, ?_⟩
  intro key active
  change (S5Proof.classGeometry trace realized key active).Realizes
  exact {
    first := S5Proof.classGeometry_first trace realized key active
    opposite := S5Proof.classGeometry_opposite trace realized key active
    complementary := S5Proof.classGeometry_complementary trace realized key active
    second := S5Proof.classGeometry_second trace realized key active
    secondOpposite := S5Proof.classGeometry_secondOpposite trace realized key active
    unitPart := S5Proof.classGeometry_unitPart trace realized key active
    nonunitPart := S5Proof.classGeometry_nonunitPart trace realized key active
    tag := fun _ => rfl
    retainedScale := fun _ => rfl
    supportError := fun _ => rfl
    width := S5Proof.class_width (S5Proof.classGeometry trace realized key active)
    slack := S5Proof.class_slack (S5Proof.classGeometry trace realized key active)
    correlation := S5Proof.classGeometry_correlation trace realized key active
    rowWindow := S5Proof.classGeometry_rowWindow trace realized key active
    supportWindow := S5Proof.classGeometry_supportWindow trace realized key active }

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.nominalGeometry


