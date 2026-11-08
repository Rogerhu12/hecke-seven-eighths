module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FiniteLeavesTraceCover
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FiniteLeavesAssembly

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S6: independent source proof task

Paper: Section 4.8, lines 2908--2925. The complete statement and
its original-source data are in RawContracts. The actual occurrence
covers and exact deletion of zero-cost keys preserve the same two
kernels and enumerate each live active leaf exactly once.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem finiteLeaves (c : TargetContext K) (p : SourceParameters c) :
    FiniteLeafTask c p := by
  intro call trace htrace geometry _hgeometry
  obtain ⟨covers, hcovers⟩ := FiniteLeaves.covers_of_trace trace htrace
  exact FiniteLeaves.finiteLeaves_of_covers geometry htrace.second covers hcovers

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.finiteLeaves


