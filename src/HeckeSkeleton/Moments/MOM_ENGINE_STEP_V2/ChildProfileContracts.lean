module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildInvariantData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementAssembly

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N7b: positive unit windows of the same active children

The original positive window is distinct from the broad window used
to define clipping for zero sources. Both displayed windows describe
the same arithmetic calibration. The clipped budget is the literal
capacity radius; no descendant profile or replacement radius is an
input. Activity bounds the original clipping factors and permits the
same normalized, restricted, frozen profiles to retain positive support.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}
variable {H : Type} {k : ℕ}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}

/-- The raw positive support and the already paid clipped seminorms
are kept separate. N5b gives the original windows; N6 enlarges their
common budget to the exact radius of the capacity it constructs. -/
structure SideChildProfileInput (D : OriginalCalibration call s)
    (G : D.calibration.NormalizedCapacityData) where
  originalOrders : Finset (ℕ × ℕ)
  originalBudget : EngineParameter → ℝ
  original : ∀ ξ, RawProfileWindow Set.univ Set.univ call.window
    originalOrders (D.calibration.data ξ) (originalBudget ξ)
  clipped : ∀ ξ, RawProfileWindow Set.univ Set.univ
    (Set.Icc 0 (2 * call.prepared.upper)) call.childOrders
      (D.calibration.clippedData ξ) (G.radius ξ)

variable {p : SourceParameters c} {input : ProfileInput call}
variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}
variable {R : RefinementData O input}

def RefinementData.Calibrations.ChildProfileInputs
    (C : R.Calibrations) (G : C.Capacities) : Type :=
  ∀ side a rectangle,
    SideChildProfileInput (C.side side a rectangle) (G.side side a rectangle)

/-- Only the actual active children of the explicitly assembled family
occur in the conclusion. The strict scheduled profile primitive is then
obtained by the separate, fully proved rank bridge. -/
def ChildProfileTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (call : Call c) (input : ProfileInput call)
    (trace : SourceTrace call p), trace.Realizes →
    ∀ (geometry : GeometryFamily trace.second), geometry.Realizes →
    ∀ (raw : RawFamily geometry), raw.Realizes →
    ∀ (O : ∀ j : Fin raw.count, OrdinaryData (raw.packet j))
      (R : ∀ j, RefinementData (O j) input)
      (C : ∀ j, (R j).Calibrations) (G : ∀ j, (C j).Capacities),
      (∀ j, (C j).ChildProfileInputs (G j)) →
      (Assembly.refinedNormalizedData raw O R C G).UnitWindows

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
