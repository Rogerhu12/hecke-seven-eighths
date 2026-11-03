import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FullKappaData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildProfileContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N6 compatibility contract and the original child-profile connection

The fixed choices, raw/clipped windows, constructed capacity and public
single-side task are imported from `FullKappaData`. This wrapper retains
the original child-profile connection and its unchanged public name.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

variable {c : TargetContext K} {call : Call c}
variable {H Row ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
variable {R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι}
variable {side : Bool}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter Row k}
variable {D : OriginalCalibration call s} {loss B : ℝ} {J₁ J₂ : ℕ}

namespace FullKappaSideResult

variable {choices : FullKappaChoices c loss} {G : SideGeometryData R side s D}
variable {windows : FullKappaWindows D B J₁ J₂}

/-- The positive raw window and the clipped window at the constructed
capacity radius refer to the same original functions. -/
def childProfiles (result : FullKappaSideResult choices G windows) :
    SideChildProfileInput D result.capacity where
  originalOrders := call.childOrders
  originalBudget ξ := polynomialProfileRadius B J₁ J₂ (WithLp.ofLp ξ)
  original := windows.raw
  clipped := result.profiles.clippedWindow


end FullKappaSideResult

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
