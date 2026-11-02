import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N6AnalyticChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N6SourceBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N6: one original Hecke certificate on the same allocated source

Only the original full mask and paired-row exclusion enter this
certificate. The finite-order boundary is the target's given boundary;
the same original canonical theta supplies inverse-slot membership.
The endpoint kappa equal to one does not request an analytic witness.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.N6

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open PrimeCancellation.Analytic
open EngineStep EngineInduction EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}
variable {H Row ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
variable {R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι}
variable {side : Bool}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter Row k}
variable {D : OriginalCalibration call s} {loss : ℝ}

/-- The analytic certificate and its original height bound are produced
from the fixed provider, rather than assumed for a transformed source. -/
def slotCertificate (choices : FullKappaChoices c loss)
    (G : SideGeometryData R side s D) (conditions : D.SourceConditions)
    (hκ : D.calibration.parameters.κ < 1) (ξ : EngineParameter)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u ∈ pairedRows (D.calibration.data ξ) D.calibration.parameters s.base)
    (i : Fin (D.calibration.data ξ).geometry.slotCount) :
    {analytic : ZeroFreeData
        (heckeContinuation K
          ((D.calibration.data ξ).rowCharacter u * (D.calibration.data ξ).slotCoefficient i))
        ((D.calibration.parameters.κ + 1) / 2) //
      heightConstant analytic + 3 * (analytic.k : ℝ) ≤
        choices.heightC * (1 + Real.log s.base)} :=
  choices.window.certificate D.recipe D.calibration.parameters s.base
    (by rw [D.kappa_eq]; exact call.domain.kappa_lower) hκ s.base_gt_one
    (targetDynamicFiniteOrderBoundary c D.calibration.parameters.κ
      (D.kappa_eq.trans call.kappa))
    (calibration_theta D) (calibration_slot D) (calibration_inverse_slot D)
    (calibration_totalLength D) (fullJointBudget_two G conditions.joint) ξ u hu i

end HeckeSkeleton.Moments.EngineStepV2.N6

#print axioms HeckeSkeleton.Moments.EngineStepV2.N6.slotCertificate
