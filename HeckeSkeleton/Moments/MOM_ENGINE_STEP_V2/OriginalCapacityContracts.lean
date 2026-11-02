import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalRefinement
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SideGeometryData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: capacity data for the original calibrated residual sources

Every entry names the same source produced by the canonical residual
refinement and the same calibration supplied by N3. The nominal data
are the actual S5 data of this packet, including its original common
ideals and branch tag. No normalized child is chosen by this record.

The two explicit window errors remain available to the later mass
ledger. The raw scale error is computed from the actual scale product.
Its small bound is proved separately after the fixed annulus threshold.

Paper: Section 4.8, lines 2883--2946.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} {input : ProfileInput call}

/-- The output of N4 on the same family of N3 calibrations. The source
conditions retain the original finite row image and complete mask;
the support and full-joint budgets are conclusions, not task inputs. -/
structure OriginalCapacityCertificate
    (seed : OrdinarySeed packet) (support : seed.ordinary.PassiveSupport input)
    (calibrations : (seed.refinement input support).Calibrations) where
  geometry : ∀ side a rectangle,
    SideGeometryData packet.R side
      ((seed.refinement input support).source side a rectangle)
      (calibrations.side side a rectangle)
  nominal : ∀ side a rectangle,
    (geometry side a rectangle).nominal = packet.nominal side
  pattern : ∀ side a rectangle (h : packet.R.live),
    actualNonunitPattern (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val) =
        (geometry side a rectangle).pattern
  conditions : ∀ side a rectangle,
    (calibrations.side side a rectangle).SourceConditions
  rowError : ∀ side a rectangle,
    (geometry side a rectangle).lengths.scales.rowError = 12 * p.loss
  supportError : ∀ side a rectangle,
    (geometry side a rectangle).lengths.scales.supportError = 4 * p.loss
  rawScaleError : ∀ side a rectangle,
    (geometry side a rectangle).lengths.rawScaleError =
      let s := (seed.refinement input support).source side a rectangle
      max p.loss (Real.logb s.base (s.scale₁ * s.scale₂ * s.base ^ s.beforeLength) -
        (packet.nominal side).skeleton.rawDegree)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
