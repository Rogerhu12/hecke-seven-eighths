import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationOrigin
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCanonicalSupport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fixed raw parameters from the original nominal windows

The row and support exponents use the stated original window errors.
The sixth-root length is the actual second common root. Plain lengths
are the logarithms of this allocation's exact quotient scales; the
slot length is the sum on its actual keep. No parameter is enlarged
after a calibration or a capacity result has been selected.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationParameters

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (packet : RawLeafPacket call p)

def rootLength : ℝ :=
  idealLogLength call.base
    (secondSixthRootIdeal packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity).val

theorem rootLength_nonneg : 0 ≤ rootLength packet :=
  idealLogLength_nonneg call.base call.domain.scale _
    (secondSixthRootIdeal packet.R.primes packet.R.leftMultiplicity
      packet.R.rightMultiplicity).property.1

def rowExponent (side : Bool) : ℝ :=
  (packet.nominal side).skeleton.nominalRow + 12 * p.loss

def supportExponent (side : Bool) : ℝ :=
  (packet.nominal side).skeleton.nominalSupport + 4 * p.loss + rootLength packet

theorem supportExponent_nonneg (hpacket : packet.Realizes) (side : Bool) :
    0 ≤ supportExponent packet side :=
  add_nonneg (packet.nominalSupport_error_nonneg hpacket side) (rootLength_nonneg packet)

variable {packet}
variable (seed : OrdinarySeed packet) (input : ProfileInput call)
variable (support : seed.ordinary.PassiveSupport input)
variable (side : Bool) (a : support.labels side) (rectangle : Bool)

local notation "s" => seed.canonicalSource input support side a rectangle

def parameters : RealParameters :=
  { call.node.parameters with
    m := rowExponent packet side
    q := supportExponent packet side
    n₁ := Real.log (s.scale₁ / idealNorm K (s.allocation.plainDivisor 0)) / Real.log s.base
    n₂ := Real.log (s.scale₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0))) /
      Real.log s.base
    z := ∑ i, s.childLength i }

private theorem rpow_log_ratio (Z scale : ℝ) (hZ : 1 < Z) (hscale : 0 < scale) :
    Z ^ (Real.log scale / Real.log Z) = scale := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
  have he : Real.log Z * (Real.log scale / Real.log Z) = Real.log scale := by
    rw [mul_comm, div_mul_cancel₀ _ (Real.log_pos hZ).ne']
  rw [he, Real.exp_log hscale]

theorem left_scale : s.base ^ (parameters seed input support side a rectangle).n₁ =
    s.scale₁ / idealNorm K (s.allocation.plainDivisor 0) :=
  rpow_log_ratio s.base _ s.base_gt_one
    (div_pos (seed.occurrences.plainScale_pos side rectangle false) (idealNorm_pos K _))

theorem right_scale : s.base ^ (parameters seed input support side a rectangle).n₂ =
    s.scale₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0)) :=
  rpow_log_ratio s.base _ s.base_gt_one
    (div_pos (seed.occurrences.plainScale_pos side rectangle true) (idealNorm_pos K _))

theorem slot_sum : (parameters seed input support side a rectangle).z =
    ∑ i, s.childLength i := rfl

theorem kappa : (parameters seed input support side a rectangle).κ = call.node.parameters.κ := rfl

theorem cutoff (hpacket : packet.Realizes) (h : seed.ordinary.rows.live) :
    (Arithmetic.data c).exteriorNorm (s.originalIdeal h) ≤ s.normFactor h *
      s.base ^ ((parameters seed input support side a rectangle).m +
        (parameters seed input support side a rectangle).q) :=
  seed.canonicalSource_cutoff input support hpacket side a rectangle
    (supportExponent packet side) (supportExponent_nonneg packet hpacket side) h

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationParameters

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationParameters.left_scale
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationParameters.cutoff
