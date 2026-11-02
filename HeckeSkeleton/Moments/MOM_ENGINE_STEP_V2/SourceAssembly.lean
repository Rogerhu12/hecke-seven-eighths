import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstSourceContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstCauchyContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PoolContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.GeometryContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Assembly of S1--S6 from explicit task proofs

This module imports contracts only. It selects the two input demands
before the moving call, follows one original source chain, and divides
its actual inequality by the unchanged original parent width. It has
no proof holes and does not import any admitted task theorem.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

structure SourceCertificate (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c) where
  demand : UniformDemand
  produce : ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
    demand.Ready call input → call.Active →
    ∃ trace : SourceTrace call p, ∃ geometry : GeometryFamily trace.second,
      ∃ raw : RawFamily geometry,
        trace.Realizes ∧ geometry.Realizes ∧ raw.Realizes ∧
          call.node.normalizedEnergy call.base 0 ≤
            trace.first.normalizedZero + trace.second.normalizedZero +
              raw.normalizedExceptional +
              (trace.first.normalizedTail + trace.second.normalizedTail) +
              raw.normalizedOrdinary

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open Blueprint NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem sourceCertificate (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c)
    (firstTransform : FirstTransformTask c p)
    (firstAllowance : FirstAllowanceTask c p)
    (amplification : AmplificationTask c p)
    (secondTransform : SecondTransformTask c p)
    (nominalGeometry : NominalGeometryTask c p)
    (finiteLeaves : FiniteLeafTask c p) :
    Nonempty (SourceCertificate c frame p) := by
  obtain ⟨firstDemand, hfirstDemand⟩ := firstAllowance frame
  obtain ⟨poolDemand, hpoolDemand⟩ := amplification frame
  refine ⟨{ demand := firstDemand.join poolDemand, produce := ?_ }⟩
  intro call input hframe ready active
  obtain ⟨F, hF, hfirst⟩ := firstTransform call active
  obtain ⟨family, hfamily, hcauchy, hfirstWindows⟩ :=
    hfirstDemand call input hframe (UniformDemand.ready_left ready) F hF
  obtain ⟨expansion, hexpansion, hpool, hpoolWindows⟩ :=
    hpoolDemand call input hframe (UniformDemand.ready_right ready) F hF family hfamily hfirstWindows
  obtain ⟨second, hsecond, hsecondBound⟩ :=
    secondTransform call F hF family hfamily expansion hexpansion hpoolWindows
  let trace : SourceTrace call p := ⟨F, family, expansion, second⟩
  have htrace : trace.Realizes :=
    ⟨hF, hfamily, hfirstWindows, hexpansion, hpoolWindows, hsecond⟩
  obtain ⟨geometry, hgeometry⟩ := nominalGeometry call trace htrace
  obtain ⟨raw, hraw, hleaves⟩ := finiteLeaves call trace htrace geometry hgeometry
  refine ⟨trace, geometry, raw, htrace, hgeometry, hraw, ?_⟩
  have hstart := hfirst family.normalization
  rw [hcauchy] at hstart
  have htotal : call.node.energy call.base 0 ≤
      F.zero + second.zero + raw.exceptional + (F.tail + second.tail) + raw.ordinary := by
    change second.nonzero ≤ raw.exceptional + raw.ordinary at hleaves
    linarith
  have hnormalized := div_le_div_of_nonneg_right htotal call.parentNormalizer_pos.le
  change call.normalizedScalar (call.node.energy call.base 0) ≤ _
  simpa only [trace, FirstPresentation.normalizedZero, FirstPresentation.normalizedTail,
    SecondFamily.normalizedZero, SecondFamily.normalizedTail,
    RawFamily.normalizedExceptional, RawFamily.normalizedOrdinary,
    Call.normalizedScalar, add_div] using hnormalized

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.sourceCertificate

