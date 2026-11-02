import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DependentNormalizedFamily

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The exact refined leaves form one dependent normalized family

Each label contains one original live leaf, its two passive labels and
its two comparison bits. The original two kernels and outer coefficient
are read once from that label. All capacities are the specific inputs
constructed from the individual length and profile tasks.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep Blueprint

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {input : ProfileInput call}

namespace Blueprint.RefinementData

variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}
variable (R : RefinementData O input) (C : R.Calibrations) (G : C.Capacities)

def normalizedFamily : ActualNormalizedPairFamily (Arithmetic.data c)
    (Arithmetic.embedding c) EngineParameter R.Label
    c.family.omega (targetCharacter K c) call.base where
  LeftRow _ := O.rows.live
  RightRow _ := O.rows.live
  leftSlots _ := O.residualSlotCount false
  rightSlots _ := O.residualSlotCount true
  leftSource := R.leftSource
  rightSource := R.rightSource
  leftCalibration b := (C.side false b.1 b.2.2.1).calibration
  rightCalibration b := (C.side true b.2.1 b.2.2.2).calibration
  leftCapacity b := G.side false b.1 b.2.2.1
  rightCapacity b := G.side true b.2.1 b.2.2.2
  left_base b := R.base_eq false b.1 b.2.2.1
  right_base b := R.base_eq true b.2.1 b.2.2.2
  leftNormalizer := R.leftNormalizer
  rightNormalizer := R.rightNormalizer

def sourceBudget : ℝ :=
  ∑ b : R.Label, R.outer b *
    ∫ z : ℝ × ℝ, R.sourcePair b (WithLp.toLp 2 z) ∂packet.leaf.measure

theorem ordinaryCost_le_sourceBudget
    (pointwise : ∀ z : ℝ × ℝ,
      packet.leaf.weight * packet.leaf.ordinaryIntegrand z /
        call.base ^ (call.node.parameters.m + call.node.parameters.q) ≤
      ∑ b : R.Label, R.outer b * R.sourcePair b (WithLp.toLp 2 z)) :
    packet.leaf.ordinaryCost /
      call.base ^ (call.node.parameters.m + call.node.parameters.q) ≤ R.sourceBudget := by
  have hi (b : R.Label) : Integrable
      (fun z : ℝ × ℝ => R.outer b * R.sourcePair b (WithLp.toLp 2 z))
      packet.leaf.measure :=
    ((R.normalizedFamily C G).sourcePair_nested_integrable
      packet.leaf.firstKernel packet.leaf.secondKernel
      (call.node.parameters.m + call.node.parameters.q) b).const_mul (R.outer b)
  calc
    _ = ∫ z : ℝ × ℝ, packet.leaf.weight * packet.leaf.ordinaryIntegrand z /
        call.base ^ (call.node.parameters.m + call.node.parameters.q)
          ∂packet.leaf.measure := by
      rw [integral_div, integral_const_mul]
      rfl
    _ ≤ ∫ z : ℝ × ℝ,
        ∑ b : R.Label, R.outer b * R.sourcePair b (WithLp.toLp 2 z)
          ∂packet.leaf.measure :=
      integral_mono
        ((packet.leaf.ordinaryIntegrand_integrable.const_mul packet.leaf.weight).div_const _)
        (integrable_finsetSum Finset.univ (fun b _ => hi b)) pointwise
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun b _ => hi b)]
      simp only [sourceBudget, integral_const_mul]

end Blueprint.RefinementData

namespace Assembly

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable {geometry : GeometryFamily second}
variable (raw : RawFamily geometry)
variable (O : ∀ j : Fin raw.count, OrdinaryData (raw.packet j))
variable (R : ∀ j, RefinementData (O j) input)
variable (C : ∀ j, (R j).Calibrations) (G : ∀ j, (C j).Capacities)

def refinedNormalizedData : NormalizedData call where
  Label := Σ j : Fin raw.count, (R j).Label
  finite := inferInstance
  family := ActualNormalizedPairFamily.sigmaCombine
    (fun j => (R j).normalizedFamily (C j) (G j))
  firstKernel b := (raw.packet b.1).leaf.firstKernel
  secondKernel b := (raw.packet b.1).leaf.secondKernel
  outer b := (R b.1).outer b.2
  outer_nonneg b := (R b.1).outer_nonneg b.2

theorem refinedNormalizedData_sourceBudget :
    (refinedNormalizedData raw O R C G).sourceBudget = ∑ j, (R j).sourceBudget := by
  change (∑ b : (Σ j : Fin raw.count, (R j).Label), (R b.1).outer b.2 *
    ∫ z : ℝ × ℝ, (R b.1).sourcePair b.2 (WithLp.toLp 2 z)
      ∂(raw.packet b.1).leaf.measure) = _
  rw [Fintype.sum_sigma]
  rfl

theorem ordinaryBudget_le_refinedSourceBudget
    (pointwise : ∀ (j : Fin raw.count) (z : ℝ × ℝ),
      (raw.packet j).leaf.weight * (raw.packet j).leaf.ordinaryIntegrand z /
        call.base ^ (call.node.parameters.m + call.node.parameters.q) ≤
      ∑ b : (R j).Label, (R j).outer b * (R j).sourcePair b (WithLp.toLp 2 z)) :
    raw.normalizedOrdinary ≤ (refinedNormalizedData raw O R C G).sourceBudget := by
  change (∑ j, (raw.packet j).leaf.ordinaryCost) /
    call.base ^ (call.node.parameters.m + call.node.parameters.q) ≤ _
  rw [Finset.sum_div, refinedNormalizedData_sourceBudget]
  exact Finset.sum_le_sum fun j _ =>
    (R j).ordinaryCost_le_sourceBudget (C j) (G j) (pointwise j)

end Assembly
end HeckeSkeleton.Moments.EngineStepV2

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RefinementData.normalizedFamily
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.refinedNormalizedData
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.ordinaryBudget_le_refinedSourceBudget
