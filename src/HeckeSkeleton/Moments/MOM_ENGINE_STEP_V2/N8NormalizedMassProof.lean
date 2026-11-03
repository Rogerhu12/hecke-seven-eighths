import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedArithmeticReduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceOuterMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N8b: the same normalized family is bounded by the same source index

The first Cauchy scalar and its one pool allowance complete the original
arithmetic ledger. Both independent Mobius divisors, both common
radicals and every unchanged allocation label remain in indexWeight.
The actual mesh and all fixed source losses are paid before applying
the exact sigma reindexing of the normalized family.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Normalized

open EngineStep EngineInduction.Source
open NumberField HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]

theorem normalizedMassTask (c : TargetContext K) (p : SourceParameters c) :
    NormalizedMassTask c p := by
  intro frame
  obtain ⟨baseCost, hbase⟩ := arithmeticReduction c p frame
  let cost : UniformCost := {
    baseCost with
    coefficient := baseCost.coefficient * N8Source.outerConstant c p
    coefficient_nonneg := mul_nonneg baseCost.coefficient_nonneg
      (N8Source.outerConstant_nonneg c p)
    threshold := max baseCost.threshold (N8Source.normThreshold c frame)
    threshold_one_le := baseCost.threshold_one_le.trans (le_max_left _ _) }
  refine ⟨cost, ?_⟩
  intro call input hframe ready trace htrace geometry hgeometry raw hraw choices packets
  have hbaseReady : baseCost.Ready call input := {
    orders := ready.orders
    large := (le_max_left _ _).trans ready.large }
  have hlarge : N8Source.normThreshold c call.frame ≤ call.base := by
    rw [hframe]
    exact (le_max_right _ _).trans ready.large
  have hbaseValue : 0 ≤ baseCost.value input.amplitude call.request.height :=
    baseCost.value_nonneg (zero_le_one.trans input.amplitude_one_le)
      call.request.height_nonneg
  have hvalue : 0 ≤ cost.value input.amplitude call.request.height :=
    cost.value_nonneg (zero_le_one.trans input.amplitude_one_le)
      call.request.height_nonneg
  have hvalue_eq : cost.value input.amplitude call.request.height =
      baseCost.value input.amplitude call.request.height * N8Source.outerConstant c p := by
    dsimp only [UniformCost.value, cost]
    ring
  have hlabel (j : Fin raw.count) :
      ((packets j).seed.refinement input (packets j).support).arithmeticMass
          (packets j).calibrations (packets j).capacities ≤
        (cost.value input.amplitude call.request.height *
          call.base ^ (recipeInductionEdgeLoss c / 2 - 2 * p.loss)) * raw.indexWeight j := by
    have hpacket := RawFamily.packet_realizes trace htrace hgeometry raw hraw j
    have hm := hbase call input hframe hbaseReady (raw.packet j) hpacket choices (packets j)
    have ho := RawFamily.outerArithmeticWeight_le trace htrace input hlarge hgeometry raw hraw j
    have hscaled := mul_le_mul_of_nonneg_left ho
      (mul_nonneg hbaseValue (Real.rpow_nonneg call.base_pos.le
        (31 * p.loss + call.node.parameters.κ * (momentMesh K c.family).val)))
    have hpower := Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
      (call.normalized_arithmetic_exponent p)
    calc
      _ ≤ (baseCost.value input.amplitude call.request.height *
          call.base ^ (31 * p.loss + call.node.parameters.κ * (momentMesh K c.family).val)) *
          (N8Source.outerConstant c p *
            call.base ^ (2 * N8Source.columnExponent c * p.tilt) * raw.indexWeight j) :=
        hm.trans hscaled
      _ = (cost.value input.amplitude call.request.height *
          call.base ^ (31 * p.loss + 2 * N8Source.columnExponent c * p.tilt +
            call.node.parameters.κ * (momentMesh K c.family).val)) * raw.indexWeight j := by
        rw [hvalue_eq,
          show 31 * p.loss + 2 * N8Source.columnExponent c * p.tilt +
              call.node.parameters.κ * (momentMesh K c.family).val =
            (31 * p.loss + call.node.parameters.κ * (momentMesh K c.family).val) +
              2 * N8Source.columnExponent c * p.tilt by ring,
          Real.rpow_add call.base_pos
            (31 * p.loss + call.node.parameters.κ * (momentMesh K c.family).val)
            (2 * N8Source.columnExponent c * p.tilt)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower hvalue) (raw.indexWeight_nonneg j)
  exact Assembly.refinedNormalizedData_mass_le_indexMass raw
    (fun j => (packets j).seed.ordinary)
    (fun j => (packets j).seed.refinement input (packets j).support)
    (fun j => (packets j).calibrations) (fun j => (packets j).capacities)
    (cost.value input.amplitude call.request.height *
      call.base ^ (recipeInductionEdgeLoss c / 2 - 2 * p.loss)) hlabel

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Normalized

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Normalized.normalizedMassTask
