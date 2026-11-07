module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedMassContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedRows
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedFibres
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedLabels

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The same whole-slot capacity children pay the original atom costs

Both canonical row maxima, both passive scalar maxima and both original
orbit fibres are bounded by the proved original-atom estimates. The N6
prime bound is exactly one on the actual removal set. This file keeps
the original normalizers, the independent inner divisor and the literal
active family, before inserting the original numerical width ledger.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} {input : ProfileInput call}
variable {choices : FullKappaChoices c p.loss}

namespace CanonicalMassPacket

variable (P : CanonicalMassPacket packet input choices)

def localFamily :=
  (P.seed.refinement input P.support).normalizedFamily P.calibrations P.capacities

def originalAtomCost (_P : CanonicalMassPacket packet input choices) : ℝ :=
  (packet.orbitalRowCost * (input.frozenAtomBudget ^ c.geometry.slots /
    (Ideal.absNorm packet.allocation.1.val : ℝ))) *
      input.frozenAtomBudget ^ c.geometry.slots * (Arithmetic.unitSubgroup c).index

theorem originalAtomCost_nonneg : 0 ≤ P.originalAtomCost := by
  unfold originalAtomCost
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg packet.orbitalRowCost_nonneg
        (div_nonneg (pow_nonneg (zero_le_one.trans input.frozenAtomBudget_one) _)
          (Nat.cast_nonneg _)))
      (pow_nonneg (zero_le_one.trans input.frozenAtomBudget_one) _))
    (Nat.cast_nonneg _)

def originalPairBound (budget : ℝ) : ℝ :=
  ‖P.seed.occurrences.normalizer P.seed.phases false‖ *
    ‖P.seed.occurrences.normalizer P.seed.phases true‖ * P.originalAtomCost *
      call.base ^ (budget - (call.node.parameters.m + call.node.parameters.q))

theorem originalPairBound_nonneg (budget : ℝ) : 0 ≤ P.originalPairBound budget :=
  mul_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) P.originalAtomCost_nonneg)
    (Real.rpow_nonneg call.base_pos.le _)

theorem keptSlotCount_le (side : Bool) (a : P.support.labels side) (rectangle : Bool) :
    ((P.seed.refinement input P.support).source side a rectangle).allocation.keep.card ≤
      c.geometry.slots :=
  (((P.seed.refinement input P.support).source side a rectangle).allocation.keep_card_le).trans
    (P.seed.residualSlotCount_le input P.support side)

/-- A primitive budget inequality is the only ledger still left open
here. All arithmetic costs refer to the same canonical source and are
proved from its original atoms above, rather than assumed as fields. -/
theorem normalized_weight_le_original (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (budget : ℝ)
    (hbudget : ∀ side a rectangle,
      (P.calibrations.side side a rectangle).calibration.parameters.m +
        (P.calibrations.side side a rectangle).calibration.parameters.q +
        (P.capacities.side side a rectangle).exponent ≤ budget)
    (b : P.localFamily.active Finset.univ) :
    P.localFamily.weight Finset.univ
      (call.node.parameters.m + call.node.parameters.q) b ≤ P.originalPairBound budget := by
  have hrow (side : Bool) (a : P.support.labels side) (rectangle : Bool) :
      (P.calibrations.side side a rectangle).calibration.rowBound ≤
        packet.orbitalRowCost * (input.frozenAtomBudget ^ c.geometry.slots /
          (Ideal.absNorm packet.allocation.1.val : ℝ)) := by
    rw [(P.calibrations.side side a rectangle).row_cost]
    exact P.seed.canonicalSource_rowCost_realized input P.support hpacket horders
      side a rectangle
  have hscalar (side : Bool) (a : P.support.labels side) (rectangle : Bool) :
      (P.calibrations.side side a rectangle).calibration.scalarBound ≤
        input.frozenAtomBudget ^ c.geometry.slots := by
    rw [(P.calibrations.side side a rectangle).scalar_cost]
    exact P.seed.canonicalSource_scalarCost_uniform input P.support P.support_actual horders
      side a rectangle
  have hfiber (side : Bool) (a : P.support.labels side) (rectangle : Bool) :
      ((P.calibrations.side side a rectangle).calibration.fiberBound : ℝ) ≤
        (Arithmetic.unitSubgroup c).index := by
    rw [(P.calibrations.side side a rectangle).fiber_cost]
    exact_mod_cast P.seed.canonicalSource_fibreCost_realized input P.support hpacket
      side a rectangle
  have hprime (side : Bool) (a : P.support.labels side) (rectangle : Bool) :
      ∀ i, (P.capacities.side side a rectangle).primeBound i ≤ 1 := by
    intro i
    rw [P.primeBound side a rectangle i]
  have h := normalizedCapacityPairWeight_le_costs
    (P.localFamily.leftChild Finset.univ b) (P.localFamily.rightChild Finset.univ b)
    (P.seed.occurrences.normalizer P.seed.phases false)
    (P.seed.occurrences.normalizer P.seed.phases true)
    call.base (call.node.parameters.m + call.node.parameters.q)
    (packet.orbitalRowCost * (input.frozenAtomBudget ^ c.geometry.slots /
      (Ideal.absNorm packet.allocation.1.val : ℝ)))
    (input.frozenAtomBudget ^ c.geometry.slots) (Arithmetic.unitSubgroup c).index
    1 budget c.geometry.slots call.domain.scale.le rfl rfl
    (hrow false b.val.1 b.val.2.2.1) (hrow true b.val.2.1 b.val.2.2.2)
    (hscalar false b.val.1 b.val.2.2.1) (hscalar true b.val.2.1 b.val.2.2.2)
    (hfiber false b.val.1 b.val.2.2.1) (hfiber true b.val.2.1 b.val.2.2.2)
    (hprime false b.val.1 b.val.2.2.1) (hprime true b.val.2.1 b.val.2.2.2)
    le_rfl (P.keptSlotCount_le false b.val.1 b.val.2.2.1)
    (P.keptSlotCount_le true b.val.2.1 b.val.2.2.2)
    (hbudget false b.val.1 b.val.2.2.1) (hbudget true b.val.2.1 b.val.2.2.2)
  change normalizedCapacityPairWeight
    (P.localFamily.leftChild Finset.univ b) (P.localFamily.rightChild Finset.univ b)
    (P.seed.occurrences.normalizer P.seed.phases false)
    (P.seed.occurrences.normalizer P.seed.phases true)
    call.base (call.node.parameters.m + call.node.parameters.q) ≤ _
  simpa only [originalPairBound, originalAtomCost, one_pow, mul_one] using h

/-- Passing to the genuine active subtype cannot increase the original
positive outer sum. No active label is duplicated or replaced. -/
theorem active_outer_sum_le :
    (∑ b : P.localFamily.active Finset.univ,
      (P.seed.refinement input P.support).outer b.val) ≤
        4 * packet.leaf.weight * (P.support.labels false).card *
          (P.support.labels true).card := by
  calc
    _ = ∑ b ∈ P.localFamily.active Finset.univ,
        (P.seed.refinement input P.support).outer b := Finset.sum_coe_sort _ _
    _ ≤ ∑ b : (P.seed.refinement input P.support).Label,
        (P.seed.refinement input P.support).outer b :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun b _ _ => (P.seed.refinement input P.support).outer_nonneg b)
    _ = _ := P.support.sum_outer

theorem arithmeticMass_le_original (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (budget : ℝ)
    (hbudget : ∀ side a rectangle,
      (P.calibrations.side side a rectangle).calibration.parameters.m +
        (P.calibrations.side side a rectangle).calibration.parameters.q +
        (P.capacities.side side a rectangle).exponent ≤ budget) :
    (P.seed.refinement input P.support).arithmeticMass P.calibrations P.capacities ≤
      (4 * packet.leaf.weight * (P.support.labels false).card *
        (P.support.labels true).card) * P.originalPairBound budget := by
  change (∑ b : P.localFamily.active Finset.univ,
    (P.seed.refinement input P.support).outer b.val *
      P.localFamily.weight Finset.univ
        (call.node.parameters.m + call.node.parameters.q) b) ≤ _
  calc
    _ ≤ ∑ b : P.localFamily.active Finset.univ,
        (P.seed.refinement input P.support).outer b.val * P.originalPairBound budget :=
      Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
        (P.normalized_weight_le_original hpacket horders budget hbudget b)
        ((P.seed.refinement input P.support).outer_nonneg b.val)
    _ = (∑ b : P.localFamily.active Finset.univ,
        (P.seed.refinement input P.support).outer b.val) * P.originalPairBound budget := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right P.active_outer_sum_le
      (P.originalPairBound_nonneg budget)

end CanonicalMassPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalMassPacket.normalized_weight_le_original
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalMassPacket.active_outer_sum_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalMassPacket.arithmeticMass_le_original
