module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedBudget
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedOriginalScalars
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonNormalization

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The second common harmonic factor of the original normalized label

The two actual second common scalars, the complete local correlation,
the original inverse radius, and the same capacity width cancel to
one inverse second common radical. The first external scalars are kept
literal for the first Cauchy ledger. The independent inner divisor is
unchanged and retains its full inverse norm.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open CommonSupportMass

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem nominal_second_swap (hpacket : packet.Realizes) :
    (packet.nominal true).ideals.second.val =
      (packet.nominal false).ideals.secondOpposite.val := by
  rw [N4.nominal_second_eq hpacket true, packet.nominal_secondOpposite_eq hpacket false]
  rfl

theorem secondFrozenExterior_nominal (hpacket : packet.Realizes) (side : Bool) :
    (packet.secondFrozenExterior side).val = (packet.nominal side).ideals.second.val := by
  rw [← packet.secondFrozenExterior_val side]
  change N4.secondFrozenIdeal packet side = _
  rw [N4.secondFrozenIdeal_eq, N4.nominal_second_eq hpacket side]

theorem nominal_enlargement_eq (hpacket : packet.Realizes) (side : Bool) :
    (packet.nominal side).enlargement = packet.second.physical.enlargement := by
  simp only [OriginalNominalGeometry.enlargement, OriginalNominalGeometry.shiftedCommon,
    OriginalNominalGeometry.retainedLength, OriginalNominalIdeals.firstFrequency,
    N4.nominal_first_eq hpacket side, packet.nominal_opposite_eq hpacket side,
    packet.nominal_complementary_eq hpacket side, packet.nominal_retained_eq hpacket side,
    N4.nominal_tag_eq hpacket side, PhysicalSource.enlargement,
    PhysicalSource.firstFrequency]
  congr 2
  ring

theorem nominal_retained_rpow (hpacket : packet.Realizes) (side : Bool) :
    call.base ^ (packet.nominal side).skeleton.Krow =
      packet.second.physical.first.retainedScale := by
  change call.base ^ (Real.log (packet.nominal side).retainedScale /
    Real.log call.base) = _
  rw [Real.rpow_def_of_pos call.base_pos]
  have hlog : Real.log call.base *
      (Real.log (packet.nominal side).retainedScale / Real.log call.base) =
        Real.log (packet.nominal side).retainedScale := by
    field_simp [(Real.log_pos call.domain.scale).ne']
  rw [hlog]
  rw [Real.exp_log (packet.nominal side).retainedScale_pos,
    packet.nominal_retained_eq hpacket side]

theorem correlationCost_eq_rpow (hpacket : packet.Realizes) :
    packet.correlationCost = call.base ^
      ((packet.nominal false).skeleton.g₂ - (packet.nominal false).skeleton.t₂) := by
  unfold correlationCost
  change _ = call.base ^
    (idealLogLength call.base (gcd (packet.nominal false).ideals.second.val
      (packet.nominal false).ideals.secondOpposite.val) -
        idealLogLength call.base (packet.nominal false).ideals.unitPart.val)
  rw [Real.rpow_sub call.base_pos,
    rpow_idealLogLength call.base call.domain.scale _
      (gcd_ne_zero_of_left (nonZeroDivisors.coe_ne_zero
        (packet.nominal false).ideals.second)),
    rpow_idealLogLength call.base call.domain.scale _
      (nonZeroDivisors.coe_ne_zero (packet.nominal false).ideals.unitPart),
    N4.nominal_second_eq hpacket false, packet.nominal_secondOpposite_eq hpacket false]
  rfl

theorem orbitalRowCost_le_nominal (hpacket : packet.Realizes) :
    packet.orbitalRowCost ≤ orbitalFieldFactor K * call.base ^
      ((packet.nominal false).skeleton.Krow + (packet.nominal false).skeleton.g +
        (packet.nominal false).skeleton.g₂ - (packet.nominal false).skeleton.t₂) := by
  apply (packet.orbitalRowCost_le_retained_scale hpacket).trans_eq
  rw [← packet.nominal_retained_rpow hpacket false,
    ← packet.nominal_enlargement_eq hpacket false,
    packet.correlationCost_eq_rpow hpacket]
  change orbitalFieldFactor K * call.base ^ (packet.nominal false).skeleton.Krow *
    call.base ^ (packet.nominal false).skeleton.g *
      call.base ^ ((packet.nominal false).skeleton.g₂ -
        (packet.nominal false).skeleton.t₂) = _
  rw [mul_assoc, ← Real.rpow_add call.base_pos, mul_assoc,
    ← Real.rpow_add call.base_pos]
  congr 2
  ring

/-- The part of the first-scale ledger left after the second radius,
second common ideals and row radicals have canceled. -/
def secondLedgerExponent : ℝ :=
  2 * ((packet.nominal false).skeleton.A - (packet.nominal false).skeleton.c -
      (packet.nominal false).skeleton.w) +
    ((packet.nominal false).skeleton.q + (packet.nominal false).skeleton.R +
      (packet.nominal false).skeleton.E) + (packet.nominal false).skeleton.wo +
    (packet.nominal false).skeleton.w + (packet.nominal false).boundary +
    (packet.nominal false).tag.poolLength (recipeInductionSigma c) -
    (call.node.parameters.m + call.node.parameters.q) +
      20 * p.loss + packet.annulusLog / 6 +
        call.node.parameters.κ * (momentMesh K c.family).val

theorem second_exponent_identity :
    (packet.nominal false).skeleton.Krow + (packet.nominal false).skeleton.g +
      (packet.nominal false).skeleton.g₂ - (packet.nominal false).skeleton.t₂ -
      (packet.nominal false).halfSecond +
      (packet.nominalBudget false - (call.node.parameters.m + call.node.parameters.q)) =
        packet.secondLedgerExponent - (packet.nominal false).secondRadical := by
  unfold secondLedgerExponent nominalBudget nominalCore
  unfold NominalChildGeometry.nominalWidth NominalChildGeometry.nominalRow
    NominalChildGeometry.nominalSupport
  ring

theorem secondRadical_rpow (hpacket : packet.Realizes) :
    call.base ^ (packet.nominal false).secondRadical =
      (Ideal.absNorm (commonRadical packet.key.1.val.1 packet.key.1.val.2) : ℝ) := by
  unfold OriginalNominalGeometry.secondRadical
  rw [rpow_idealLogLength call.base call.domain.scale _ (commonRadical_ne_zero _ _),
    N4.nominal_second_eq hpacket false, packet.nominal_secondOpposite_eq hpacket false]
  rfl

def firstExternalPair : ℝ :=
  ‖packet.firstExternalScalar false‖ * ‖packet.firstExternalScalar true‖

theorem firstExternalPair_nonneg : 0 ≤ packet.firstExternalPair :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

end RawLeafPacket

namespace OriginalOccurrenceData

variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}
variable (D : OriginalOccurrenceData O)

theorem secondCommonScalar_pair_le (input : ProfileInput call) (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (phases : OriginalPhaseData packet) :
    ‖D.secondCommonScalar phases false‖ * ‖D.secondCommonScalar phases true‖ ≤
      input.frozenAtomBudget ^ c.geometry.slots /
        call.base ^ (packet.nominal false).halfSecond := by
  have hB : 0 ≤ input.frozenAtomBudget ^ c.geometry.slots :=
    pow_nonneg (zero_le_one.trans input.frozenAtomBudget_one) _
  have hp := mul_le_mul
    (D.secondCommonScalar_norm_le input hpacket horders phases false)
    (D.secondCommonScalar_norm_le input hpacket horders phases true)
    (norm_nonneg _) (Real.sqrt_nonneg _)
  apply hp.trans_eq
  rw [packet.secondFrozenExterior_nominal hpacket false,
    packet.secondFrozenExterior_nominal hpacket true, packet.nominal_second_swap hpacket]
  rw [Real.sqrt_div hB, Real.sqrt_div hB]
  have he :
      Real.sqrt (input.frozenAtomBudget ^ c.geometry.slots) *
        Real.sqrt (input.frozenAtomBudget ^ c.geometry.slots) =
      input.frozenAtomBudget ^ c.geometry.slots := Real.mul_self_sqrt hB
  have hcentral := second_central_norm_eq_rpow call.base call.domain.scale
    (packet.nominal false).ideals.second.val (packet.nominal false).ideals.secondOpposite.val
    (nonZeroDivisors.coe_ne_zero _) (nonZeroDivisors.coe_ne_zero _)
  change call.base ^ (packet.nominal false).halfSecond = _ at hcentral
  rw [hcentral]
  calc
    _ = (Real.sqrt (input.frozenAtomBudget ^ c.geometry.slots) *
          Real.sqrt (input.frozenAtomBudget ^ c.geometry.slots)) /
        (Real.sqrt (Ideal.absNorm (packet.nominal false).ideals.second.val : ℝ) *
          Real.sqrt (Ideal.absNorm (packet.nominal false).ideals.secondOpposite.val : ℝ)) :=
      by ring
    _ = _ := by rw [he]

/-- The original second scalars and row cost pay precisely the actual
second common radical, with no second pool or changed label. -/
theorem secondCommonScalar_row_budget_le (input : ProfileInput call)
    (hpacket : packet.Realizes) (horders : (0, 0) ∈ input.orders)
    (phases : OriginalPhaseData packet) :
    (‖D.secondCommonScalar phases false‖ * ‖D.secondCommonScalar phases true‖) *
        packet.orbitalRowCost *
        call.base ^ (packet.nominalBudget false -
          (call.node.parameters.m + call.node.parameters.q)) ≤
      (input.frozenAtomBudget ^ c.geometry.slots * orbitalFieldFactor K) *
        call.base ^ packet.secondLedgerExponent /
          (Ideal.absNorm (commonRadical packet.key.1.val.1 packet.key.1.val.2) : ℝ) := by
  have hB : 0 ≤ input.frozenAtomBudget ^ c.geometry.slots :=
    pow_nonneg (zero_le_one.trans input.frozenAtomBudget_one) _
  have hb := mul_le_mul
    (D.secondCommonScalar_pair_le input hpacket horders phases)
    (packet.orbitalRowCost_le_nominal hpacket) packet.orbitalRowCost_nonneg
    (div_nonneg hB (Real.rpow_nonneg call.base_pos.le _))
  apply (mul_le_mul_of_nonneg_right hb
    (Real.rpow_nonneg call.base_pos.le _)).trans_eq
  calc
    _ = (input.frozenAtomBudget ^ c.geometry.slots * orbitalFieldFactor K) *
      ((call.base ^ ((packet.nominal false).skeleton.Krow +
          (packet.nominal false).skeleton.g + (packet.nominal false).skeleton.g₂ -
          (packet.nominal false).skeleton.t₂) /
        call.base ^ (packet.nominal false).halfSecond) *
      call.base ^ (packet.nominalBudget false -
        (call.node.parameters.m + call.node.parameters.q))) := by ring
    _ = (input.frozenAtomBudget ^ c.geometry.slots * orbitalFieldFactor K) *
        call.base ^ (packet.secondLedgerExponent - (packet.nominal false).secondRadical) := by
      rw [← Real.rpow_sub call.base_pos, ← Real.rpow_add call.base_pos,
        packet.second_exponent_identity]
    _ = _ := by
      rw [Real.rpow_sub call.base_pos, packet.secondRadical_rpow hpacket]
      ring

end OriginalOccurrenceData

namespace CanonicalMassPacket

variable {packet : RawLeafPacket call p} {input : ProfileInput call}
variable {choices : FullKappaChoices c p.loss}
variable (P : CanonicalMassPacket packet input choices)

/-- A pointwise intermediate ledger; its first pair is the original
first scalar pair, not an independent normalization chosen for a bound. -/
def secondHarmonicBound (_P : CanonicalMassPacket packet input choices) : ℝ :=
  packet.firstExternalPair *
    (input.frozenAtomBudget ^ c.geometry.slots) ^ 3 *
    (Arithmetic.unitSubgroup c).index * orbitalFieldFactor K *
    call.base ^ packet.secondLedgerExponent /
      (Ideal.absNorm (commonRadical packet.key.1.val.1 packet.key.1.val.2) : ℝ) /
      (Ideal.absNorm packet.allocation.1.val : ℝ)

theorem originalPairBound_le_secondHarmonic (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) :
    P.originalPairBound (packet.nominalBudget false) ≤ P.secondHarmonicBound := by
  have hB : 0 ≤ input.frozenAtomBudget ^ c.geometry.slots :=
    pow_nonneg (zero_le_one.trans input.frozenAtomBudget_one) _
  have htail : 0 ≤ (input.frozenAtomBudget ^ c.geometry.slots) ^ 2 *
      (Arithmetic.unitSubgroup c).index / (Ideal.absNorm packet.allocation.1.val : ℝ) := by
    positivity
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (P.seed.occurrences.secondCommonScalar_row_budget_le input hpacket horders P.seed.phases)
      packet.firstExternalPair_nonneg) htail
  convert h using 1
  · unfold originalPairBound originalAtomCost RawLeafPacket.firstExternalPair
      OriginalOccurrenceData.normalizer
    simp only [norm_mul]
    ring
  · unfold secondHarmonicBound
    ring

theorem arithmeticMass_le_secondHarmonic (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (frame : SourceFrame) (hframe : call.frame = frame)
    (ready : (N4.annulusDemand p frame).Ready call input) :
    (P.seed.refinement input P.support).arithmeticMass P.calibrations P.capacities ≤
      (4 * packet.leaf.weight * (P.support.labels false).card *
        (P.support.labels true).card) * P.secondHarmonicBound := by
  apply (P.arithmeticMass_le_nominal hpacket horders frame hframe ready).trans
  apply mul_le_mul_of_nonneg_left (P.originalPairBound_le_secondHarmonic hpacket horders)
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) packet.leaf.weight_nonneg) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

end CanonicalMassPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.orbitalRowCost_le_nominal
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalOccurrenceData.secondCommonScalar_row_budget_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalMassPacket.arithmeticMass_le_secondHarmonic
