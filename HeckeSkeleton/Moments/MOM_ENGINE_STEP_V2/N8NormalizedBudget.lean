import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedCapacityMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4UniformCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonIndexSwap

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual sixth-root and whole-slot arithmetic ledger

The additional sixth-root support occurs once in the calibrated width
and once with the opposite sign in the capacity allowance. The same N6
capacity constructor cancels these two occurrences. All remaining
window errors are the original N4 values; the source error becomes the
fixed p.loss after its frame demand. The exact original mesh is retained.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

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

theorem nominal_opposite_eq (hpacket : packet.Realizes) (side : Bool) :
    (packet.nominal side).ideals.opposite.val = packet.second.physical.first.opposite.val := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).opposite side

theorem nominal_complementary_eq (hpacket : packet.Realizes) (side : Bool) :
    (packet.nominal side).ideals.complementary.val =
      packet.second.physical.first.complementary.val := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).complementary side

theorem nominal_retained_eq (hpacket : packet.Realizes) (side : Bool) :
    (packet.nominal side).retainedScale = packet.second.physical.first.retainedScale := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).retainedScale side

theorem nominal_supportError_eq (hpacket : packet.Realizes) (side : Bool) :
    (packet.nominal side).supportError = 4 * p.loss := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).supportError side

theorem nominal_secondOpposite_eq (hpacket : packet.Realizes) (side : Bool) :
    (packet.nominal side).ideals.secondOpposite.val =
      if side then packet.key.1.val.1 else packet.key.1.val.2 := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).secondOpposite side

def nominalCore (side : Bool) : ℝ :=
  (packet.nominal side).skeleton.nominalWidth + (packet.nominal side).halfSecond -
    (packet.nominal side).secondRadical + (packet.nominal side).skeleton.w +
    (packet.nominal side).boundary +
    (packet.nominal side).tag.poolLength (recipeInductionSigma c)

def annulusLog (_packet : RawLeafPacket call p) : ℝ :=
  (Real.log (max 1 (2 * call.prepared.upper)) +
    Real.log (max 1 (2 * call.prepared.upper))) / Real.log call.base

def nominalBudget (side : Bool) : ℝ :=
  packet.nominalCore side + 20 * p.loss + packet.annulusLog / 6 +
    call.node.parameters.κ * (momentMesh K c.family).val

/-- Swapping the two original second common ideals does not change the
numeric mass ledger. Both unit and nonunit ideals are read from the same
actual row class; all first-transform coordinates remain identical. -/
theorem nominalCore_eq_false (hpacket : packet.Realizes) (side : Bool) :
    packet.nominalCore side = packet.nominalCore false := by
  cases side with
  | false => rfl
  | true =>
    have hlive : Nonempty packet.R.live := by
      rcases hpacket with ⟨trace, geometry, raw, j, _, _, _, rfl⟩
      rcases (raw.active j).2.2.2 with ⟨h, hh⟩
      exact ⟨⟨h, hh⟩⟩
    let h : packet.R.live := Classical.choice hlive
    have hunit := (packet.realized_unitPart hpacket true h).trans
      (packet.realized_unitPart hpacket false h).symm
    have hnonunit := (packet.realized_nonunitPart hpacket true h).trans
      (packet.realized_nonunitPart hpacket false h).symm
    have hfirst := (N4.nominal_first_eq hpacket true).trans
      (N4.nominal_first_eq hpacket false).symm
    have hopposite := (packet.nominal_opposite_eq hpacket true).trans
      (packet.nominal_opposite_eq hpacket false).symm
    have hcomplementary := (packet.nominal_complementary_eq hpacket true).trans
      (packet.nominal_complementary_eq hpacket false).symm
    have hretained := (packet.nominal_retained_eq hpacket true).trans
      (packet.nominal_retained_eq hpacket false).symm
    have htag := (N4.nominal_tag_eq hpacket true).trans
      (N4.nominal_tag_eq hpacket false).symm
    have hsecond : (packet.nominal true).ideals.second.val =
        (packet.nominal false).ideals.secondOpposite.val := by
      rw [N4.nominal_second_eq hpacket true, packet.nominal_secondOpposite_eq hpacket false]
      rfl
    have hsecondOpposite : (packet.nominal true).ideals.secondOpposite.val =
        (packet.nominal false).ideals.second.val := by
      rw [packet.nominal_secondOpposite_eq hpacket true, N4.nominal_second_eq hpacket false]
      rfl
    simp only [nominalCore, NominalChildGeometry.nominalWidth,
      NominalChildGeometry.nominalRow, NominalChildGeometry.nominalSupport,
      OriginalNominalGeometry.skeleton, OriginalNominalGeometry.halfSecond,
      OriginalNominalGeometry.secondRadical, OriginalNominalGeometry.boundary,
      OriginalNominalGeometry.retainedLength, OriginalNominalGeometry.enlargement,
      OriginalNominalGeometry.shiftedCommon, OriginalNominalIdeals.firstFrequency,
      hfirst, hopposite, hcomplementary, hretained, htag, hsecond, hsecondOpposite,
      hunit, hnonunit]
    rw [gcd_comm (packet.nominal false).ideals.secondOpposite.val,
      commonRadical_comm (packet.nominal false).ideals.secondOpposite.val]
    ring

theorem nominalBudget_eq_false (hpacket : packet.Realizes) (side : Bool) :
    packet.nominalBudget side = packet.nominalBudget false := by
  unfold nominalBudget
  rw [packet.nominalCore_eq_false hpacket side]

end RawLeafPacket

namespace CanonicalMassPacket

variable {packet : RawLeafPacket call p} {input : ProfileInput call}
variable {choices : FullKappaChoices c p.loss}
variable (P : CanonicalMassPacket packet input choices)

set_option maxHeartbeats 1000000 in
theorem capacityBudget_le_nominal (hpacket : packet.Realizes)
    (frame : SourceFrame) (hframe : call.frame = frame)
    (ready : (N4.annulusDemand p frame).Ready call input)
    (side : Bool) (a : P.support.labels side) (rectangle : Bool) :
    (P.calibrations.side side a rectangle).calibration.parameters.m +
      (P.calibrations.side side a rectangle).calibration.parameters.q +
      (P.capacities.side side a rectangle).exponent ≤ packet.nominalBudget side := by
  let G := P.geometry.geometry side a rectangle
  let D := P.calibrations.side side a rectangle
  let result := P.normalization side a rectangle
  let root := idealLogLength call.base (secondSixthRootIdeal packet.R.primes
    (selectedMultiplicity packet.R side) (oppositeMultiplicity packet.R side)).val
  have herror : G.lengths.scales.error = 16 * p.loss := by
    change G.lengths.scales.rowError + G.lengths.scales.supportError = _
    rw [P.geometry.rowError side a rectangle, P.geometry.supportError side a rectangle]
    ring
  have hraw : G.lengths.rawScaleError = p.loss :=
    N4.certificate_rawScaleError_eq hpacket P.seed frame input hframe ready P.support
      P.calibrations P.geometry side a rectangle
  have hnominal : G.nominal = packet.nominal side := P.geometry.nominal side a rectangle
  have hwidth := G.lengths.width_bounds.1
  change D.calibration.parameters.m + D.calibration.parameters.q ≤
    (G.nominal.skeleton.sixthDeletionSkeleton root).nominalWidth + G.lengths.scales.error
    at hwidth
  rw [NominalChildGeometry.sixthDeletionSkeleton_nominalWidth, herror, hnominal] at hwidth
  change D.calibration.parameters.m + D.calibration.parameters.q +
    (((G.nominal.halfSecond - root) - G.nominal.secondRadical + G.nominal.skeleton.w +
      G.nominal.boundary + G.nominal.tag.poolLength (recipeInductionSigma c)) +
      (G.nominal.supportError + (G.lengths.rawScaleError +
        (Real.log result.profiles.annulus + Real.log result.profiles.annulus) /
          Real.log call.base) + G.lengths.scales.error) / 6 +
        D.calibration.parameters.κ * (momentMesh K c.family).val) ≤ _
  rw [hraw, herror, hnominal, result.annulus_eq, D.kappa_eq,
    packet.nominal_supportError_eq hpacket side]
  dsimp only [RawLeafPacket.nominalBudget, RawLeafPacket.nominalCore, RawLeafPacket.annulusLog]
  linarith only [hwidth, p.loss_pos]

/-- Both sides use one common numerical budget for their unchanged
active label, including its original whole-slot removal set. -/
theorem capacityBudget_le (hpacket : packet.Realizes)
    (frame : SourceFrame) (hframe : call.frame = frame)
    (ready : (N4.annulusDemand p frame).Ready call input)
    (side : Bool) (a : P.support.labels side) (rectangle : Bool) :
    (P.calibrations.side side a rectangle).calibration.parameters.m +
      (P.calibrations.side side a rectangle).calibration.parameters.q +
      (P.capacities.side side a rectangle).exponent ≤ packet.nominalBudget false :=
  (P.capacityBudget_le_nominal hpacket frame hframe ready side a rectangle).trans_eq
    (packet.nominalBudget_eq_false hpacket side)

theorem arithmeticMass_le_nominal (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (frame : SourceFrame) (hframe : call.frame = frame)
    (ready : (N4.annulusDemand p frame).Ready call input) :
    (P.seed.refinement input P.support).arithmeticMass P.calibrations P.capacities ≤
      (4 * packet.leaf.weight * (P.support.labels false).card *
        (P.support.labels true).card) * P.originalPairBound (packet.nominalBudget false) :=
  P.arithmeticMass_le_original hpacket horders (packet.nominalBudget false)
    (P.capacityBudget_le hpacket frame hframe ready)

end CanonicalMassPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.nominalCore_eq_false
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalMassPacket.capacityBudget_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalMassPacket.arithmeticMass_le_nominal
