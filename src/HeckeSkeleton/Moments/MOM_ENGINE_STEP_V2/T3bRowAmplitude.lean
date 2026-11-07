module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bRowBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bMaskGeometry
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bScaleBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bPoolOuter

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original row amplitude and nominal scalar coordinates

The same S5 geometry identifies the retained radius, actual enlargement,
two second common norms and selected first allowance. The retained
scale is at least one in every direct, main and valuation-error source,
so its positive Mellin tilt only decreases the original row amplitude.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

namespace T3b

theorem rpow_logLength (Z R : ℝ) (hZ : 1 < Z) (hR : 0 < R) :
    Z ^ (Real.log R / Real.log Z) = R := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ),
    show Real.log Z * (Real.log R / Real.log Z) = Real.log R by
      field_simp [(Real.log_pos hZ).ne'] <;> ring, Real.exp_log hR]

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)

include hpacket in
theorem t3b_nominal_opposite (side : Bool) :
    (packet.nominal side).ideals.opposite.val = packet.second.physical.first.opposite.val := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).opposite side

include hpacket in
theorem t3b_nominal_complementary (side : Bool) :
    (packet.nominal side).ideals.complementary.val =
      packet.second.physical.first.complementary.val := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).complementary side

include hpacket in
theorem t3b_nominal_retained (side : Bool) :
    (packet.nominal side).retainedScale = packet.second.physical.first.retainedScale := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).retainedScale side

include hpacket in
theorem t3b_nominal_firstFrequency (side : Bool) :
    (packet.nominal side).skeleton.firstFrequency = packet.second.physical.firstFrequency := by
  simp only [NominalChildGeometry.firstFrequency, OriginalNominalGeometry.skeleton,
    PhysicalSource.firstFrequency, packet.t3b_nominal_first hpacket,
    packet.t3b_nominal_opposite hpacket, packet.t3b_nominal_complementary hpacket]

include hpacket in
theorem t3b_nominal_retainedLength_rpow (side : Bool) :
    call.base ^ (packet.nominal side).skeleton.Krow =
      packet.second.physical.first.retainedScale := by
  change call.base ^ (Real.log (packet.nominal side).retainedScale / Real.log call.base) = _
  rw [packet.t3b_nominal_retained hpacket]
  exact T3b.rpow_logLength call.base _ call.domain.scale
    packet.second.physical.first.retainedScale_pos

include hpacket in
theorem t3b_nominal_enlargement (side : Bool) :
    (packet.nominal side).skeleton.g = packet.second.physical.enlargement := by
  have hfreq : (packet.nominal side).ideals.firstFrequency call.workingParameters call.base =
      packet.second.physical.firstFrequency := packet.t3b_nominal_firstFrequency hpacket side
  change (packet.nominal side).enlargement = packet.second.physical.enlargement
  unfold OriginalNominalGeometry.enlargement OriginalNominalGeometry.shiftedCommon
    OriginalNominalGeometry.retainedLength PhysicalSource.enlargement
  rw [packet.t3b_nominal_first hpacket, packet.t3b_nominal_opposite hpacket,
    packet.t3b_nominal_tag hpacket, packet.t3b_nominal_retained hpacket, hfreq]
  congr 1
  congr 1
  ring

theorem t3b_enlargement_nonneg : 0 ≤ packet.second.physical.enlargement := by
  have hs := (recipeInduction_budget (c := c)).1.le
  have hpad : 0 ≤ packet.second.physical.first.tag.padding (recipeInductionSigma c) := by
    cases packet.second.physical.first.tag <;> simp only [OriginalNominalTag.padding] <;> positivity
  exact add_nonneg (le_max_right _ _) hpad

include hpacket in
/-- The true original row amplitude is paid at its own nominal radius. -/
theorem t3bRowAmplitude_le_nominal (side : Bool) :
    packet.t3bRowAmplitude ≤ orbitalFieldFactor K *
      call.base ^ ((packet.nominal side).skeleton.Krow + (packet.nominal side).skeleton.g) := by
  have hone : 1 ≤ packet.second.physical.first.retainedScale *
      call.base ^ packet.second.physical.enlargement :=
    one_le_mul_of_one_le_of_one_le (packet.t3b_retainedScale_one hpacket)
      (Real.one_le_rpow call.domain.scale.le packet.t3b_enlargement_nonneg)
  have hpow : (packet.second.physical.first.retainedScale *
      call.base ^ packet.second.physical.enlargement) ^ (1 - p.tilt) ≤
        packet.second.physical.first.retainedScale * call.base ^ packet.second.physical.enlargement := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hone (sub_le_self 1 p.tilt_pos.le))
  rw [packet.t3bRowAmplitude_eq_retained hpacket]
  calc
    _ ≤ orbitalFieldFactor K * (packet.second.physical.first.retainedScale *
        call.base ^ packet.second.physical.enlargement) :=
      mul_le_mul_of_nonneg_left hpow (orbitalFieldFactor_nonneg K)
    _ = _ := by
      rw [Real.rpow_add call.base_pos, packet.t3b_nominal_retainedLength_rpow hpacket,
        packet.t3b_nominal_enlargement hpacket]

include hpacket in
/-- The denominator contains both actual common ideals, with either
orientation giving exactly the same twice-half-common exponent. -/
theorem t3b_secondNorm_product_eq (side : Bool) :
    (Ideal.absNorm (packet.secondIdeal false) : ℝ) *
        (Ideal.absNorm (packet.secondIdeal true) : ℝ) =
      call.base ^ (2 * (packet.nominal side).halfSecond) := by
  have hn (s : Bool) : packet.secondIdeal s ≠ 0 := by
    rw [← N4.secondFrozenIdeal_eq packet s]
    exact N4.secondFrozenIdeal_ne_zero packet s
  rw [packet.t3b_halfSecond_eq hpacket]
  rw [show 2 * ((idealLogLength call.base (packet.secondIdeal side) +
      idealLogLength call.base (packet.secondIdeal (!side))) / 2) =
        idealLogLength call.base (packet.secondIdeal side) +
          idealLogLength call.base (packet.secondIdeal (!side)) by ring,
    Real.rpow_add call.base_pos,
    rpow_idealLogLength call.base call.domain.scale _ (hn side),
    rpow_idealLogLength call.base call.domain.scale _ (hn (!side))]
  cases side <;> simp only [Bool.not_false, Bool.not_true] <;> ring

include hpacket in
theorem t3b_firstAllowance_eq_nominal (side : Bool) :
    packet.second.physical.first.t3bAllowance =
      call.base ^ ((packet.nominal side).skeleton.A + (packet.nominal side).skeleton.q +
        (packet.nominal side).skeleton.R + (packet.nominal side).skeleton.E -
        (packet.nominal side).skeleton.c + (packet.nominal side).boundary) := by
  simp only [FirstCoordinates.t3bAllowance, OriginalNominalGeometry.skeleton,
    OriginalNominalGeometry.boundary, packet.t3b_nominal_first hpacket,
    packet.t3b_nominal_opposite hpacket, packet.t3b_nominal_complementary hpacket]

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bRowAmplitude_le_nominal
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_secondNorm_product_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_firstAllowance_eq_nominal
