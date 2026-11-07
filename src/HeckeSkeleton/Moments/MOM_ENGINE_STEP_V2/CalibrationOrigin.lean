module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalRefinement
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The calibrated rows retain the original physical windows

The source trace and its S5 geometry supply the windows of this exact
raw packet. Restricting to the ordinary live rows, changing the side,
and making the passive allocation preserve its extracted moment ideal.
The calibration cutoff follows from the original physical row window.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain
open DedekindZetaZeroFree.LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem realized_rowWindow (hpacket : packet.Realizes) (side : Bool) (h : packet.R.live) :
    idealNorm K (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal ≤
      call.base ^ ((packet.nominal side).skeleton.nominalRow + 12 * p.loss) := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).rowWindow side h

theorem realized_supportWindow (hpacket : packet.Realizes) (side : Bool) :
    (Arithmetic.data c).exteriorNorm packet.second.physical.first.paidSupport *
      (Ideal.absNorm (packet.nominal side).ideals.unitPart.val : ℝ) *
      (Ideal.absNorm (packet.nominal side).ideals.nonunitPart.val : ℝ) ≤
        call.base ^ ((packet.nominal side).skeleton.nominalSupport + 4 * p.loss) := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).supportWindow side

theorem realized_unitPart (hpacket : packet.Realizes) (side : Bool) (h : packet.R.live) :
    (packet.nominal side).ideals.unitPart.val =
      (unitFrequencyRadical (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)).val := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).unitPart side h

theorem realized_nonunitPart (hpacket : packet.Realizes) (side : Bool) (h : packet.R.live) :
    (packet.nominal side).ideals.nonunitPart.val =
      (nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)).val := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).nonunitPart side h

theorem nominalSupport_error_nonneg (hpacket : packet.Realizes) (side : Bool) :
    0 ≤ (packet.nominal side).skeleton.nominalSupport + 4 * p.loss := by
  have hp : 1 ≤ (Arithmetic.data c).exteriorNorm packet.second.physical.first.paidSupport :=
    actual_momentIdeal_norm_one_le (exteriorMomentIdeal packet.second.physical.first.paidSupport)
  have hu : 1 ≤ (Ideal.absNorm (packet.nominal side).ideals.unitPart.val : ℝ) :=
    actual_momentIdeal_norm_one_le (packet.nominal side).ideals.unitPart
  have hn : 1 ≤ (Ideal.absNorm (packet.nominal side).ideals.nonunitPart.val : ℝ) :=
    actual_momentIdeal_norm_one_le (packet.nominal side).ideals.nonunitPart
  have hprod := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hp hu) hn
  apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
  simpa only [Real.rpow_zero] using hprod.trans (packet.realized_supportWindow hpacket side)

end RawLeafPacket

namespace OrdinaryData

variable {packet : RawLeafPacket call p} (O : OrdinaryData packet)

def originalLiveRow (h : O.rows.live) : packet.R.live :=
  packet.R.liveInclusion (fun h => ¬packet.leaf.exceptional h) h

theorem originalSource_momentIdeal (side rectangle : Bool) (h : O.rows.live) :
    ((O.originalSource side rectangle).row h).momentIdeal =
      (packet.R.extractedRow (Arithmetic.context c) (O.originalLiveRow h)).momentIdeal := by
  cases side <;> rfl

end OrdinaryData

namespace OrdinarySeed

variable {packet : RawLeafPacket call p} (seed : OrdinarySeed packet)
variable (input : ProfileInput call) (support : seed.ordinary.PassiveSupport input)

theorem canonicalSource_rowWindow (hpacket : packet.Realizes)
    (side : Bool) (a : support.labels side) (rectangle : Bool)
    (h : seed.ordinary.rows.live) :
    idealNorm K ((seed.canonicalSource input support side a rectangle).row h).momentIdeal ≤
      call.base ^ ((packet.nominal side).skeleton.nominalRow + 12 * p.loss) := by
  change idealNorm K ((seed.ordinary.originalSource side false).row h).momentIdeal ≤ _
  rw [seed.ordinary.originalSource_momentIdeal]
  exact packet.realized_rowWindow hpacket side (seed.ordinary.originalLiveRow h)

theorem canonicalSource_cutoff (hpacket : packet.Realizes)
    (side : Bool) (a : support.labels side) (rectangle : Bool)
    (q : ℝ) (hq : 0 ≤ q) (h : seed.ordinary.rows.live) :
    (Arithmetic.data c).exteriorNorm
        ((seed.canonicalSource input support side a rectangle).originalIdeal h) ≤
      (seed.canonicalSource input support side a rectangle).normFactor h *
        call.base ^ ((packet.nominal side).skeleton.nominalRow + 12 * p.loss + q) := by
  let s := seed.canonicalSource input support side a rectangle
  calc
    _ = s.normFactor h * idealNorm K (s.row h).momentIdeal := (s.row h).norm_factor
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((seed.canonicalSource_rowWindow input support hpacket side a rectangle h).trans
        (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (le_add_of_nonneg_right hq)))
      (s.row h).factor_pos.le

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.realized_rowWindow
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalSource_rowWindow
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalSource_cutoff
