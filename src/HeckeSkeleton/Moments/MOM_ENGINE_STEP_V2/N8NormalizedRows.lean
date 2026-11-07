module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationOrigin
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedInnerAtoms
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9OriginalRowWeights
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EmptyGaussMask
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalLogTiltWindows

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The genuine orbital row and its complete correlation

The first retained scale is the original maximum with one and the pool
keeps it. The second transform uses its inverse after a nonnegative
enlargement. Thus its actual negative row tilt costs at most one. The
common correlation keeps its exact gcd divided by the same unit-radical
label; neither side introduces a second correlation factor.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace FirstCauchyFamily

variable {F : FirstPresentation call p} (family : FirstCauchyFamily F)

theorem retainedScale_one (hfamily : family.Realizes) (i : Fin family.count) :
    1 ≤ (family.source i).first.retainedScale := by
  rw [hfamily.retained i]
  exact le_max_left _ _

end FirstCauchyFamily

namespace PoolExpansion

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem retainedScale_one (expansion : PoolExpansion family)
    (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) :
    1 ≤ (expansion.source i).first.retainedScale := by
  cases expansion with
  | direct => exact family.retainedScale_one hfamily i
  | pooled pool count index source =>
    have horigin := hexpansion.2.2 i
    have hr : (source i).first.retainedScale =
        (family.source (index i).1).first.retainedScale := by
      rcases htag : (index i).2 with u | qe
      · simp only [PoolPresentation.Origin, htag] at horigin
        rcases horigin with ⟨_, _, _, _, _, _, _, hfirst⟩
        rw [hfirst]
      · simp only [PoolPresentation.Origin, htag] at horigin
        rcases horigin with
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hretained, _, _, _⟩
        exact hretained
    change 1 ≤ (source i).first.retainedScale
    rw [hr]
    exact family.retainedScale_one hfamily (index i).1

end PoolExpansion

namespace PhysicalSource

variable (source : PhysicalSource call p)

theorem enlargement_nonneg : 0 ≤ source.enlargement := by
  have hstep : 0 ≤ recipeInductionSigma c := (recipeInduction_budget (c := c)).1.le
  have hpadding : 0 ≤ source.first.tag.padding (recipeInductionSigma c) := by
    cases source.first.tag <;> simp only [OriginalNominalTag.padding] <;> positivity
  exact add_nonneg (le_max_right _ _) hpadding

end PhysicalSource

namespace RawFamily

variable (trace : SourceTrace call p) (htrace : trace.Realizes)
variable {geometry : GeometryFamily trace.second} (raw : RawFamily geometry)

include htrace in
theorem second_radius_le_one (j : Fin raw.count) :
    (raw.packet j).second.stage.radius.val ≤ 1 := by
  change (trace.second.source (raw.index j).val.1.1).stage.radius.val ≤ 1
  rw [(htrace.second.stage (raw.index j).val.1.1).radius]
  have hr : 1 ≤ (trace.second.source (raw.index j).val.1.1).physical.first.retainedScale := by
    rw [htrace.second.physical]
    exact trace.expansion.retainedScale_one htrace.cauchy htrace.expansion _
  have he : 1 ≤ call.base ^ (trace.second.source (raw.index j).val.1.1).physical.enlargement :=
    Real.one_le_rpow call.domain.scale.le (PhysicalSource.enlargement_nonneg _)
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
    (one_le_mul_of_one_le_of_one_le hr he)
  simpa only [one_div, inv_one] using h

end RawFamily

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem realized_second_radius_le_one (hpacket : packet.Realizes) :
    packet.second.stage.radius.val ≤ 1 := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
  exact raw.second_radius_le_one trace htrace j

def correlationCost : ℝ :=
  (Ideal.absNorm (gcd packet.key.1.val.1 packet.key.1.val.2) : ℝ) /
    (Ideal.absNorm (packet.nominal false).ideals.unitPart.val : ℝ)

theorem correlationCost_nonneg : 0 ≤ packet.correlationCost := by
  unfold correlationCost
  positivity

theorem realized_correlation_bound (hpacket : packet.Realizes) (h : packet.R.live) :
    ‖packet.R.correlation h.val‖ ≤ packet.correlationCost := by
  have hc := packet.block.secondCorrelation_norm_le (Arithmetic.context c)
    packet.R.leftGenerator packet.R.rightGenerator packet.R.leftGenerates
    packet.R.rightGenerates (packet.R.frequency h.val)
  change ‖packet.R.correlation h.val‖ ≤
    (Ideal.absNorm (gcd packet.key.1.val.1 packet.key.1.val.2) : ℝ) /
      (Ideal.absNorm (unitFrequencyRadical (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)).val : ℝ)
    at hc
  rw [← packet.realized_unitPart hpacket false h] at hc
  exact hc

theorem realized_chart_weight_le_one (hpacket : packet.Realizes) (q : Arithmetic.Orbit c) :
    ‖packet.chart.weight q‖ ≤ 1 := by
  rw [packet.chart_weight_eq hpacket, packet.chart_mask_eq hpacket]
  have h := CanonicalSecondLogChart.rowTilt_norm_le_of_norm_window
    (K := K) packet.second.stage.radius ∅ q (Z := call.base) (B := 0) (δ := p.tilt)
    call.base_pos p.tilt_pos.le (by
      simpa only [sIntegerMaskGenerator_empty_norm, mul_one, Real.rpow_zero] using
        packet.realized_second_radius_le_one hpacket)
  simpa only [zero_mul, Real.rpow_zero] using h

def orbitalRowCost : ℝ :=
  ‖secondOrbitalScalar (K := K) (S := (Arithmetic.data c).Sf)
    packet.second.stage.radius packet.key.2.1.val‖ * packet.correlationCost

theorem orbitalRowCost_nonneg : 0 ≤ packet.orbitalRowCost :=
  mul_nonneg (norm_nonneg _) packet.correlationCost_nonneg

theorem realized_row_weight_bound (hpacket : packet.Realizes) (h : packet.R.live) :
    ‖packet.R.weight h.val * packet.R.correlation h.val‖ ≤ packet.orbitalRowCost := by
  change ‖(secondOrbitalScalar (K := K) (S := (Arithmetic.data c).Sf)
    packet.second.stage.radius packet.key.2.1.val * packet.chart.weight h.val) *
      packet.R.correlation h.val‖ ≤ _
  rw [norm_mul, norm_mul]
  apply mul_le_mul _ (packet.realized_correlation_bound hpacket h)
    (norm_nonneg _) (norm_nonneg _)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (packet.realized_chart_weight_le_one hpacket h.val) (norm_nonneg _)

theorem orbitalRowCost_le_inverse_radius (hpacket : packet.Realizes) :
    packet.orbitalRowCost ≤
      (orbitalFieldFactor K / packet.second.stage.radius.val) * packet.correlationCost := by
  apply mul_le_mul_of_nonneg_right _ packet.correlationCost_nonneg
  rw [packet.chart_mask_eq hpacket]
  simpa only [sIntegerMaskGenerator_empty_norm, mul_one] using
    (secondOrbitalScalar_norm_le (K := K) (S := (Arithmetic.data c).Sf)
      packet.second.stage.radius ∅)

theorem orbitalRowCost_le_retained_scale (hpacket : packet.Realizes) :
    packet.orbitalRowCost ≤
      orbitalFieldFactor K * packet.second.physical.first.retainedScale *
        call.base ^ packet.second.physical.enlargement * packet.correlationCost := by
  apply (packet.orbitalRowCost_le_inverse_radius hpacket).trans_eq
  rw [packet.stage_radius_eq hpacket]
  simp only [div_inv_eq_mul]
  ring

end RawLeafPacket

namespace OrdinaryData

variable {packet : RawLeafPacket call p} (O : OrdinaryData packet)

theorem originalSource_row_weight (side rectangle : Bool) (h : O.rows.live) :
    (O.originalSource side rectangle).weight h =
      packet.R.weight h.val * packet.R.correlation h.val := by
  cases side <;> rfl

theorem originalSource_correlation_bound (hpacket : packet.Realizes)
    (h : O.rows.live) :
    ‖packet.R.correlation h.val‖ ≤ packet.correlationCost :=
  packet.realized_correlation_bound hpacket (O.originalLiveRow h)

theorem originalSource_row_weight_bound (hpacket : packet.Realizes)
    (side rectangle : Bool) (h : O.rows.live) :
    ‖(O.originalSource side rectangle).weight h‖ ≤ packet.orbitalRowCost := by
  rw [O.originalSource_row_weight]
  exact packet.realized_row_weight_bound hpacket (O.originalLiveRow h)

end OrdinaryData

namespace OrdinarySeed

variable {packet : RawLeafPacket call p} (seed : OrdinarySeed packet)
variable (input : ProfileInput call) (support : seed.ordinary.PassiveSupport input)

theorem canonicalSource_rowCost_realized (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders)
    (side : Bool) (a : support.labels side) (rectangle : Bool) :
    SourceCost.row (seed.canonicalSource input support side a rectangle) ≤
      packet.orbitalRowCost * (input.frozenAtomBudget ^ c.geometry.slots /
        (Ideal.absNorm packet.allocation.1.val : ℝ)) := by
  apply seed.canonicalSource_rowCost_inner_bound input hpacket horders support
    side a rectangle packet.orbitalRowCost_nonneg
  intro h hh
  exact seed.ordinary.originalSource_row_weight_bound hpacket side false h

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PoolExpansion.retainedScale_one
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.realized_second_radius_le_one
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.realized_correlation_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.realized_chart_weight_le_one
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.realized_row_weight_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalSource_rowCost_realized
