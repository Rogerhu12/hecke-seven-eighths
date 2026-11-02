import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9OriginalKernels

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original second-stage row weights on the same raw packets

The source trace already identifies every second chart's weight,
radius and empty mask.  These lemmas project that dictionary through
the existing geometry and raw index, without changing any row.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField MeasureTheory EngineStep EngineInduction.Source
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawFamily

variable (trace : SourceTrace call p) (htrace : trace.Realizes)
variable {geometry : GeometryFamily trace.second} (raw : RawFamily geometry)

theorem second_realizes (j : Fin raw.count) : (raw.packet j).second.Realizes :=
  htrace.second.stage (raw.index j).val.1.1

end RawFamily

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)

theorem second_realizes : packet.second.Realizes := by
  obtain ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩ := hpacket
  exact raw.second_realizes trace htrace j

theorem stage_mask_eq : packet.second.stage.mask = ∅ :=
  (packet.second_realizes hpacket).mask

theorem stage_radius_eq : packet.second.stage.radius.val =
    (packet.second.physical.first.retainedScale *
      call.base ^ packet.second.physical.enlargement)⁻¹ :=
  (packet.second_realizes hpacket).radius

theorem chart_weight_eq (q : Arithmetic.Orbit c) :
    packet.chart.weight q =
      (((CanonicalSecondLogChart.rowRadius packet.second.stage.radius
        packet.key.2.1.val q).val ^ (-p.tilt) : ℝ) : ℂ) :=
  (packet.second_realizes hpacket).weight packet.key.1 packet.key.2.1 q

theorem chart_mask_eq : packet.key.2.1.val = ∅ := by
  have hsubset := Finset.mem_powerset.mp packet.key.2.1.property
  rw [packet.stage_mask_eq hpacket] at hsubset
  exact Finset.eq_empty_of_subset_empty hsubset

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.second_realizes
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.chart_weight_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.chart_mask_eq
