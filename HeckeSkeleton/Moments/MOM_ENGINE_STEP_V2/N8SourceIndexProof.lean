import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourcePoolMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N8a: the uniform source-index certificate

The actual raw carrier is first summed over its original second
classes, keeping both independent divisors and both occurrence
allocations.  Its first-divisor density then feeds the original first
common-support sum.  The same earlier prime pool is summed exactly once.
Every fixed constant and the scale threshold precedes the call.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source

open EngineStep EngineInduction.Source
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

theorem sourceIndexTask (c : TargetContext K) (p : SourceParameters c) :
    SourceIndexTask c p := by
  intro frame loss hloss
  let ε : ℝ := loss / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨R, hR, hraw⟩ := original_raw_index_reduction c ε hε
  obtain ⟨F, hF, hfirst⟩ := original_first_index_mass c ε hε
  obtain ⟨P, threshold, hP, hthreshold, hpool⟩ :=
    original_expansion_index_reduction c p frame
  refine ⟨{
    coefficient := R * P * F
    coefficient_nonneg := by positivity
    threshold := max threshold (normThreshold c frame)
    threshold_one := hthreshold.trans (le_max_left _ _)
    bound := ?_ }⟩
  intro call input hframe large trace htrace geometry _hgeometry raw hrawRealizes
  have hbase_pos : 0 < call.base := call.base_pos
  have largeNorm : normThreshold c call.frame ≤ call.base := by
    rw [hframe]
    exact (le_max_right _ _).trans large
  have largePool : threshold ≤ call.base := (le_max_left _ _).trans large
  have hr := hraw call input largeNorm p trace htrace geometry raw hrawRealizes
  have hp := hpool call input hframe largePool trace htrace
  have hf := hfirst call input largeNorm p trace.first htrace.first trace.cauchy htrace.cauchy
  calc
    raw.indexMass ≤ R * call.base ^ ε * trace.expansion.firstIndexMass := hr
    _ ≤ (R * call.base ^ ε) *
        (P * call.base ^ p.loss * trace.cauchy.firstIndexMass) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (R * call.base ^ ε) * (P * call.base ^ p.loss * (F * call.base ^ ε)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hf (by positivity)) (by positivity)
    _ = (R * P * F) * call.base ^ (loss + p.loss) := by
      have he : loss + p.loss = ε + p.loss + ε := by dsimp [ε]; ring
      rw [he, Real.rpow_add call.base_pos, Real.rpow_add call.base_pos]
      ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.sourceIndexTask
