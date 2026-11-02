import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S2FirstPhysicalCutoff
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S2FirstRowWindow

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S2: the actual retained endpoint obeys the nominal window

When the direct row set is nonempty, its physical cutoff is at least
one.  The retained endpoint is therefore that same cutoff.  Exchanging
the two Cauchy sides exchanges the common ideals and preserves the
actual active radical, so the single physical bound covers both sides.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p}

theorem source_retained_upper (hF : F.Realizes)
    (hcolumns : ∀ i ∈ F.source.columns, F.coefficient i ≠ 0 →
      (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤
        call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z + p.loss))
    (key : FirstCauchyKey F) (N : F.source.Normalization)
    (hne : (source key N).source.rows.Nonempty) :
    (source key N).first.retainedScale ≤
      call.base ^ (2 * (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z) -
        idealLogLength call.base (source key N).first.selected.val -
        idealLogLength call.base (source key N).first.opposite.val +
        idealLogLength call.base (firstActiveRadical
          (source key N).first.selected.val (source key N).first.opposite.val) +
        idealLogLength call.base (source key N).first.complementary.val -
        call.workingParameters.m + 4 * p.loss) := by
  rw [source_retained_eq_cutoff hF key N hne]
  have hb := physicalCutoff_le hF hcolumns key.1 key.2.1
  change (F.source.source key.1).divisorPhysicalCutoff key.2.1.val ≤
    call.base ^ (2 * (call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.workingParameters.z) - idealLogLength call.base (selected key).val -
      idealLogLength call.base (opposite key).val +
      idealLogLength call.base (firstActiveRadical (selected key).val (opposite key).val) +
      idealLogLength call.base (complementary key).val -
      call.workingParameters.m + 4 * p.loss)
  by_cases hs : FirstCauchyKey.side key = true
  · simp only [selected, opposite, complementary, hs, if_true]
    apply hb.trans_eq
    congr 1
    rw [S2Cutoff.activeRadical_swap (F.source.block key.1).common_support_eq]
    ring
  · simpa only [selected, opposite, complementary, hs, Bool.false_eq_true, if_false] using hb

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2.source_retained_upper
