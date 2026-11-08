module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondTransformArithmetic
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsPhase

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Integration of the exact second-transform decomposition

The three literal terms are integrated against the original first
Fourier measure. The same complete coefficient and source are retained
at each frequency, and the nonnegative original outer weight is paid
once. Integrability follows from the finite original Gram phases.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem phase_energy_le (source : SecondSource call p) (x : ℝ) :
    source.physical.source.phaseEnergy (hDiff := Arithmetic.different c)
      source.physical.firstPoint x ≤
        (source.stage.fiber : ℝ) *
          ((source.phaseStage x).rawZeroCost + source.phaseTail x +
            (source.phaseStage x).rawNonzeroCost) := by
  exact raw_energy_le
    (originalPoissonData (Arithmetic.context c))
    (originalPoissonData_recipes (Arithmetic.context c))
    (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_locallyConstant K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_compactSupport K (Arithmetic.data c).Sf 1)
    (source.physical.source.withMultiplier
      (fun i => jointPhase x (source.physical.firstPoint i))) (source.phaseStage x)

theorem source_cost_le (source : SecondSource call p) :
    source.physical.cost ≤ source.zero + source.tail + source.nonzero := by
  have hz := Tails.phaseZero_integrable source
  have ht := Tails.phaseTail_integrable source
  have hn := source.stage.rawPhaseNonzeroCost_integrable
    source.physical.firstKernel source.physical.firstPoint
  change Integrable (fun x : ℝ => (source.phaseStage x).rawNonzeroCost)
    (actualFourierMeasure source.physical.firstKernel) at hn
  have hzt : Integrable
      (fun x : ℝ => (source.phaseStage x).rawZeroCost + source.phaseTail x)
      (actualFourierMeasure source.physical.firstKernel) := hz.add ht
  have henergy := source.physical.source.phaseEnergy_integrable
    (hDiff := Arithmetic.different c) source.physical.firstKernel source.physical.firstPoint
  have hbound := integral_mono henergy
    ((hzt.add hn).const_mul (source.stage.fiber : ℝ))
    (phase_energy_le source)
  calc
    source.physical.cost ≤ source.physical.outerWeight *
        ∫ x, (source.stage.fiber : ℝ) *
          ((source.phaseStage x).rawZeroCost + source.phaseTail x +
            (source.phaseStage x).rawNonzeroCost)
            ∂actualFourierMeasure source.physical.firstKernel :=
      mul_le_mul_of_nonneg_left hbound source.physical.outerWeight_nonneg
    _ = source.zero + source.tail + source.nonzero := by
      unfold SecondSource.zero SecondSource.tail SecondSource.nonzero
      rw [integral_const_mul, integral_add hzt hn, integral_add hz ht]
      ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate.source_cost_le
