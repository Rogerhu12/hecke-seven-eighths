module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9ProfileWindowData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N9 for the actual upstream N5b windows and N6 capacities

This contract has no clipping-bound or capacity-radius hypothesis.
It consumes the original upstream records and projects the same
capacities from their N6 results.  All uniform data precede the call.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField MeasureTheory EngineStep EngineInduction.Source
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]

def OriginalWindowKernelMassTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (frame : SourceFrame) (shape : ProfileShape) (orders : Finset (ℕ × ℕ))
    (choices : FullKappaChoices c p.loss)
    (certificate : UniformProfileWindowCertificate c frame shape orders),
    ∃ kernelCost : UniformCost,
      kernelCost.orders = certificate.inputOrders ∧
      kernelCost.threshold = 1 ∧
      ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
      ∀ horders : call.childOrders ⊆ orders, kernelCost.Ready call input →
      ∀ (trace : SourceTrace call p), trace.Realizes →
      ∀ (geometry : GeometryFamily trace.second) (raw : RawFamily geometry)
        (O : ∀ j : Fin raw.count, OrdinaryData (raw.packet j))
        (R : ∀ j, RefinementData (O j) input) (C : ∀ j, (R j).Calibrations)
        (windows : ∀ j, (C j).ProfileWindows orders
          (certificate.coefficient * input.amplitude * 1)
          (certificate.costCoefficient * input.amplitude * (1 + 1)) certificate.degree)
        (results : ∀ j, (C j).FullKappaResults choices horders (windows j)),
      let G := fun j => (C j).fullKappaCapacities (results j)
      let N := Assembly.refinedNormalizedData raw O R C G
      (∀ b : N.Active, Integrable
        (fun z : ℝ × ℝ => normalizedCapacityPairEnvelope (N.family.leftCapacity b.val)
          (N.family.rightCapacity b.val) (WithLp.toLp 2 z))
        (nestedFourierMeasure (N.firstKernel b.val) (N.secondKernel b.val))) ∧
      (∀ b : N.Active, IsFiniteMeasure (N.kernel b)) ∧
      N.kernelMass ≤ kernelCost.value input.amplitude call.request.height *
        call.base ^ (recipeInductionEdgeLoss c / 2) * N.arithmeticMass

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
