import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9RadiusData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementAssembly

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N9: integrate the original kernels of the same refined family

Paper Section 4.8, lines 3043--3073.  The finite Fourier orders and
constant precede the moving call and all its original labels.  N5b
supplies the individual original profile coefficients on actual active labels; N6 supplies the
literal polynomial radii and the full power of its already fixed
radius factor.  The conclusion retains the exact N8 arithmetic mass.

The shared contour is not chosen in this task.  Nor are first or second
kernel bounds premises: the proof identifies both with the fixed
canonical kernels along the actual S1--S4 source chain.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField MeasureTheory EngineStep
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]

def KernelMassTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ cap J₁₁ J₁₂ J₂₁ J₂₂ : ℕ, ∃ coefficient : ℝ, 0 < coefficient ∧
    ∀ (call : Call c) (input : ProfileInput call)
      (trace : SourceTrace call p), trace.Realizes →
    ∀ (geometry : GeometryFamily trace.second) (raw : RawFamily geometry)
      (O : ∀ j : Fin raw.count, OrdinaryData (raw.packet j))
      (R : ∀ j, RefinementData (O j) input)
      (C : ∀ j, (R j).Calibrations) (G : ∀ j, (C j).Capacities),
    let N := Assembly.refinedNormalizedData raw O R C G
    ∀ B radius radiusCost : ℝ, 0 ≤ B → 1 ≤ radius → 0 ≤ radiusCost →
      radius ^ ((cap + 2) + (cap + 2)) ≤ radiusCost * call.base ^ p.loss →
    ∀ D : KernelRadiusData N cap J₁₁ J₁₂ J₂₁ J₂₂ B radius,
      (∀ b, Integrable (D.envelope b)
        (nestedFourierMeasure (N.firstKernel b.val) (N.secondKernel b.val))) ∧
      (∀ b : N.Active, IsFiniteMeasure (N.kernel b)) ∧
      N.kernelMass ≤ coefficient * radiusCost *
        (1 + B) ^ ((cap + 2) + (cap + 2)) * call.base ^ p.loss * N.arithmeticMass

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
