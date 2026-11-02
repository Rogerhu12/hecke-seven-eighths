import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.KernelMassContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FullKappaContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N9 with the fixed N6 analytic choices

The numerical radius is the original N6 radiusFactor, with its fixed
contour, complete norm box two, original mesh and original analytic
height.  It is computed from choices selected before the moving call.
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
variable {c : TargetContext K} {loss : ℝ}

def fullKappaKernelRadius (choices : FullKappaChoices c loss) (call : Call c) : ℝ :=
  CanonicalFullKappaPrime.radiusFactor K call.base choices.contour (fullKappaLengthBound c)
    (CanonicalHeckePrimeAnalytic.degreeBound K)
    (choices.heightC * (1 + Real.log call.base))
    (CompleteMovingRowRecipe.primeMaskLogBound (Arithmetic.data c) call.base 2)

/-- The complete original contour and radius are already fixed by N6.
Only exact individual capacity identities and active coefficient bounds
remain to be supplied by the N5b/N6 constructors. -/
def FullKappaKernelMassTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (choices : FullKappaChoices c p.loss) (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ),
    ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ (call : Call c) (input : ProfileInput call)
        (trace : SourceTrace call p), trace.Realizes →
      ∀ (geometry : GeometryFamily trace.second) (raw : RawFamily geometry)
        (O : ∀ j : Fin raw.count, OrdinaryData (raw.packet j))
        (R : ∀ j, RefinementData (O j) input)
        (C : ∀ j, (R j).Calibrations) (G : ∀ j, (C j).Capacities),
      let N := Assembly.refinedNormalizedData raw O R C G
      ∀ B : ℝ, 0 ≤ B →
      ∀ D : KernelRadiusData N c.geometry.slots J₁₁ J₁₂ J₂₁ J₂₂ B
        (fullKappaKernelRadius choices call),
        (∀ b, Integrable (D.envelope b)
          (nestedFourierMeasure (N.firstKernel b.val) (N.secondKernel b.val))) ∧
        (∀ b : N.Active, IsFiniteMeasure (N.kernel b)) ∧
        N.kernelMass ≤ coefficient * (1 + B) ^ fullKappaProfilePower c *
          call.base ^ p.loss * N.arithmeticMass

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
