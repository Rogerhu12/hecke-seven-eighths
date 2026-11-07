module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9FullKappaContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TasksKernelMass

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N9 consumes the actual N6 contour and radius power

Every numerical parameter in the Fourier estimate is read from the
same original FullKappaChoices.  No new contour or independent radius
bound is a premise of the public task.
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
variable {c : TargetContext K} {call : Call c} {loss : ℝ}

theorem fullKappaKernelRadius_one (choices : FullKappaChoices c loss) (call : Call c) :
    1 ≤ fullKappaKernelRadius choices call :=
  CanonicalFullKappaPrime.one_le_radiusFactor _ _ _ _ _ _
    call.domain.scale.le choices.contour_pos.le (momentMesh K c.family).property.le

theorem fullKappaKernelRadius_power (choices : FullKappaChoices c loss) (call : Call c) :
    fullKappaKernelRadius choices call ^ fullKappaProfilePower c ≤
      choices.radiusConstant ^ fullKappaProfilePower c * call.base ^ loss :=
  choices.radius_power call.base call.domain.scale.le

section SideRadius

variable {H Row ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
variable {R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι}
variable {side : Bool}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter Row k}
variable {D : OriginalCalibration call s} {B : ℝ} {J₁ J₂ : ℕ}
variable {choices : FullKappaChoices c loss} {G : SideGeometryData R side s D}
variable {windows : FullKappaWindows D B J₁ J₂}

theorem FullKappaSideResult.capacity_radius_at_call
    (result : FullKappaSideResult choices G windows) (z : ℝ × ℝ) :
    result.capacity.radius (WithLp.toLp 2 z) = polynomialProfileRadius
      (CanonicalFullKappaPrime.enlargedCoefficient B (fullKappaKernelRadius choices call))
      J₁ J₂ z := by
  simpa only [D.base_eq, fullKappaKernelRadius] using
    result.capacity_radius (WithLp.toLp 2 z)

end SideRadius

namespace Tasks

theorem fullKappaKernelMass (c : TargetContext K) (p : SourceParameters c) :
    FullKappaKernelMassTask c p := by
  intro choices J₁₁ J₁₂ J₂₁ J₂₂
  obtain ⟨coefficient, hcoefficient, bound⟩ :=
    kernelMass c p c.geometry.slots J₁₁ J₁₂ J₂₁ J₂₂
  refine ⟨coefficient * choices.radiusConstant ^ fullKappaProfilePower c,
    mul_pos hcoefficient (pow_pos (zero_lt_one.trans_le choices.radiusConstant_one_le) _), ?_⟩
  intro call input trace htrace geometry raw O R C G _N B hB D
  have h := bound call input trace htrace geometry raw O R C G
    B (fullKappaKernelRadius choices call)
    (choices.radiusConstant ^ fullKappaProfilePower c) hB
    (fullKappaKernelRadius_one choices call)
    (pow_nonneg (zero_le_one.trans choices.radiusConstant_one_le) _)
    (fullKappaKernelRadius_power choices call) D
  exact h

end Tasks
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FullKappaSideResult.capacity_radius_at_call
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.fullKappaKernelMass
