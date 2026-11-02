import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.KernelMassContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9OriginalKernels
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9FixedRadiusMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N9 proof: the same original pair and the same normalization radius

The source identities fix the two kernels.  The analytic estimate then
integrates the complete capacity envelope on that pair, without changing
the child family, its contour, its outer weights or its active labels.
-/

noncomputable section
open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]

theorem kernelMass (c : TargetContext K) (p : SourceParameters c) :
    KernelMassTask c p := by
  intro cap J₁₁ J₁₂ J₂₁ J₂₂
  obtain ⟨coefficient, hcoefficient, bound⟩ := fixed_radius_kernel_mass
    (c := c) cap J₁₁ J₁₂ J₂₁ J₂₂ (secondKernel c p) (secondKernel c p)
  refine ⟨coefficient, hcoefficient, ?_⟩
  intro call input trace htrace geometry raw O R C G _N B radius radiusCost
    hB hradius hcost hpower D
  have hk := Assembly.refinedNormalizedData_original_kernels trace htrace raw O R C G
  exact bound call (Assembly.refinedNormalizedData raw O R C G)
    B radius radiusCost p.loss hB hradius hcost hpower
    (fun b => (hk b).1) (fun b => (hk b).2) D

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.kernelMass
