import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedIndexedKernelMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The common original Fourier windows pay the actual kernel envelope

The base theorem chooses its seminorms and scalar before the moving
family. Its remaining arithmetic sum is exactly NormalizedData's sum,
with the same active labels, outer weights, children and two kernels.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep Blueprint

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}

theorem original_profile_mass_bound
    (cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ : ℕ) :
    ∃ orders₁ orders₂ : Finset (ℕ × ℕ), ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ (call : Call c) (N : NormalizedData call) (P : ℝ), 1 ≤ P →
      ∀ B₁ B₂ : N.Label → ℝ,
        InternalMassAssembly.ProfileWindows N.family N.labels
          N.firstKernel N.secondKernel N.outer B₁ B₂ P
          cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ orders₁ orders₂ →
        N.kernelMass ≤ coefficient *
          P ^ originalProfilePowerDegree cap dBL dBR dF₁ dF₂ * N.arithmeticMass := by
  obtain ⟨orders₁, orders₂, coefficient, hcoefficient, bound⟩ :=
    actual_finite_normalized_kernel_mass_original_profiles
      (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
      (ω := c.family.omega) (ψ := targetCharacter K c) (U := ℝ) (E := ℝ)
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂
  refine ⟨orders₁, orders₂, coefficient, hcoefficient, ?_⟩
  intro call N P hP B₁ B₂ windows
  exact (bound call.base call.base_pos P hP N.family N.labels
    N.firstKernel N.secondKernel N.outer B₁ B₂ N.parentWidth
    windows.outer_nonneg windows.left_radius_nonneg windows.right_radius_nonneg
    windows.left_slots windows.right_slots windows.left_radius windows.right_radius
    windows.left_radius_power windows.right_radius_power
    windows.first_kernel_power windows.second_kernel_power).2

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.original_profile_mass_bound
