import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildFamily
import Mathlib.Data.Fintype.BigOperators

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # One positive finite kernel for both Cauchy sides -/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {I J Ω : Type*} [MeasurableSpace Ω]
variable {d : MomentData K ω ψ} {a : RealParameters} {σ Z : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

structure FiniteKernelFamily (f : ChildFamily I Ω d a σ admissible) (Z : ℝ) where
  kernel : I → Measure Ω
  finite_kernel : ∀ b, IsFiniteMeasure (kernel b)
  integrable : ∀ side b, Integrable (f.energy side b Z) (kernel b)
  cauchy_integrable : ∀ b, Integrable (f.pair b Z) (kernel b)

namespace FiniteKernelFamily

variable {f : ChildFamily I Ω d a σ admissible}

def mass [Fintype I] (g : FiniteKernelFamily f Z) : ℝ :=
  ∑ b : I, (g.kernel b).real Set.univ

def pairIntegral [Fintype I] (g : FiniteKernelFamily f Z) : ℝ :=
  ∑ b : I, ∫ ξ, f.pair b Z ξ ∂g.kernel b

theorem mass_nonneg [Fintype I] (g : FiniteKernelFamily f Z) : 0 ≤ g.mass := by
  sorry

theorem pairIntegral_nonneg [Fintype I] (g : FiniteKernelFamily f Z) :
    0 ≤ g.pairIntegral := by
  sorry

/-- The same finite measure occurs in both energies and in the paired integral. -/
theorem pairIntegral_le_average [Fintype I] (g : FiniteKernelFamily f Z)
    (hZ : 0 < Z) :
    g.pairIntegral ≤ ∑ b : I,
      ((∫ ξ, f.energy false b Z ξ ∂g.kernel b) +
        ∫ ξ, f.energy true b Z ξ ∂g.kernel b) / 2 := by
  sorry

def reindex (g : FiniteKernelFamily f Z) (e : J → I) :
    FiniteKernelFamily (f.reindex e) Z where
  kernel b := g.kernel (e b)
  finite_kernel b := g.finite_kernel (e b)
  integrable side b := g.integrable side (e b)
  cauchy_integrable b := g.cauchy_integrable (e b)

theorem mass_reindex [Fintype I] [Fintype J]
    (g : FiniteKernelFamily f Z) (e : J ≃ I) :
    (g.reindex e).mass = g.mass := by
  sorry

theorem pairIntegral_reindex [Fintype I] [Fintype J]
    (g : FiniteKernelFamily f Z) (e : J ≃ I) :
    (g.reindex e).pairIntegral = g.pairIntegral := by
  sorry

def sigma {J : Type*} {I : J → Type*}
    {f : ∀ j, ChildFamily (I j) Ω d a σ admissible}
    (g : ∀ j, FiniteKernelFamily (f j) Z) :
    FiniteKernelFamily (ChildFamily.sigma f) Z where
  kernel b := (g b.1).kernel b.2
  finite_kernel b := (g b.1).finite_kernel b.2
  integrable side b := (g b.1).integrable side b.2
  cauchy_integrable b := (g b.1).cauchy_integrable b.2

theorem mass_sigma {J : Type*} {I : J → Type*}
    [Fintype J] [∀ j, Fintype (I j)]
    {f : ∀ j, ChildFamily (I j) Ω d a σ admissible}
    (g : ∀ j, FiniteKernelFamily (f j) Z) :
    (sigma g).mass = ∑ j : J, (g j).mass := by
  sorry

theorem pairIntegral_sigma {J : Type*} {I : J → Type*}
    [Fintype J] [∀ j, Fintype (I j)]
    {f : ∀ j, ChildFamily (I j) Ω d a σ admissible}
    (g : ∀ j, FiniteKernelFamily (f j) Z) :
    (sigma g).pairIntegral = ∑ j : J, (g j).pairIntegral := by
  sorry

end FiniteKernelFamily
end HeckeSkeleton.Moments.EngineStepV2

#print axioms HeckeSkeleton.Moments.EngineStepV2.FiniteKernelFamily.pairIntegral_le_average
#print axioms HeckeSkeleton.Moments.EngineStepV2.FiniteKernelFamily.mass_reindex
#print axioms HeckeSkeleton.Moments.EngineStepV2.FiniteKernelFamily.mass_sigma
