module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaNormalization

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The exact N9 radius data on actual active labels

Only the same family's capacity radii and individual original profile
coefficients are stored here. Inactive labels have no upper-bound
requirement. There is no mass estimate, kernel bound or task proof.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep CanonicalFullKappaPrime

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

/-- The individual polynomial radii of the capacities already selected
by N6.  The coefficients are the N5b coefficients before multiplication
by the single fixed analytic radius.  No mass bound is a field. -/
structure KernelRadiusData (N : NormalizedData call)
    (cap J₁₁ J₁₂ J₂₁ J₂₂ : ℕ) (B radius : ℝ) where
  leftCoefficient : N.Label → ℝ
  rightCoefficient : N.Label → ℝ
  left_nonneg : ∀ b : N.Active, 0 ≤ leftCoefficient b.val
  right_nonneg : ∀ b : N.Active, 0 ≤ rightCoefficient b.val
  left_le : ∀ b : N.Active, leftCoefficient b.val ≤ B
  right_le : ∀ b : N.Active, rightCoefficient b.val ≤ B
  left_slots : ∀ b : N.Active, (N.family.leftSource b.val).allocation.keep.card ≤ cap
  right_slots : ∀ b : N.Active, (N.family.rightSource b.val).allocation.keep.card ≤ cap
  left_radius : ∀ (b : N.Active) z,
    (N.family.leftCapacity b.val).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius (enlargedCoefficient (leftCoefficient b.val) radius) J₁₁ J₁₂ z
  right_radius : ∀ (b : N.Active) z,
    (N.family.rightCapacity b.val).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius (enlargedCoefficient (rightCoefficient b.val) radius) J₂₁ J₂₂ z

namespace KernelRadiusData

variable {N : NormalizedData call} {cap J₁₁ J₁₂ J₂₁ J₂₂ : ℕ} {B radius : ℝ}
variable (D : KernelRadiusData N cap J₁₁ J₁₂ J₂₁ J₂₂ B radius)

/-- This is exactly the density in the original normalized kernel. -/
def envelope (b : N.Active) (z : ℝ × ℝ) : ℝ :=
  pairedProfileEnvelope
    (enlargedCoefficient (D.leftCoefficient b.val) radius)
    (enlargedCoefficient (D.rightCoefficient b.val) radius)
    (N.family.leftSource b.val).allocation.keep.card
    (N.family.rightSource b.val).allocation.keep.card J₁₁ J₁₂ J₂₁ J₂₂ z


end KernelRadiusData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
