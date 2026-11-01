import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAtomCosts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralScaleProduct
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralGaussScale
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralMassProfilePower

/-!
# Original per-occurrence windows of an actual literal table

The direct, main and valuation constructors produce this record from
the original profile window, original domain and prime support in
`(1, 2)`. Its frozen ideal is the complete first extraction ideal,
including the valuation power when present.

The record contains only individual occurrence and scale statements.
The Boolean is the original centered flag, so the scale statement is
used only on rectangles present in that original source. The second
slot cost is independent of the annulus and is the fixed
`max 1 bound^2`; the first scalar pair is estimated separately.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms

open NumberField

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

/-- Computed original windows for this precise literal table. This is
an output of the actual source constructors, before any normalized
child, allocation or kernel weight is selected. -/
structure OriginalWeightWindows (d : Atoms (K := K) k)
    (centered : Bool) (cap : ℕ) (bound annulus base total : ℝ)
    (firstFrozen : Ideal (𝓞 K)) : Prop where
  slots : k ≤ cap
  prime_atoms : ∀ i p, d.primeAtomCost i p ≤
    CanonicalLiteralMassProfilePower.slotBudget bound
  prime_norm : d.PrimeNormWindow annulus
  present_scale : ∀ r, r = false ∨ centered = true →
    d.scaleProduct r * (Ideal.absNorm firstFrozen : ℝ) ≤
      annulus ^ cap * base ^ total
  gauss_lower : base ^ (total - idealLogLength base firstFrozen) ≤ d.gaussScale

namespace OriginalWeightWindows

variable {d : Atoms (K := K) k} {centered : Bool} {cap : ℕ}
variable {bound annulus base total : ℝ} {firstFrozen : Ideal (𝓞 K)}

theorem atomBound_one
    (_W : d.OriginalWeightWindows centered cap bound annulus base total firstFrozen) :
    1 ≤ CanonicalLiteralMassProfilePower.slotBudget bound :=
  CanonicalLiteralMassProfilePower.slotBudget_one bound

end OriginalWeightWindows
end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.OriginalWeightWindows.atomBound_one
