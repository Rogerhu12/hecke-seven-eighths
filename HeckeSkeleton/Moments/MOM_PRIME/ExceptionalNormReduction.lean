import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalContinuation
import HeckeGeneral.Characters.RadialNormalization
import HeckeGeneral.Analysis.MomentInputs

/-!
# Norm reduction for fixed backgrounds and plain rows

Canonical radial normalization and finite-order twists provide the analytic
principal-or-nonnorm alternative. These results use the original `MomentData`
interface without importing the physical source construction.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField HeckeGeneral.Characters HeckeGeneral.Arithmetic
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

theorem exceptionalNormReduced_of_radial_zero
    (w : InfinitePlace K) (χ : HeckeCharacter K)
    (hχ : heckeRadialParameter K w χ = 0) : ExceptionalNormReduced K χ := by
  by_cases h : χ = 1
  · exact Or.inl h
  · exact Or.inr (ne_normTwist_of_radial_zero K w χ hχ h)

/-- Canonical removal of a norm twist supplies the analytic alternative
without imposing an additional restriction on the original character. -/
theorem exceptionalNormReduced_radialNormalization
    (w : InfinitePlace K) (χ : HeckeCharacter K) :
    ExceptionalNormReduced K (radialNormalization K w χ) :=
  exceptionalNormReduced_of_radial_zero K w _
    (radialParameter_radialNormalization K w χ)

/-- The finite background family in Lemma 4.11 remains norm-reduced after
the canonical normalization of its fixed generator. -/
theorem exceptionalNormReduced_normalized_finite_background
    (w : InfinitePlace K) (ω θ : HeckeCharacter K) (hθ : FiniteOrder θ) :
    ExceptionalNormReduced K (radialNormalization K w ω * θ) :=
  exceptionalNormReduced_of_radial_zero K w _
    (radial_zero_mul_finiteOrder K w (radialNormalization K w ω) θ
      (radialParameter_radialNormalization K w ω) hθ)

/-- Finite-order row twists preserve the normalized slice for all three
plain backgrounds allowed by the original `MomentData` definition. -/
theorem exceptionalNormReduced_plain_row
    {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
    (w : InfinitePlace K) (hψ : heckeRadialParameter K w ψ = 0)
    (u : NonzeroIdeal K) :
    ExceptionalNormReduced K (d.plainBackground * d.rowCharacter u) := by
  have hbackground : heckeRadialParameter K w d.plainBackground = 0 := by
    rcases d.plain_background_spec with h | h | h
    · rw [h]
      simp
    · simpa only [h] using hψ
    · rw [h, heckeRadialParameter_inv, hψ, neg_zero]
  exact exceptionalNormReduced_of_radial_zero K w _
    (radial_zero_mul_finiteOrder K w d.plainBackground (d.rowCharacter u)
      hbackground (d.rowCharacter_finite u))

end HeckeSkeleton.Moments.MOM_PRIME
