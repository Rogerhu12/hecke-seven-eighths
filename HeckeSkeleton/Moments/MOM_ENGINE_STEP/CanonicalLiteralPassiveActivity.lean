import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveFrames
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralInactiveRectangle

/-!
# The absent ordinary rectangle in each passive frame

The complete smooth carrier and the passive occurrence allocation
preserve the original comparison gate in the left weight. Therefore
an ordinary comparison branch has zero energy on the actual new frame,
independently of cancellation in the source before passive deletion.
This supplies the original rectangle choice needed by the active
scale-product and radius estimates.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

namespace CanonicalLiteralPassiveFrames

open CanonicalLiteralPassiveSource

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k) (A : SArithmeticData K)
variable (paid : FixedChildCharacters K B.keep.card)
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (R : ActualSecondCorrelationRows A σ H ι) (side : SecondColumnSide)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })
variable (firstSign : ℝ)

/-- The right Fourier orientation also retains this same left
individual weight. -/
theorem frame_source_leftWeight (r : Bool) (h : R.live)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (frame W B A paid C R side M a firstSign r).source.leftWeight h I =
      (table W B A paid).rectangleLeftWeight r I := by
  cases side <;> rfl

theorem comparison_source_energy_zero (hordinary : d.centered = false)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    (frame W B A paid C R side M a firstSign true).source.energy (σ := σ) ξ = 0 := by
  apply ActualAllocatedSource.energy_zero_of_leftWeight
  intro h _ I
  rw [frame_source_leftWeight W B A paid C R side M a firstSign true h I]
  have ht : (table W B A paid).centered = false := hordinary
  simp [CanonicalLiteralRectangles.Atoms.rectangleLeftWeight, ht]

/-- This activity is the new passive branch's own source activity.
It excludes the ordinary comparison rectangle before a child or
normalization is chosen. -/
theorem active_rectangle (r : Bool)
    (hactive : ¬ ∀ ξ,
      (frame W B A paid C R side M a firstSign r).source.energy (σ := σ) ξ = 0) :
    r = false ∨ d.centered = true := by
  cases r with
  | false => exact Or.inl rfl
  | true =>
    cases hc : d.centered with
    | false =>
        exfalso
        apply hactive
        intro ξ
        exact comparison_source_energy_zero W B A paid C R side M a firstSign hc ξ
    | true => exact Or.inr (by simp only [hc])

end CanonicalLiteralPassiveFrames
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.frame_source_leftWeight
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.comparison_source_energy_zero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.active_rectangle
