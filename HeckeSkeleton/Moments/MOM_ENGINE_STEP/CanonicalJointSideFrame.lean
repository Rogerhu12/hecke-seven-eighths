import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalJointAllocatedSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondClassProduction

/-!
# The original side frame with both Fourier locations

The same zero-mode rectangle frame is presented on the Hilbert product.
The first location is oriented before the right-side conjugation, so the
actual source has precisely the two coordinates already used by the joint
source constructor. No coefficient, normalization or allocation changes.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι U V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k : ℕ}

namespace SecondColumnSide

def orientFirstLocation (side : SecondColumnSide) (u : U) : U :=
  match side with
  | .left => u
  | .right => -u

end SecondColumnSide

namespace SecondSideFrame

variable (f : SecondSideFrame (V := V) C R Ray side k)
variable (x₁ x₂ : H → NonzeroIdeal K → U)
variable (x : H → Fin k → HeightOneSpectrum (𝓞 K) → U)

/-- The original second frame and its two actual first-mode locations
are fixed before both Fourier variables and before any slot removal. -/
def jointFrame : SecondSideFrame (V := WithLp 2 (U × V)) C R Ray side k where
  allocation := f.allocation
  characters := f.characters
  phaseCharacter := f.phaseCharacter
  dictionary := f.dictionary
  base_gt_one := f.base_gt_one
  length_pos := f.length_pos
  ideal := f.ideal
  ideal_product := f.ideal_product
  gaussScale₁ := f.gaussScale₁
  gaussScale₂ := f.gaussScale₂
  gaussSlotScale := f.gaussSlotScale
  gaussScale₁_pos := f.gaussScale₁_pos
  gaussScale₂_pos := f.gaussScale₂_pos
  gaussSlotScale_pos := f.gaussSlotScale_pos
  leftLocation h I := WithLp.toLp 2 (side.orientFirstLocation (x₁ h I), f.leftLocation h I)
  rightLocation h I := WithLp.toLp 2 (side.orientFirstLocation (x₂ h I), f.rightLocation h I)
  slotLocation h j p := WithLp.toLp 2 (side.orientFirstLocation (x h j p), f.slotLocation h j p)

@[simp] theorem jointFrame_normalizer :
    (f.jointFrame x₁ x₂ x).normalizer = f.normalizer := rfl

@[simp] theorem jointFrame_normalizationScale :
    (f.jointFrame x₁ x₂ x).normalizationScale = f.normalizationScale := rfl

/-- This is an equality of the complete actual source records,
including the negative right frequency and the chosen extracted row. -/
theorem jointFrame_source :
    (f.jointFrame x₁ x₂ x).source =
      CanonicalJointAllocatedSource.jointSource f.source
        (fun h => x₁ h.val) (fun h => x₂ h.val) (fun h => x h.val) := by
  cases side <;>
    simp only [jointFrame, source, rawSource, ActualSecondCorrelationRows.source,
      ActualAllocatedSource.negativeSide, CanonicalJointAllocatedSource.jointSource,
      SecondColumnSide.orientFirstLocation, ← WithLp.toLp_neg, Prod.neg_mk, neg_neg]

/-- The original Gauss normalizer is paid once on the unchanged
joint source, as in the single-mode source identity. -/
theorem jointFrame_energy (ξ : WithLp 2 (U × V)) :
    (f.jointFrame x₁ x₂ x).energy ξ =
      ‖f.normalizer‖ ^ 2 *
        (CanonicalJointAllocatedSource.jointSource f.source
          (fun h => x₁ h.val) (fun h => x₂ h.val) (fun h => x h.val)).energy (σ := σ) ξ := by
  rw [(f.jointFrame x₁ x₂ x).energy_eq_source, f.jointFrame_source,
    f.jointFrame_normalizer]

end SecondSideFrame
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.jointFrame_source
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.jointFrame_energy
