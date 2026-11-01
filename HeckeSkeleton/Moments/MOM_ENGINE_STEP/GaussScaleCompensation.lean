import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondBranchProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedChildKernel

/-!
# Explicit compensation for the original prime annuli

An original prime support may extend below its formal central scale.
The exact residual Gauss product then has the fixed annulus loss proved
in OriginalGaussScaleProduction. For applying the exact scalar-budget
lemma, enlarge one extra Gauss scale on each Cauchy side by that same
positive factor. This is only an auxiliary frame used in the proof:
its allocated source is definitionally the original source, and the
same normalized children are used throughout.

The original pair weight is exactly the compensation factor times the
auxiliary pair weight. Thus the factor remains visible in the actual
family's mass estimate, instead of assuming an invalid lossless window.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]

namespace SecondSideFrame

variable {side : SecondColumnSide} {k : ℕ}
variable (f : SecondSideFrame (V := V) C R Ray side k)

/-- An auxiliary normalization of the same original allocated source.
No arithmetic atom, support, location, base, slot or length is changed. -/
def compensatedGauss (factor : ℝ) (hfactor : 0 < factor) :
    SecondSideFrame (V := V) C R Ray side k :=
  { f with
    gaussScale₁ := factor * f.gaussScale₁
    gaussScale₁_pos := mul_pos hfactor f.gaussScale₁_pos }

theorem compensatedGauss_source (factor : ℝ) (hfactor : 0 < factor) :
    (f.compensatedGauss factor hfactor).source = f.source := rfl

theorem compensatedGauss_normalizationScale (factor : ℝ) (hfactor : 0 < factor) :
    (f.compensatedGauss factor hfactor).normalizationScale = factor * f.normalizationScale := by
  unfold normalizationScale extraGaussScale compensatedGauss
  ring

end SecondSideFrame

section Pair

variable {k l : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)

theorem frame_pair_normalizer_norm :
    ‖left.normalizer‖ * ‖right.normalizer‖ =
      1 / (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) :=
  extraGaussNormalizer_pair_norm left.gaussScale₁ left.gaussScale₂
    right.gaussScale₁ right.gaussScale₂ left.gaussSlotScale right.gaussSlotScale
    left.gaussScale₁_pos left.gaussScale₂_pos left.gaussSlotScale_pos
    right.gaussScale₁_pos right.gaussScale₂_pos right.gaussSlotScale_pos

/-- The compensation is paid exactly once after the paired square
roots. This identity concerns the original complex normalizers. -/
theorem compensatedGauss_pair_normalizer_norm (factor : ℝ) (hfactor : 0 < factor) :
    ‖left.normalizer‖ * ‖right.normalizer‖ = factor *
      (‖(left.compensatedGauss factor hfactor).normalizer‖ *
        ‖(right.compensatedGauss factor hfactor).normalizer‖) := by
  rw [frame_pair_normalizer_norm, frame_pair_normalizer_norm,
    SecondSideFrame.compensatedGauss_normalizationScale,
    SecondSideFrame.compensatedGauss_normalizationScale,
    Real.sqrt_mul hfactor.le, Real.sqrt_mul hfactor.le]
  have hs : Real.sqrt factor * Real.sqrt factor = factor := by
    nlinarith [Real.sq_sqrt hfactor.le]
  have hden :
      (Real.sqrt factor * Real.sqrt left.normalizationScale) *
        (Real.sqrt factor * Real.sqrt right.normalizationScale) =
      factor * (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) := by
    calc
      _ = (Real.sqrt factor * Real.sqrt factor) *
          (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) := by ring
      _ = _ := by rw [hs]
  rw [hden]
  calc
    _ = (factor * 1) /
        (factor * (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)) :=
      (mul_div_mul_left 1
        (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) hfactor.ne').symm
    _ = _ := mul_div_assoc _ _ _

variable {ω ψ : HeckeCharacter K}
variable {DL : left.source.Calibration (σ := σ) ω ψ}
variable {DR : right.source.Calibration (σ := σ) ω ψ}
variable {«GL» : DL.NormalizedCapacityData} {GR : DR.NormalizedCapacityData}

/-- The actual normalized children and all their weights are retained.
Only the two explicit original Gauss normalizers are rewritten. -/
theorem normalizedCapacityPairWeight_compensatedGauss
    (lc : «GL».Child) (rc : GR.Child) (factor : ℝ) (hfactor : 0 < factor)
    (Z parentWidth : ℝ) :
    normalizedCapacityPairWeight lc rc left.normalizer right.normalizer Z parentWidth =
      factor * normalizedCapacityPairWeight lc rc
        (left.compensatedGauss factor hfactor).normalizer
        (right.compensatedGauss factor hfactor).normalizer Z parentWidth := by
  unfold normalizedCapacityPairWeight
  rw [compensatedGauss_pair_normalizer_norm left right factor hfactor]
  ring

end Pair
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.compensatedGauss_source
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.compensatedGauss_normalizationScale
#print axioms HeckeSkeleton.Moments.EngineStep.compensatedGauss_pair_normalizer_norm
#print axioms HeckeSkeleton.Moments.EngineStep.normalizedCapacityPairWeight_compensatedGauss
