import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalParentWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDirectParentWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalOuterScalar

/-!
# Exact original parent weights after the first scalar extraction

The original canonical normalization and the actual dependent source
label determine the first allowance, two divisors and two phases. The
second common atoms remain in the row mass. The norm of the first scalar
pair multiplies only the original first Poisson profile, ready for the
six actual combined-profile estimates.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local instance canonicalExceptionalParentWeightsCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

namespace ActualDirectFirstSource.SecondStages

variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)
variable (hZ : 1 < Z)
variable (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)

/-- Both original kernels and every arithmetic label are retained.
Only the first scalar pair moves outside its actual two whole columns. -/
theorem stripOuter_parentLeaf_weight_original_relative
    (exceptional : R.CoverHybridPredicates L) (parentWidth : ℝ)
    (j : R.CoveredLeafKey L)
    (extract :
      (R.parentLeaf L exceptional (s.canonicalNormalization hZ total) j).ConstantAtomExtraction)
    (leftScalar rightScalar : ℂ) (hleftScalar : leftScalar ≠ 0)
    (hrightScalar : rightScalar ≠ 0) :
    (extract.stripOuter leftScalar rightScalar hleftScalar hrightScalar).weight /
        Z ^ parentWidth =
      R.originalScalarAt L j *
        ((firstOriginalAllowanceWeight Z parentWidth (total j.1 j.2.1)
          (s.pieces j.1 j.2.1).weightBound j.1.val.1 j.1.val.2 *
          (‖leftScalar‖ * ‖rightScalar‖)) *
          ‖(moebius j.2.2.1.val : ℂ)‖ *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) j.2.2.2.1‖ *
          ‖(moebius (R.innerDivisor L j) : ℂ)‖ *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle))
            (R.secondPhaseAt L j)‖) /
        R.firstAllowanceAt L total j := by
  rw [extract.stripOuter_weight]
  calc
    _ = (‖leftScalar‖ * ‖rightScalar‖) *
        ((R.parentLeaf L exceptional (s.canonicalNormalization hZ total) j).weight /
          Z ^ parentWidth) := by ring
    _ = _ := by
      rw [R.parentLeaf_weight_original_relative L hZ total exceptional parentWidth j]
      ring

end ActualDirectFirstSource.SecondStages

namespace ActualFirstSource.SecondStages

variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)
variable (hZ : 1 < Z)
variable (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)

/-- Both original kernels and every arithmetic label are retained.
Only the first scalar pair moves outside its actual two whole columns. -/
theorem stripOuter_parentLeaf_weight_original_relative
    (exceptional : R.CoverHybridPredicates L) (parentWidth : ℝ)
    (j : R.CoveredLeafKey L)
    (extract :
      (R.parentLeaf L exceptional (s.canonicalNormalization hZ total) j).ConstantAtomExtraction)
    (leftScalar rightScalar : ℂ) (hleftScalar : leftScalar ≠ 0)
    (hrightScalar : rightScalar ≠ 0) :
    (extract.stripOuter leftScalar rightScalar hleftScalar hrightScalar).weight /
        Z ^ parentWidth =
      R.originalScalarAt L j *
        ((firstOriginalAllowanceWeight Z parentWidth (total j.1 j.2.1)
          (s.pools j.1 j.2.1).weightBound j.1.val.1 j.1.val.2 *
          (‖leftScalar‖ * ‖rightScalar‖)) *
          ‖(moebius j.2.2.1.val : ℂ)‖ *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) j.2.2.2.1‖ *
          ‖(moebius (R.innerDivisor L j) : ℂ)‖ *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle))
            (R.secondPhaseAt L j)‖) /
        R.firstAllowanceAt L total j := by
  rw [extract.stripOuter_weight]
  calc
    _ = (‖leftScalar‖ * ‖rightScalar‖) *
        ((R.parentLeaf L exceptional (s.canonicalNormalization hZ total) j).weight /
          Z ^ parentWidth) := by ring
    _ = _ := by
      rw [R.parentLeaf_weight_original_relative L hZ total exceptional parentWidth j]
      ring

end ActualFirstSource.SecondStages

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.stripOuter_parentLeaf_weight_original_relative
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.stripOuter_parentLeaf_weight_original_relative
