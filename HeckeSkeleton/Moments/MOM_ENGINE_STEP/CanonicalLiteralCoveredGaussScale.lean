import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralGaussScale
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCoveredLeaf

/-!
# The stored covered leaf retains its original Gauss lower scale

These identities follow the existing covered occurrence indices. The
second common extraction, atlas transport and exact removal of column
constants preserve the complete first-stage Gauss product. The actual
frame therefore consumes the original direct/main/pool lower bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum
open WholeAllocation

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

local instance canonicalLiteralCoveredGaussScaleCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)

variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)

/-- The stored second common extraction preserves the complete left
Gauss product, including every removed occurrence. -/
@[simp] theorem literalLeftAtoms_gaussScale :
    (v.literalLeftAtoms leftAtoms).gaussScale = leftAtoms.gaussScale := by
  simp only [literalLeftAtoms, literalLeftOriginal,
    CanonicalLiteralRectangles.Atoms.gaussScale_onAtlas,
    CanonicalLiteralRectangles.Atoms.gaussScale_extract]

/-- The right stored atlas has the same exact preservation; no second
common ideal norm is divided out of the Gauss scale. -/
@[simp] theorem literalRightAtoms_gaussScale :
    (v.literalRightAtoms rightAtoms).gaussScale = rightAtoms.gaussScale := by
  simp only [literalRightAtoms, literalRightOriginal,
    CanonicalLiteralRectangles.Atoms.gaussScale_onAtlas,
    CanonicalLiteralRectangles.Atoms.gaussScale_extract]

@[simp] theorem literalLeftStripped_gaussScale (scalar : ℂ) (balance : Bool → ℝ) :
    (((v.literalLeftAtoms leftAtoms).scale scalar⁻¹).balancePlain balance).gaussScale =
      leftAtoms.gaussScale := by
  rw [CanonicalLiteralRectangles.Atoms.gaussScale_balancePlain,
    CanonicalLiteralRectangles.Atoms.gaussScale_scale, v.literalLeftAtoms_gaussScale]

@[simp] theorem literalRightStripped_gaussScale (scalar : ℂ) (balance : Bool → ℝ) :
    (((v.literalRightAtoms rightAtoms).scale scalar⁻¹).balancePlain balance).gaussScale =
      rightAtoms.gaussScale := by
  rw [CanonicalLiteralRectangles.Atoms.gaussScale_balancePlain,
    CanonicalLiteralRectangles.Atoms.gaussScale_scale, v.literalRightAtoms_gaussScale]

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalLeftAtoms_gaussScale
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalRightAtoms_gaussScale
