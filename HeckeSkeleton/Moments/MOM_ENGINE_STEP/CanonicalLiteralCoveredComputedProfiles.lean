import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFullKappaInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualProfiles

/-!
# Computed profiles on the same second covered occurrence

The original direct, main and pool constructors compute their profile
coefficients before the second extraction. This file transports those
same computed values through the stored second occurrence and residual
atlas. The first scalar and first balance remain fixed; no profile
bound, whole-source identity or new choice of representative is input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralActualProfiles CanonicalLiteralFullKappaInput

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

local instance canonicalLiteralCoveredComputedProfilesCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)
variable {excluded : Finset (Ideal (𝓞 K))} {window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {bound : ℝ}

def literalLeftComputedProfiles
    (d : CanonicalLiteralRectangles.Atoms (K := K) (LC.branch v.2.2.1).slotCount)
    (E : ProfileSupport d excluded)
    (hleft : v.literalLeftParent.reindex.plain₁ = d.plain₁)
    (hright : v.literalLeftParent.reindex.plain₂ = d.plain₂)
    (hslot : ∀ i, v.literalLeftParent.reindex.slots i = d.slots i)
    (scalar : ℂ) (balance : Bool → ℝ)
    (T : ComputedProfiles ((E.profiles.scale scalar⁻¹).balancePlain balance)
      window orders bound) :
    ComputedProfiles
      ((((v.literalLeftProfileSupport d E hleft hright hslot).profiles).scale scalar⁻¹)
        .balancePlain balance) window orders bound :=
  ((T.onAtlasThenScaleBalance scalar⁻¹ balance v.literalLeftParent rfl)
    .extractThenScaleBalance scalar⁻¹ balance v.literalLeftBranch)
      .onAtlasThenScaleBalance scalar⁻¹ balance v.literalLeftResidualAtlas rfl

def literalRightComputedProfiles
    (d : CanonicalLiteralRectangles.Atoms (K := K) (RC.branch v.2.2.2.1).slotCount)
    (E : ProfileSupport d excluded)
    (hleft : v.literalRightParent.reindex.plain₁ = d.plain₁)
    (hright : v.literalRightParent.reindex.plain₂ = d.plain₂)
    (hslot : ∀ i, v.literalRightParent.reindex.slots i = d.slots i)
    (scalar : ℂ) (balance : Bool → ℝ)
    (T : ComputedProfiles ((E.profiles.scale scalar⁻¹).balancePlain balance)
      window orders bound) :
    ComputedProfiles
      ((((v.literalRightProfileSupport d E hleft hright hslot).profiles).scale scalar⁻¹)
        .balancePlain balance) window orders bound :=
  ((T.onAtlasThenScaleBalance scalar⁻¹ balance v.literalRightParent rfl)
    .extractThenScaleBalance scalar⁻¹ balance v.literalRightBranch)
      .onAtlasThenScaleBalance scalar⁻¹ balance v.literalRightResidualAtlas rfl

@[simp] theorem literalLeftComputedProfiles_bound
    (d : CanonicalLiteralRectangles.Atoms (K := K) (LC.branch v.2.2.1).slotCount)
    (E : ProfileSupport d excluded)
    (hleft : v.literalLeftParent.reindex.plain₁ = d.plain₁)
    (hright : v.literalLeftParent.reindex.plain₂ = d.plain₂)
    (hslot : ∀ i, v.literalLeftParent.reindex.slots i = d.slots i)
    (scalar : ℂ) (balance : Bool → ℝ)
    (T : ComputedProfiles ((E.profiles.scale scalar⁻¹).balancePlain balance)
      window orders bound) (r : Bool) :
    (v.literalLeftComputedProfiles d E hleft hright hslot scalar balance T).bound r =
      T.bound r := rfl

@[simp] theorem literalRightComputedProfiles_bound
    (d : CanonicalLiteralRectangles.Atoms (K := K) (RC.branch v.2.2.2.1).slotCount)
    (E : ProfileSupport d excluded)
    (hleft : v.literalRightParent.reindex.plain₁ = d.plain₁)
    (hright : v.literalRightParent.reindex.plain₂ = d.plain₂)
    (hslot : ∀ i, v.literalRightParent.reindex.slots i = d.slots i)
    (scalar : ℂ) (balance : Bool → ℝ)
    (T : ComputedProfiles ((E.profiles.scale scalar⁻¹).balancePlain balance)
      window orders bound) (r : Bool) :
    (v.literalRightComputedProfiles d E hleft hright hslot scalar balance T).bound r =
      T.bound r := rfl

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalLeftComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalRightComputedProfiles
