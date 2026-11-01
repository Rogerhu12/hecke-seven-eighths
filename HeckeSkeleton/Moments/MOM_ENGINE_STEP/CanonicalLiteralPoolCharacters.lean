import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolAtoms

/-!
# Literal character and slot recipes of the actual main and pool tables

Every map is the original extraction map followed by the actual atlas
cast. The displayed character recipe includes all original moving
factors, the three actual fixed generated elements and the complete
first deletion. Its slot dictionary is constructed, not assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum
open MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

local notation "original" => (Q.arithmeticAtoms ξ).constantAtoms W a Z t
local notation "raw" => (original).raw Y₁ Y₂
local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
local notation "c" => ((original).values Y₁ Y₂).coefficient centered

variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock
  (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).columnExterior
  (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).columnExterior DE)
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
variable (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁half : δ₁ ≤ 1 / 2)
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z ell eps}
variable {M : Finset (HeightOneSpectrum A.R)} {cutoff : ℝ} {hcutoff : 1 ≤ cutoff}
variable (p : FirstBlockPoolData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns φ
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half) pool M cutoff hcutoff)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

open CanonicalLiteralActualCharacters

/-- Exact original characters and the injective occurrence dictionary
of the existing left main table, constructed before any child bound. -/
def literalLeftMainRecipe
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.leftSourceCovers (raw).originalAtlas S χ).main.labels) :
    Recipe P R (unamplifiedPhases firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst) (data ξ) Q.moving Q.correction Q.remaining
      (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))
      (literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
        b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        firstFixed hfirst δ₂ label) := by
  let F := unamplifiedPhases firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.1 label
  let extra := literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp)
  let original := Q.literalSecondInputRecipe (σ := σ) ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ branch F (unitExterior A) δ₁ δ₂ extra
  have e := literalLeftMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  have E := original.onAtlas ((p.leftSourceCovers (raw).originalAtlas S χ).main.branch label) (congrArg Sigma.fst e).symm
  simpa only [CanonicalLiteralRectangles.Atoms.deleteMask_onAtlas] using E

/-- Exact original characters and the injective occurrence dictionary
of the existing right main table, constructed before any child bound. -/
def literalRightMainRecipe
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.rightSourceCovers (raw).originalAtlas S χ).main.labels) :
    Recipe P R (unamplifiedPhases firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst) (data ξ) Q.moving Q.correction Q.remaining
      (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))
      (literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
        b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        firstFixed hfirst δ₂ label) := by
  let F := unamplifiedPhases firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.2 label
  let extra := literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp)
  let original := Q.literalSecondInputRecipe (σ := σ) ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ branch F (unitExterior A) δ₁ δ₂ extra
  have e := literalRightMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  have E := original.onAtlas ((p.rightSourceCovers (raw).originalAtlas S χ).main.branch label) (congrArg Sigma.fst e).symm
  simpa only [CanonicalLiteralRectangles.Atoms.deleteMask_onAtlas] using E

/-- Exact original characters and the injective occurrence dictionary
of the existing left pool table, constructed before any child bound. -/
def literalLeftPoolRecipe
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).labels) :
    Recipe P R (amplifiedPhases C firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst q.val n) (data ξ) Q.moving Q.correction Q.remaining
      (literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) (fun _ hp => by
          rcases Finset.mem_union.mp hp with hp | hp
          · exact support_prime hp
          · rcases Finset.mem_singleton.mp hp with rfl
            exact q.val.val.prime))
      (literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
        b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        firstFixed hfirst δ₂ q n label) := by
  let F := amplifiedPhases C firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst q.val n
  let branch := (p.divisorPools.leftData S).combinedBranchForLabel (raw).originalAtlas
    (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label
  let extra := literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) (fun _ hp => by
          rcases Finset.mem_union.mp hp with hp | hp
          · exact support_prime hp
          · rcases Finset.mem_singleton.mp hp with rfl
            exact q.val.val.prime)
  let original := Q.literalSecondInputRecipe (σ := σ) ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ branch F (powerIdeal q.val n) δ₁ δ₂ extra
  have e := literalLeftPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  have E := original.onAtlas (((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label) (congrArg Sigma.fst e).symm
  simpa only [CanonicalLiteralRectangles.Atoms.deleteMask_onAtlas] using E

/-- Exact original characters and the injective occurrence dictionary
of the existing right pool table, constructed before any child bound. -/
def literalRightPoolRecipe
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).labels) :
    Recipe P R (amplifiedPhases C firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst q.val n) (data ξ) Q.moving Q.correction Q.remaining
      (literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) (fun _ hp => by
          rcases Finset.mem_union.mp hp with hp | hp
          · exact support_prime hp
          · rcases Finset.mem_singleton.mp hp with rfl
            exact q.val.val.prime))
      (literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
        b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        firstFixed hfirst δ₂ q n label) := by
  let F := amplifiedPhases C firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst q.val n
  let branch := (p.divisorPools.rightData S).combinedBranchForLabel (raw).originalAtlas
    (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label
  let extra := literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) (fun _ hp => by
          rcases Finset.mem_union.mp hp with hp | hp
          · exact support_prime hp
          · rcases Finset.mem_singleton.mp hp with rfl
            exact q.val.val.prime)
  let original := Q.literalSecondInputRecipe (σ := σ) ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ branch F (powerIdeal q.val n) δ₁ δ₂ extra
  have e := literalRightPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  have E := original.onAtlas (((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label) (congrArg Sigma.fst e).symm
  simpa only [CanonicalLiteralRectangles.Atoms.deleteMask_onAtlas] using E

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainRecipe
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainRecipe
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolRecipe
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolRecipe
