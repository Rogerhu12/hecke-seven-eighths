import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalOriginalSideFactory
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectFactorFreeComputed
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectCharacters

/-!
# The actual exceptional sides of the two direct first branches

The original direct cover dictionary transports each original occurrence
branch into the same first atlas. Its stored second branch and stored
allocation then construct both exceptional sides. Original raw profiles
supply their factor-free representatives and uniform seminorm bounds.

The actual stage and live leaf are retained. No normalization data,
capacity certificate, finished source bound or new allocation is an input.
-/

set_option autoImplicit false
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
local notation "raw" => original.raw Y₁ Y₂
local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
local notation "c" => (original.values Y₁ Y₂).coefficient centered

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
variable {M : Finset (HeightOneSpectrum A.R)} {cutoff : ℝ} {hcutoff : 1 ≤ cutoff}
variable (p : FirstBlockDirectData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns φ
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half) M cutoff hcutoff)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (δ₂ : ℝ)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (orders : Finset (ℕ × ℕ)) (amplitude : ℝ) (hamplitude : 0 ≤ amplitude)
variable (originalWindow : RawProfileWindow rowDomain heightDomain window
  (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
    (data ξ) amplitude)
variable (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (hprime : ∀ i, Function.support (originalWindow.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)

section LeftDirectExceptionalSides

local notation "cover" => p.leftSourceCover raw.originalAtlas S χ
local notation "firstPoint" => (fun i => -Real.log (A.exteriorNorm (b.leftResidual i)))
variable {stage : ActualGaussStage (E := ℝ) hΓ μv hDiff
  (p.leftData.directSource (p.leftDivisorCoefficient S χ)) finiteTest}
variable (v : stage.CoveredClassKey
  (p.leftSourceCover raw.originalAtlas S χ) (p.leftSourceCover raw.originalAtlas S χ))
variable (exceptional : stage.CoverHybridPredicates
  (p.leftSourceCover raw.originalAtlas S χ) (p.leftSourceCover raw.originalAtlas S χ))
variable (kernel : SchwartzMap ℝ ℂ) (j : v.AllocationKey)
variable (hlive : (v.leaf exceptional kernel firstPoint j).Live)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))

local notation "phases" => CanonicalLiteralActualCharacters.unamplifiedPhases firstFixed
  (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst
local notation "branchL" => raw.originalAtlas.branch (primeSupport DE.1) DE.1 v.2.2.1
local notation "branchR" => raw.originalAtlas.branch (primeSupport DE.1) DE.1 v.2.2.2.1

/-- Both sides use this exact stored allocation. The inequalities in
its returned result concern the original factor-free representatives. -/
def literalLeftDirectExceptionalSides :=
  let selected := v.literalAllocation exceptional kernel firstPoint j hlive
  let live := (Finset.mem_filter.mp selected.property).2
  let eL := literalLeftDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.1
  let eR := literalLeftDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.2.1
  let left := CanonicalLiteralExceptionalOriginalSideFactory.firstAtlasResult
    Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href orders amplitude hamplitude
    originalWindow hreference ht hcompact hpositive hprime branchL
    (fun _ hp => support_prime hp) phases (unitExterior A) δ₁ δ₂
    v.literalLeftParent (fun i => raw.originalIndex (branchL.reconstruct i)) eL
    v.literalLeftBranch (fun _ hp => support_prime hp) v.literalLeftResidualAtlas rfl
    (by
      change v.leftReindex.plain₁ = _
      rw [SourceCartesianAtlas.residualReindex_plain₁])
    (by
      change v.leftReindex.plain₂ = _
      rw [SourceCartesianAtlas.residualReindex_plain₂])
    (by
      intro i
      change v.leftReindex.slots i = _
      rw [SourceCartesianAtlas.residualReindex_slots])
    j.2.1 1 (by norm_num) j.1.val j.2.2.1.val live.2.1 live.1 j.2.2.1.property
  let right := CanonicalLiteralExceptionalOriginalSideFactory.firstAtlasResult
    Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href orders amplitude hamplitude
    originalWindow hreference ht hcompact hpositive hprime branchR
    (fun _ hp => support_prime hp) phases (unitExterior A) δ₁ δ₂
    v.literalRightParent (fun i => raw.originalIndex (branchR.reconstruct i)) eR
    v.literalRightBranch (fun _ hp => support_prime hp) v.literalRightResidualAtlas rfl
    (by
      change v.rightReindex.plain₁ = _
      rw [SourceCartesianAtlas.residualReindex_plain₁])
    (by
      change v.rightReindex.plain₂ = _
      rw [SourceCartesianAtlas.residualReindex_plain₂])
    (by
      intro i
      change v.rightReindex.slots i = _
      rw [SourceCartesianAtlas.residualReindex_slots])
    j.2.1 (-1) (by norm_num) j.1.val j.2.2.2.val live.2.2 live.1 j.2.2.2.property
  (left, right)

end LeftDirectExceptionalSides

section RightDirectExceptionalSides

local notation "cover" => p.rightSourceCover raw.originalAtlas S χ
local notation "firstPoint" => (fun i => -(-Real.log (A.exteriorNorm (b.rightResidual i))))
variable {stage : ActualGaussStage (E := ℝ) hΓ μv hDiff
  (p.rightData.directSource (p.rightDivisorCoefficient S χ)) finiteTest}
variable (v : stage.CoveredClassKey
  (p.rightSourceCover raw.originalAtlas S χ) (p.rightSourceCover raw.originalAtlas S χ))
variable (exceptional : stage.CoverHybridPredicates
  (p.rightSourceCover raw.originalAtlas S χ) (p.rightSourceCover raw.originalAtlas S χ))
variable (kernel : SchwartzMap ℝ ℂ) (j : v.AllocationKey)
variable (hlive : (v.leaf exceptional kernel firstPoint j).Live)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))

local notation "phases" => CanonicalLiteralActualCharacters.unamplifiedPhases firstFixed
  (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst
local notation "branchL" => raw.originalAtlas.branch (primeSupport DE.1) DE.2 v.2.2.1
local notation "branchR" => raw.originalAtlas.branch (primeSupport DE.1) DE.2 v.2.2.2.1

/-- Both sides use this exact stored allocation. The inequalities in
its returned result concern the original factor-free representatives. -/
def literalRightDirectExceptionalSides :=
  let selected := v.literalAllocation exceptional kernel firstPoint j hlive
  let live := (Finset.mem_filter.mp selected.property).2
  let eL := literalRightDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.1
  let eR := literalRightDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.2.1
  let left := CanonicalLiteralExceptionalOriginalSideFactory.firstAtlasResult
    Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href orders amplitude hamplitude
    originalWindow hreference ht hcompact hpositive hprime branchL
    (fun _ hp => support_prime hp) phases (unitExterior A) δ₁ δ₂
    v.literalLeftParent (fun i => raw.originalIndex (branchL.reconstruct i)) eL
    v.literalLeftBranch (fun _ hp => support_prime hp) v.literalLeftResidualAtlas rfl
    (by
      change v.leftReindex.plain₁ = _
      rw [SourceCartesianAtlas.residualReindex_plain₁])
    (by
      change v.leftReindex.plain₂ = _
      rw [SourceCartesianAtlas.residualReindex_plain₂])
    (by
      intro i
      change v.leftReindex.slots i = _
      rw [SourceCartesianAtlas.residualReindex_slots])
    j.2.1 (-1) (by norm_num) j.1.val j.2.2.1.val live.2.1 live.1 j.2.2.1.property
  let right := CanonicalLiteralExceptionalOriginalSideFactory.firstAtlasResult
    Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href orders amplitude hamplitude
    originalWindow hreference ht hcompact hpositive hprime branchR
    (fun _ hp => support_prime hp) phases (unitExterior A) δ₁ δ₂
    v.literalRightParent (fun i => raw.originalIndex (branchR.reconstruct i)) eR
    v.literalRightBranch (fun _ hp => support_prime hp) v.literalRightResidualAtlas rfl
    (by
      change v.rightReindex.plain₁ = _
      rw [SourceCartesianAtlas.residualReindex_plain₁])
    (by
      change v.rightReindex.plain₂ = _
      rw [SourceCartesianAtlas.residualReindex_plain₂])
    (by
      intro i
      change v.rightReindex.slots i = _
      rw [SourceCartesianAtlas.residualReindex_slots])
    j.2.1 1 (by norm_num) j.1.val j.2.2.2.val live.2.2 live.1 j.2.2.2.property
  (left, right)

end RightDirectExceptionalSides

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectExceptionalSides
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightDirectExceptionalSides
