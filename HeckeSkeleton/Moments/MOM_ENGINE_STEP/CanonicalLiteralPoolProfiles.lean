import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolAtoms

/-!
# Computed smooth profiles and supports for the actual pooled tables

The existing literal source tables are preserved. The original window
and one original paired row supply their tests and supports through the
same original extraction, transform and atlas maps as their definitions.
No final profile/support certificate or aggregate estimate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
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

open CanonicalLiteralActualProfiles

variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {bound : ℝ}
variable (originalWindow : RawProfileWindow rowDomain heightDomain window seminorms
  (data ξ) bound)
variable (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
variable (hwindow : window ⊆ Set.Ioi 0)

/-- Both certificates are constructed from the original row and window
on the existing left main atom table. -/
def literalLeftMainProfileSupport
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.leftSourceCovers (raw).originalAtlas S χ).main.labels) :
    ProfileSupport
      (literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
        b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        firstFixed hfirst δ₂ label)
      (primeSupport A.cS ∪ (primeSupport DE.1)) := by
  let initial := Q.literalOriginalProfileSupport ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    reference href originalWindow hreference ht hwindow
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.1 label
  let transformed := initial.secondInput (σ := σ) branch P R (fun _ hp => support_prime hp)
    (unitExterior A) firstFixed (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  have e := literalLeftMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  exact (transformed.onAtlas ((p.leftSourceCovers (raw).originalAtlas S χ).main.branch label) _ e).deleteMask
    (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))

/-- Both certificates are constructed from the original row and window
on the existing right main atom table. -/
def literalRightMainProfileSupport
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.rightSourceCovers (raw).originalAtlas S χ).main.labels) :
    ProfileSupport
      (literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
        b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        firstFixed hfirst δ₂ label)
      (primeSupport A.cS ∪ (primeSupport DE.1)) := by
  let initial := Q.literalOriginalProfileSupport ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    reference href originalWindow hreference ht hwindow
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.2 label
  let transformed := initial.secondInput (σ := σ) branch P R (fun _ hp => support_prime hp)
    (unitExterior A) firstFixed (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  have e := literalRightMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  exact (transformed.onAtlas ((p.rightSourceCovers (raw).originalAtlas S χ).main.branch label) _ e).deleteMask
    (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))

/-- Both certificates are constructed from the original row and window
on the existing left pool atom table. -/
def literalLeftPoolProfileSupport
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).labels) :
    ProfileSupport
      (literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
        b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        firstFixed hfirst δ₂ q n label)
      (primeSupport A.cS ∪ (primeSupport DE.1 ∪ {q.val.val.asIdeal})) := by
  let initial := Q.literalOriginalProfileSupport ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    reference href originalWindow hreference ht hwindow
  let branch := (p.divisorPools.leftData S).combinedBranchForLabel (raw).originalAtlas
    (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label
  have hfirstSupport : ∀ J ∈ (primeSupport DE.1 ∪ {q.val.val.asIdeal}), Prime J := by
    intro J hJ
    rcases Finset.mem_union.mp hJ with hJ | hJ
    · exact support_prime hJ
    · rcases Finset.mem_singleton.mp hJ with rfl
      exact q.val.val.prime
  let transformed := initial.secondInput (σ := σ) branch P R hfirstSupport
    (powerIdeal q.val n) firstFixed (powerIdeal q.val (2 * n)) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q.val ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q.val (2 * n))
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  have e := literalLeftPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  exact (transformed.onAtlas (((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label) _ e).deleteMask
    (literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) hfirstSupport)

/-- Both certificates are constructed from the original row and window
on the existing right pool atom table. -/
def literalRightPoolProfileSupport
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).labels) :
    ProfileSupport
      (literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
        b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        firstFixed hfirst δ₂ q n label)
      (primeSupport A.cS ∪ (primeSupport DE.1 ∪ {q.val.val.asIdeal})) := by
  let initial := Q.literalOriginalProfileSupport ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    reference href originalWindow hreference ht hwindow
  let branch := (p.divisorPools.rightData S).combinedBranchForLabel (raw).originalAtlas
    (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label
  have hfirstSupport : ∀ J ∈ (primeSupport DE.1 ∪ {q.val.val.asIdeal}), Prime J := by
    intro J hJ
    rcases Finset.mem_union.mp hJ with hJ | hJ
    · exact support_prime hJ
    · rcases Finset.mem_singleton.mp hJ with rfl
      exact q.val.val.prime
  let transformed := initial.secondInput (σ := σ) branch P R hfirstSupport
    (powerIdeal q.val n) firstFixed (powerIdeal q.val (2 * n)) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q.val ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q.val (2 * n))
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  have e := literalRightPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  exact (transformed.onAtlas (((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label) _ e).deleteMask
    (literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) hfirstSupport)

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainProfileSupport
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainProfileSupport
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolProfileSupport
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolProfileSupport
