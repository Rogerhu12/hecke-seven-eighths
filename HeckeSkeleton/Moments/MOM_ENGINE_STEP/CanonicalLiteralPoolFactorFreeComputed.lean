import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolComputedProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectFactorFreeComputed

/-!
# Computed profiles for the redistributed actual pool tables

Each constructor starts with the original parent window and the same
first extraction. The positive factor of every retained occurrence is
moved into the original first scalar before normalization. The complete
source is preserved by the proved redistribution identity.

The return value uses the actual atlas, its original full deletion,
the combined original scalar, and the identity plain balance. Every
Schwartz representative and bound is constructed internally. No child
window or whole-source estimate is an input.
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

variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (s : Finset (ℕ × ℕ)) (bound : ℝ) (hbound : 0 ≤ bound)
variable (originalWindow : RawProfileWindow rowDomain heightDomain window
  (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)) (data ξ) bound)
variable (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
variable (hcompact : IsCompact window) (hwindow : window ⊆ Set.Ioi 0)
variable (hprime : ∀ j, Function.support (originalWindow.primeRep j t) ⊆ Set.Ioo (1 : ℝ) 2)

/-- All profile data are constructed for this same actual table,
with the complete positive factor charged in its first scalar. -/
def literalLeftMainFactorFreeComputedProfiles
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : ((p.leftSourceCovers raw.originalAtlas S χ).main).labels) :
    let actual := literalLeftMainProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href originalWindow hreference ht hwindow
      firstFixed hfirst δ₂ label
    let atoms := literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label
    let scalar := literalLeftMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((((actual.redistributeNormFactors δ₁ δ₂).profiles).scale
        (scalar * (atoms.normProfileFactor δ₁ δ₂ : ℂ))⁻¹).balancePlain (fun _ => 1))
      window s bound := by
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.1 label
  let scalar := literalLeftMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  have hallowed : (data ξ).allowedRow reference :=
    (((data ξ).rows_spec _ reference).mp (Finset.mem_filter.mp href).1).1
  let initial := Q.literalFactorFreeComputedProfiles (σ := σ) ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ reference hallowed s bound hbound originalWindow hreference ht
    hcompact hwindow hprime branch (unitExterior A) firstFixed (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A) CanonicalLiteralFixedPhases.emptyDivisorInverse_generates
    δ₁ δ₂
  have e := literalLeftMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  exact (CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenRedistributeScale
    scalar δ₁ δ₂
    (CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenRedistributeScale
      scalar δ₁ δ₂ initial (((p.leftSourceCovers raw.originalAtlas S χ).main).branch label) (congrArg Sigma.fst e).symm)
    (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))).balanceOne

/-- The coefficient remains the explicit original seed bound,
before any Fourier variable or child is chosen. -/
theorem literalLeftMainFactorFreeComputedProfiles_bound
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : ((p.leftSourceCovers raw.originalAtlas S χ).main).labels) :
    (literalLeftMainFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href s bound hbound originalWindow hreference ht hcompact hwindow hprime
      firstFixed hfirst δ₂ label).bound =
      let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.1 label
      fun r => bound + bound * CanonicalLogProfiles.shapeCoefficient window hcompact hwindow
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s) *
          (1 + CanonicalLiteralBalancedSchwartz.factor seed branch δ₁ δ₂ r) := by
  unfold literalLeftMainFactorFreeComputedProfiles
  simp only [CanonicalLiteralFullKappaInput.ComputedProfiles.balanceOne_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenRedistributeScale_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenRedistributeScale_bound] <;> rfl

/-- All profile data are constructed for this same actual table,
with the complete positive factor charged in its first scalar. -/
def literalRightMainFactorFreeComputedProfiles
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : ((p.rightSourceCovers raw.originalAtlas S χ).main).labels) :
    let actual := literalRightMainProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href originalWindow hreference ht hwindow
      firstFixed hfirst δ₂ label
    let atoms := literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label
    let scalar := literalRightMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((((actual.redistributeNormFactors δ₁ δ₂).profiles).scale
        (scalar * (atoms.normProfileFactor δ₁ δ₂ : ℂ))⁻¹).balancePlain (fun _ => 1))
      window s bound := by
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.2 label
  let scalar := literalRightMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  have hallowed : (data ξ).allowedRow reference :=
    (((data ξ).rows_spec _ reference).mp (Finset.mem_filter.mp href).1).1
  let initial := Q.literalFactorFreeComputedProfiles (σ := σ) ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ reference hallowed s bound hbound originalWindow hreference ht
    hcompact hwindow hprime branch (unitExterior A) firstFixed (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A) CanonicalLiteralFixedPhases.emptyDivisorInverse_generates
    δ₁ δ₂
  have e := literalRightMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  exact (CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenRedistributeScale
    scalar δ₁ δ₂
    (CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenRedistributeScale
      scalar δ₁ δ₂ initial (((p.rightSourceCovers raw.originalAtlas S χ).main).branch label) (congrArg Sigma.fst e).symm)
    (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))).balanceOne

/-- The coefficient remains the explicit original seed bound,
before any Fourier variable or child is chosen. -/
theorem literalRightMainFactorFreeComputedProfiles_bound
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : ((p.rightSourceCovers raw.originalAtlas S χ).main).labels) :
    (literalRightMainFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href s bound hbound originalWindow hreference ht hcompact hwindow hprime
      firstFixed hfirst δ₂ label).bound =
      let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.2 label
      fun r => bound + bound * CanonicalLogProfiles.shapeCoefficient window hcompact hwindow
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s) *
          (1 + CanonicalLiteralBalancedSchwartz.factor seed branch δ₁ δ₂ r) := by
  unfold literalRightMainFactorFreeComputedProfiles
  simp only [CanonicalLiteralFullKappaInput.ComputedProfiles.balanceOne_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenRedistributeScale_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenRedistributeScale_bound] <;> rfl

/-- All profile data are constructed for this same actual table,
with the complete positive factor charged in its first scalar. -/
def literalLeftPoolFactorFreeComputedProfiles
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers raw.originalAtlas S χ).residual q n).labels) :
    let actual := literalLeftPoolProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href originalWindow hreference ht hwindow
      firstFixed hfirst δ₂ q n label
    let atoms := literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ q n label
    let scalar := literalLeftPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((((actual.redistributeNormFactors δ₁ δ₂).profiles).scale
        (scalar * (atoms.normProfileFactor δ₁ δ₂ : ℂ))⁻¹).balancePlain (fun _ => 1))
      window s bound := by
  let branch := (p.divisorPools.leftData S).combinedBranchForLabel raw.originalAtlas
    (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label
  let scalar := literalLeftPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  have hallowed : (data ξ).allowedRow reference :=
    (((data ξ).rows_spec _ reference).mp (Finset.mem_filter.mp href).1).1
  let initial := Q.literalFactorFreeComputedProfiles (σ := σ) ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ reference hallowed s bound hbound originalWindow hreference ht
    hcompact hwindow hprime branch (powerIdeal q.val n) firstFixed (powerIdeal q.val (2 * n)) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q.val ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q.val (2 * n)) CanonicalLiteralFixedPhases.emptyDivisorInverse_generates
    δ₁ δ₂
  have e := literalLeftPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  have hfirstSupport : ∀ J ∈ (primeSupport DE.1 ∪ {q.val.val.asIdeal}), Prime J := by
    intro J hJ
    rcases Finset.mem_union.mp hJ with hJ | hJ
    · exact support_prime hJ
    · rcases Finset.mem_singleton.mp hJ with rfl
      exact q.val.val.prime
  exact (CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenRedistributeScale
    scalar δ₁ δ₂
    (CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenRedistributeScale
      scalar δ₁ δ₂ initial (((p.leftSourceCovers raw.originalAtlas S χ).residual q n).branch label) (congrArg Sigma.fst e).symm)
    (literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) hfirstSupport)).balanceOne

/-- The coefficient remains the explicit original seed bound,
before any Fourier variable or child is chosen. -/
theorem literalLeftPoolFactorFreeComputedProfiles_bound
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers raw.originalAtlas S χ).residual q n).labels) :
    (literalLeftPoolFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href s bound hbound originalWindow hreference ht hcompact hwindow hprime
      firstFixed hfirst δ₂ q n label).bound =
      let branch := (p.divisorPools.leftData S).combinedBranchForLabel raw.originalAtlas
        (primeSupport DE.1) DE.1
        ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label
      fun r => bound + bound * CanonicalLogProfiles.shapeCoefficient window hcompact hwindow
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s) *
          (1 + CanonicalLiteralBalancedSchwartz.factor seed branch δ₁ δ₂ r) := by
  unfold literalLeftPoolFactorFreeComputedProfiles
  simp only [CanonicalLiteralFullKappaInput.ComputedProfiles.balanceOne_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenRedistributeScale_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenRedistributeScale_bound] <;> rfl

/-- All profile data are constructed for this same actual table,
with the complete positive factor charged in its first scalar. -/
def literalRightPoolFactorFreeComputedProfiles
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers raw.originalAtlas S χ).residual q n).labels) :
    let actual := literalRightPoolProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href originalWindow hreference ht hwindow
      firstFixed hfirst δ₂ q n label
    let atoms := literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ q n label
    let scalar := literalRightPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((((actual.redistributeNormFactors δ₁ δ₂).profiles).scale
        (scalar * (atoms.normProfileFactor δ₁ δ₂ : ℂ))⁻¹).balancePlain (fun _ => 1))
      window s bound := by
  let branch := (p.divisorPools.rightData S).combinedBranchForLabel raw.originalAtlas
    (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label
  let scalar := literalRightPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  have hallowed : (data ξ).allowedRow reference :=
    (((data ξ).rows_spec _ reference).mp (Finset.mem_filter.mp href).1).1
  let initial := Q.literalFactorFreeComputedProfiles (σ := σ) ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ reference hallowed s bound hbound originalWindow hreference ht
    hcompact hwindow hprime branch (powerIdeal q.val n) firstFixed (powerIdeal q.val (2 * n)) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q.val ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q.val (2 * n)) CanonicalLiteralFixedPhases.emptyDivisorInverse_generates
    δ₁ δ₂
  have e := literalRightPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  have hfirstSupport : ∀ J ∈ (primeSupport DE.1 ∪ {q.val.val.asIdeal}), Prime J := by
    intro J hJ
    rcases Finset.mem_union.mp hJ with hJ | hJ
    · exact support_prime hJ
    · rcases Finset.mem_singleton.mp hJ with rfl
      exact q.val.val.prime
  exact (CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenRedistributeScale
    scalar δ₁ δ₂
    (CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenRedistributeScale
      scalar δ₁ δ₂ initial (((p.rightSourceCovers raw.originalAtlas S χ).residual q n).branch label) (congrArg Sigma.fst e).symm)
    (literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) hfirstSupport)).balanceOne

/-- The coefficient remains the explicit original seed bound,
before any Fourier variable or child is chosen. -/
theorem literalRightPoolFactorFreeComputedProfiles_bound
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers raw.originalAtlas S χ).residual q n).labels) :
    (literalRightPoolFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href s bound hbound originalWindow hreference ht hcompact hwindow hprime
      firstFixed hfirst δ₂ q n label).bound =
      let branch := (p.divisorPools.rightData S).combinedBranchForLabel raw.originalAtlas
        (primeSupport DE.1) DE.2
        ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label
      fun r => bound + bound * CanonicalLogProfiles.shapeCoefficient window hcompact hwindow
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s) *
          (1 + CanonicalLiteralBalancedSchwartz.factor seed branch δ₁ δ₂ r) := by
  unfold literalRightPoolFactorFreeComputedProfiles
  simp only [CanonicalLiteralFullKappaInput.ComputedProfiles.balanceOne_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenRedistributeScale_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenRedistributeScale_bound] <;> rfl

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainFactorFreeComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainFactorFreeComputedProfiles_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainFactorFreeComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainFactorFreeComputedProfiles_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolFactorFreeComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolFactorFreeComputedProfiles_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolFactorFreeComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolFactorFreeComputedProfiles_bound
