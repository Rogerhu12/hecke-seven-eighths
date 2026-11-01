import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolScalars
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActiveRadius

/-!
# Computed scalar-free profiles on the actual pool tables

These constructors start with the original profile window and paired
reference row. They follow the existing first extraction, exact atlas
transport and full mask deletion. The returned objects refer to the
same actual profile data, scaled by the inverse of its actual scalar
and balanced on the original first branch. Neither a finished child
window nor an estimate of a whole source is supplied as an input.
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

/-- The positive reciprocal balance computed on the original first
extraction. It does not depend on a profile bound or a later child. -/
def literalLeftMainBalance (δ₂ : ℝ) (label : ((p.leftSourceCovers raw.originalAtlas S χ).main).labels) : Bool → ℝ :=
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.1 label
  CanonicalLiteralBalancedSchwartz.balance seed branch δ₁ δ₂

/-- The positive reciprocal balance computed on the original first
extraction. It does not depend on a profile bound or a later child. -/
def literalRightMainBalance (δ₂ : ℝ) (label : ((p.rightSourceCovers raw.originalAtlas S χ).main).labels) : Bool → ℝ :=
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.2 label
  CanonicalLiteralBalancedSchwartz.balance seed branch δ₁ δ₂

/-- The positive reciprocal balance computed on the original first
extraction. It does not depend on a profile bound or a later child. -/
def literalLeftPoolBalance (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers raw.originalAtlas S χ).residual q n).labels) : Bool → ℝ :=
  let branch := (p.divisorPools.leftData S).combinedBranchForLabel raw.originalAtlas
    (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label
  CanonicalLiteralBalancedSchwartz.balance seed branch δ₁ δ₂

/-- The positive reciprocal balance computed on the original first
extraction. It does not depend on a profile bound or a later child. -/
def literalRightPoolBalance (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers raw.originalAtlas S χ).residual q n).labels) : Bool → ℝ :=
  let branch := (p.divisorPools.rightData S).combinedBranchForLabel raw.originalAtlas
    (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label
  CanonicalLiteralBalancedSchwartz.balance seed branch δ₁ δ₂

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

/-- The original finite seminorm window constructs the complete
profile certificate on the existing left main table. The actual
common/pool scalar is stripped once, and the original balance is kept. -/
def literalLeftMainComputedProfiles
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδhi : δ₁ + δ₂ ≤ 1 / 2) (label : ((p.leftSourceCovers raw.originalAtlas S χ).main).labels) :
    let actual := literalLeftMainProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href originalWindow hreference ht hwindow
      firstFixed hfirst δ₂ label
    let scalar := literalLeftMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
    let balance := literalLeftMainBalance hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ δ₂ label
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((actual.profiles.scale scalar⁻¹).balancePlain balance) window s bound := by
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.1 label
  let scalar := literalLeftMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  let balance := literalLeftMainBalance hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ δ₂ label
  have hallowed : (data ξ).allowedRow reference :=
    (((data ξ).rows_spec _ reference).mp (Finset.mem_filter.mp href).1).1
  let initial := Q.literalScalarFreeComputedProfiles (σ := σ) ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ reference hallowed s bound hbound originalWindow hreference ht
    hcompact hwindow hprime branch (unitExterior A) firstFixed (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A) CanonicalLiteralFixedPhases.emptyDivisorInverse_generates
    δ₁ δ₂ hδhi
  have e := literalLeftMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  exact CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenScaleBalance
    scalar⁻¹ balance
    (CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance
      scalar⁻¹ balance initial (((p.leftSourceCovers raw.originalAtlas S χ).main).branch label) (congrArg Sigma.fst e).symm)
    (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))

/-- The already chosen coefficient is preserved through the atlas and
mask operations; its formula is the original single-profile estimate. -/
theorem literalLeftMainComputedProfiles_bound
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδhi : δ₁ + δ₂ ≤ 1 / 2) (label : ((p.leftSourceCovers raw.originalAtlas S χ).main).labels) :
    (literalLeftMainComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href s bound hbound originalWindow hreference ht hcompact hwindow hprime
      firstFixed hfirst δ₂ hδhi label).bound =
      let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.1 label
      fun r => bound + bound * CanonicalLogProfiles.shapeCoefficient window hcompact hwindow
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s) *
          (1 + CanonicalLiteralBalancedSchwartz.factor seed branch δ₁ δ₂ r) := by
  unfold literalLeftMainComputedProfiles
  simp only [CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenScaleBalance_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance_bound,
    literalScalarFreeComputedProfiles, CanonicalLiteralFullKappaInput.scalarFreeBalanced_bound]

/-- The original finite seminorm window constructs the complete
profile certificate on the existing right main table. The actual
common/pool scalar is stripped once, and the original balance is kept. -/
def literalRightMainComputedProfiles
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδhi : δ₁ + δ₂ ≤ 1 / 2) (label : ((p.rightSourceCovers raw.originalAtlas S χ).main).labels) :
    let actual := literalRightMainProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href originalWindow hreference ht hwindow
      firstFixed hfirst δ₂ label
    let scalar := literalRightMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
    let balance := literalRightMainBalance hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ δ₂ label
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((actual.profiles.scale scalar⁻¹).balancePlain balance) window s bound := by
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.2 label
  let scalar := literalRightMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  let balance := literalRightMainBalance hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ δ₂ label
  have hallowed : (data ξ).allowedRow reference :=
    (((data ξ).rows_spec _ reference).mp (Finset.mem_filter.mp href).1).1
  let initial := Q.literalScalarFreeComputedProfiles (σ := σ) ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ reference hallowed s bound hbound originalWindow hreference ht
    hcompact hwindow hprime branch (unitExterior A) firstFixed (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A) CanonicalLiteralFixedPhases.emptyDivisorInverse_generates
    δ₁ δ₂ hδhi
  have e := literalRightMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  exact CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenScaleBalance
    scalar⁻¹ balance
    (CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance
      scalar⁻¹ balance initial (((p.rightSourceCovers raw.originalAtlas S χ).main).branch label) (congrArg Sigma.fst e).symm)
    (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))

/-- The already chosen coefficient is preserved through the atlas and
mask operations; its formula is the original single-profile estimate. -/
theorem literalRightMainComputedProfiles_bound
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδhi : δ₁ + δ₂ ≤ 1 / 2) (label : ((p.rightSourceCovers raw.originalAtlas S χ).main).labels) :
    (literalRightMainComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href s bound hbound originalWindow hreference ht hcompact hwindow hprime
      firstFixed hfirst δ₂ hδhi label).bound =
      let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.2 label
      fun r => bound + bound * CanonicalLogProfiles.shapeCoefficient window hcompact hwindow
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s) *
          (1 + CanonicalLiteralBalancedSchwartz.factor seed branch δ₁ δ₂ r) := by
  unfold literalRightMainComputedProfiles
  simp only [CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenScaleBalance_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance_bound,
    literalScalarFreeComputedProfiles, CanonicalLiteralFullKappaInput.scalarFreeBalanced_bound]

/-- The original finite seminorm window constructs the complete
profile certificate on the existing left pool table. The actual
common/pool scalar is stripped once, and the original balance is kept. -/
def literalLeftPoolComputedProfiles
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδhi : δ₁ + δ₂ ≤ 1 / 2) (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers raw.originalAtlas S χ).residual q n).labels) :
    let actual := literalLeftPoolProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href originalWindow hreference ht hwindow
      firstFixed hfirst δ₂ q n label
    let scalar := literalLeftPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
    let balance := literalLeftPoolBalance hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ δ₂ q n label
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((actual.profiles.scale scalar⁻¹).balancePlain balance) window s bound := by
  let branch := (p.divisorPools.leftData S).combinedBranchForLabel raw.originalAtlas
    (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label
  let scalar := literalLeftPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  let balance := literalLeftPoolBalance hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ δ₂ q n label
  have hallowed : (data ξ).allowedRow reference :=
    (((data ξ).rows_spec _ reference).mp (Finset.mem_filter.mp href).1).1
  let initial := Q.literalScalarFreeComputedProfiles (σ := σ) ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ reference hallowed s bound hbound originalWindow hreference ht
    hcompact hwindow hprime branch (powerIdeal q.val n) firstFixed (powerIdeal q.val (2 * n)) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q.val ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q.val (2 * n)) CanonicalLiteralFixedPhases.emptyDivisorInverse_generates
    δ₁ δ₂ hδhi
  have e := literalLeftPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  have hfirstSupport : ∀ J ∈ (primeSupport DE.1 ∪ {q.val.val.asIdeal}), Prime J := by
    intro J hJ
    rcases Finset.mem_union.mp hJ with hJ | hJ
    · exact support_prime hJ
    · rcases Finset.mem_singleton.mp hJ with rfl
      exact q.val.val.prime
  exact CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenScaleBalance
    scalar⁻¹ balance
    (CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance
      scalar⁻¹ balance initial (((p.leftSourceCovers raw.originalAtlas S χ).residual q n).branch label) (congrArg Sigma.fst e).symm)
    (literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) hfirstSupport)

/-- The already chosen coefficient is preserved through the atlas and
mask operations; its formula is the original single-profile estimate. -/
theorem literalLeftPoolComputedProfiles_bound
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδhi : δ₁ + δ₂ ≤ 1 / 2) (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers raw.originalAtlas S χ).residual q n).labels) :
    (literalLeftPoolComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href s bound hbound originalWindow hreference ht hcompact hwindow hprime
      firstFixed hfirst δ₂ hδhi q n label).bound =
      let branch := (p.divisorPools.leftData S).combinedBranchForLabel raw.originalAtlas
        (primeSupport DE.1) DE.1
        ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label
      fun r => bound + bound * CanonicalLogProfiles.shapeCoefficient window hcompact hwindow
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s) *
          (1 + CanonicalLiteralBalancedSchwartz.factor seed branch δ₁ δ₂ r) := by
  unfold literalLeftPoolComputedProfiles
  simp only [CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenScaleBalance_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance_bound,
    literalScalarFreeComputedProfiles, CanonicalLiteralFullKappaInput.scalarFreeBalanced_bound]

/-- The original finite seminorm window constructs the complete
profile certificate on the existing right pool table. The actual
common/pool scalar is stripped once, and the original balance is kept. -/
def literalRightPoolComputedProfiles
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδhi : δ₁ + δ₂ ≤ 1 / 2) (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers raw.originalAtlas S χ).residual q n).labels) :
    let actual := literalRightPoolProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href originalWindow hreference ht hwindow
      firstFixed hfirst δ₂ q n label
    let scalar := literalRightPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
    let balance := literalRightPoolBalance hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ δ₂ q n label
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((actual.profiles.scale scalar⁻¹).balancePlain balance) window s bound := by
  let branch := (p.divisorPools.rightData S).combinedBranchForLabel raw.originalAtlas
    (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label
  let scalar := literalRightPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  let balance := literalRightPoolBalance hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ δ₂ q n label
  have hallowed : (data ξ).allowedRow reference :=
    (((data ξ).rows_spec _ reference).mp (Finset.mem_filter.mp href).1).1
  let initial := Q.literalScalarFreeComputedProfiles (σ := σ) ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ reference hallowed s bound hbound originalWindow hreference ht
    hcompact hwindow hprime branch (powerIdeal q.val n) firstFixed (powerIdeal q.val (2 * n)) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q.val ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q.val (2 * n)) CanonicalLiteralFixedPhases.emptyDivisorInverse_generates
    δ₁ δ₂ hδhi
  have e := literalRightPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  have hfirstSupport : ∀ J ∈ (primeSupport DE.1 ∪ {q.val.val.asIdeal}), Prime J := by
    intro J hJ
    rcases Finset.mem_union.mp hJ with hJ | hJ
    · exact support_prime hJ
    · rcases Finset.mem_singleton.mp hJ with rfl
      exact q.val.val.prime
  exact CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenScaleBalance
    scalar⁻¹ balance
    (CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance
      scalar⁻¹ balance initial (((p.rightSourceCovers raw.originalAtlas S χ).residual q n).branch label) (congrArg Sigma.fst e).symm)
    (literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) hfirstSupport)

/-- The already chosen coefficient is preserved through the atlas and
mask operations; its formula is the original single-profile estimate. -/
theorem literalRightPoolComputedProfiles_bound
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδhi : δ₁ + δ₂ ≤ 1 / 2) (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers raw.originalAtlas S χ).residual q n).labels) :
    (literalRightPoolComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href s bound hbound originalWindow hreference ht hcompact hwindow hprime
      firstFixed hfirst δ₂ hδhi q n label).bound =
      let branch := (p.divisorPools.rightData S).combinedBranchForLabel raw.originalAtlas
        (primeSupport DE.1) DE.2
        ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label
      fun r => bound + bound * CanonicalLogProfiles.shapeCoefficient window hcompact hwindow
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s) *
          (1 + CanonicalLiteralBalancedSchwartz.factor seed branch δ₁ δ₂ r) := by
  unfold literalRightPoolComputedProfiles
  simp only [CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenScaleBalance_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance_bound,
    literalScalarFreeComputedProfiles, CanonicalLiteralFullKappaInput.scalarFreeBalanced_bound]

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainComputedProfiles_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainComputedProfiles_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolComputedProfiles_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolComputedProfiles_bound
