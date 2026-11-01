import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralScalarNormalForm

/-!
# Exact original constant factors in the actual pool tables

Each core is constructed by the original support branch, atlas and
complete deletion. Its scalar is exactly the first frozen scalar times
the original pool reciprocity scalar. The atom-table equality is proved
from the single-occurrence operations, with no column identity as input.
The zero scalar case is included.
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

/-- The exact same atlas and full mask, with the two constant
profile factors separated before normalization. -/
def literalLeftMainCore
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.leftSourceCovers raw.originalAtlas S χ).main.labels) :
    CanonicalLiteralRectangles.Atoms (K := K) ((p.leftSourceCovers raw.originalAtlas S χ).main.branch label).slotCount :=
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.1 label
  let e := literalLeftMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  let input := seed.secondInputCore P R branch firstFixed
    (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  (input.onAtlas ((p.leftSourceCovers raw.originalAtlas S χ).main.branch label)
    (congrArg Sigma.fst e).symm).deleteMask
      (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))

def literalLeftMainScalar
    (label : (p.leftSourceCovers raw.originalAtlas S χ).main.labels) : ℂ :=
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.1 label

  seed.secondInputScalar (σ := σ) branch (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) δ₁

theorem literalLeftMainAtoms_eq_scale_core
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.leftSourceCovers raw.originalAtlas S χ).main.labels) :
    literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label =
      (literalLeftMainCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        firstFixed hfirst δ₂ label).scale
          (literalLeftMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label) := by
  unfold literalLeftMainAtoms literalLeftMainCore literalLeftMainScalar
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.secondInput_eq_scale_core,
    CanonicalLiteralRectangles.Atoms.scale_onAtlas,
    CanonicalLiteralRectangles.Atoms.scale_deleteMask]


/-- The exact same atlas and full mask, with the two constant
profile factors separated before normalization. -/
def literalLeftPoolCore
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers raw.originalAtlas S χ).residual q n).labels) :
    CanonicalLiteralRectangles.Atoms (K := K) (((p.leftSourceCovers raw.originalAtlas S χ).residual q n).branch label).slotCount :=
  let branch := (p.divisorPools.leftData S).combinedBranchForLabel raw.originalAtlas (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label
  let e := literalLeftPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  let input := seed.secondInputCore P R branch firstFixed
    (powerIdeal q.val (2 * n)) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q.val ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q.val (2 * n))
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  (input.onAtlas (((p.leftSourceCovers raw.originalAtlas S χ).residual q n).branch label)
    (congrArg Sigma.fst e).symm).deleteMask
      (literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) (fun _ hp => by
        rcases Finset.mem_union.mp hp with hp | hp
        · exact support_prime hp
        · rcases Finset.mem_singleton.mp hp with rfl
          exact q.val.val.prime))

def literalLeftPoolScalar
    (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers raw.originalAtlas S χ).residual q n).labels) : ℂ :=
  let branch := (p.divisorPools.leftData S).combinedBranchForLabel raw.originalAtlas (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label

  seed.secondInputScalar (σ := σ) branch (powerIdeal q.val n)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) δ₁

theorem literalLeftPoolAtoms_eq_scale_core
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers raw.originalAtlas S χ).residual q n).labels) :
    literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ q n label =
      (literalLeftPoolCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        firstFixed hfirst δ₂ q n label).scale
          (literalLeftPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label) := by
  unfold literalLeftPoolAtoms literalLeftPoolCore literalLeftPoolScalar
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.secondInput_eq_scale_core,
    CanonicalLiteralRectangles.Atoms.scale_onAtlas,
    CanonicalLiteralRectangles.Atoms.scale_deleteMask]


/-- The exact same atlas and full mask, with the two constant
profile factors separated before normalization. -/
def literalRightMainCore
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.rightSourceCovers raw.originalAtlas S χ).main.labels) :
    CanonicalLiteralRectangles.Atoms (K := K) ((p.rightSourceCovers raw.originalAtlas S χ).main.branch label).slotCount :=
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.2 label
  let e := literalRightMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  let input := seed.secondInputCore P R branch firstFixed
    (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  (input.onAtlas ((p.rightSourceCovers raw.originalAtlas S χ).main.branch label)
    (congrArg Sigma.fst e).symm).deleteMask
      (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))

def literalRightMainScalar
    (label : (p.rightSourceCovers raw.originalAtlas S χ).main.labels) : ℂ :=
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.2 label

  seed.secondInputScalar (σ := σ) branch (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) δ₁

theorem literalRightMainAtoms_eq_scale_core
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.rightSourceCovers raw.originalAtlas S χ).main.labels) :
    literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label =
      (literalRightMainCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        firstFixed hfirst δ₂ label).scale
          (literalRightMainScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label) := by
  unfold literalRightMainAtoms literalRightMainCore literalRightMainScalar
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.secondInput_eq_scale_core,
    CanonicalLiteralRectangles.Atoms.scale_onAtlas,
    CanonicalLiteralRectangles.Atoms.scale_deleteMask]


/-- The exact same atlas and full mask, with the two constant
profile factors separated before normalization. -/
def literalRightPoolCore
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers raw.originalAtlas S χ).residual q n).labels) :
    CanonicalLiteralRectangles.Atoms (K := K) (((p.rightSourceCovers raw.originalAtlas S χ).residual q n).branch label).slotCount :=
  let branch := (p.divisorPools.rightData S).combinedBranchForLabel raw.originalAtlas (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label
  let e := literalRightPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  let input := seed.secondInputCore P R branch firstFixed
    (powerIdeal q.val (2 * n)) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q.val ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q.val (2 * n))
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  (input.onAtlas (((p.rightSourceCovers raw.originalAtlas S χ).residual q n).branch label)
    (congrArg Sigma.fst e).symm).deleteMask
      (literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) (fun _ hp => by
        rcases Finset.mem_union.mp hp with hp | hp
        · exact support_prime hp
        · rcases Finset.mem_singleton.mp hp with rfl
          exact q.val.val.prime))

def literalRightPoolScalar
    (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers raw.originalAtlas S χ).residual q n).labels) : ℂ :=
  let branch := (p.divisorPools.rightData S).combinedBranchForLabel raw.originalAtlas (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label

  seed.secondInputScalar (σ := σ) branch (powerIdeal q.val n)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) δ₁

theorem literalRightPoolAtoms_eq_scale_core
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers raw.originalAtlas S χ).residual q n).labels) :
    literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ q n label =
      (literalRightPoolCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        firstFixed hfirst δ₂ q n label).scale
          (literalRightPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label) := by
  unfold literalRightPoolAtoms literalRightPoolCore literalRightPoolScalar
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.secondInput_eq_scale_core,
    CanonicalLiteralRectangles.Atoms.scale_onAtlas,
    CanonicalLiteralRectangles.Atoms.scale_deleteMask]

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainAtoms_eq_scale_core
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolAtoms_eq_scale_core
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainAtoms_eq_scale_core
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolAtoms_eq_scale_core
