import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolAtlasCoefficients
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralResidualDeletion
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSecondCoveredSource

/-!
# Original atom tables on the main and valuation source covers

Each table is computed from the actual parent's original atlas, the
existing first common label and the original pool valuation subtype.
The original combined-support constructor supplies its occurrence map.
The full first support deletion is added with exact value one on these
actual columns. In the error case the pool-prime mask is also retained;
it is already part of the true combined residual carrier.

These definitions select no new source, rectangle or allocation. Their
coefficient theorems are consequences of the original per-occurrence
phase calculations, original atlas products and source subtype maps.
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
theorem literalLeftMainCover_dictionary
    (label : (p.leftSourceCovers (raw).originalAtlas S χ).main.labels) :
    ((p.leftSourceCovers (raw).originalAtlas S χ).main.branch label).literalDictionary =
      ⟨((raw).originalAtlas.branch (primeSupport DE.1) DE.1 label).keep.card,
        (SupportCartesian.plainResidual (seed).plain₁ (primeSupport DE.1)
          ((raw).originalAtlas.branch (primeSupport DE.1) DE.1 label).plainExtract₁,
        SupportCartesian.plainResidual (seed).plain₂ (primeSupport DE.1)
          ((raw).originalAtlas.branch (primeSupport DE.1) DE.1 label).plainExtract₂),
        (fun j => SupportCartesian.primeLive
          ((seed).slots (SlotRestriction.index ((raw).originalAtlas.branch (primeSupport DE.1) DE.1 label).keep j)) (primeSupport DE.1)),
        (fun i => (raw).originalIndex (((raw).originalAtlas.branch (primeSupport DE.1) DE.1 label).reconstruct i))⟩ :=
  (p.divisorPools.leftData S).mainSourceCartesianCover_literalDictionary (raw).originalAtlas
    (primeSupport DE.1) DE.1 ((p.divisorPools.left_columns S).trans p.left_columns)
    (fun i => by rw [p.divisorPools.left_ideal S, p.left_ideal]; exact b.left_residual i) (p.leftDivisorCoefficient S χ) label

def literalLeftMainAtoms
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.leftSourceCovers (raw).originalAtlas S χ).main.labels) :
    CanonicalLiteralRectangles.Atoms (K := K) ((p.leftSourceCovers (raw).originalAtlas S χ).main.branch label).slotCount :=
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.1 label
  let e := literalLeftMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  let input := (seed).secondInput (σ := σ) branch P R (unitExterior A) firstFixed
    (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  (input.onAtlas ((p.leftSourceCovers (raw).originalAtlas S χ).main.branch label)
    (congrArg Sigma.fst e).symm).deleteMask
      (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))

theorem literalLeftMainAtoms_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.leftSourceCovers (raw).originalAtlas S χ).main.labels)
    (i : AllocationColumn K ((p.leftSourceCovers (raw).originalAtlas S χ).main.branch label).slotCount)
    (hi : i ∈ ((p.leftSourceCovers (raw).originalAtlas S χ).main.branch label).reindex.cartesian)
    (hSi : S.val ∣ (p.leftData.ideal
      (((p.leftSourceCovers (raw).originalAtlas S χ).main.branch label).reindex.index i)).val) :
    (literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ label).whole i =
      p.leftDivisorCoefficient S χ (((p.leftSourceCovers (raw).originalAtlas S χ).main.branch label).reindex.index i) *
        ((A.exteriorNorm ((p.divisorPools.leftData S).ideal
          (((p.leftSourceCovers (raw).originalAtlas S χ).main.branch label).reindex.index i)) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) ((p.divisorPools.leftData S).ideal
          (((p.leftSourceCovers (raw).originalAtlas S χ).main.branch label).reindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.1 label
  let T := (p.leftSourceCovers (raw).originalAtlas S χ).main.branch label
  have e := literalLeftMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  have hc := canonicalLeftMain_atlasCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    (primeSupport DE.1) branch hroot hemb T
    (fun _ hm => (Finset.mem_filter.mp hm).1) e i hi hSi firstFixed hfirst δ₂
  have hm := branch.atlas_full_mask_one T (fun _ hp => support_prime hp)
    (fun j => (raw).originalIndex (branch.reconstruct j)) e i hi
  unfold literalLeftMainAtoms
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.deleteMask_whole _ _ i hi, hm, mul_one]
  simpa only [p.divisorPools.left_ideal S, p.left_ideal] using hc

theorem literalLeftPoolCover_dictionary (q : pool.primes) (n : ℕ)
    (label : ((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).labels) :
    let branch := (p.divisorPools.leftData S).combinedBranchForLabel (raw).originalAtlas (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label
    let index := ((p.divisorPools.leftData S).residualSource_cartesianBranch_of_original_support (raw).originalAtlas
    (primeSupport DE.1) DE.1 ((p.divisorPools.left_columns S).trans p.left_columns) (fun i => by rw [p.divisorPools.left_ideal S, p.left_ideal]; exact b.left_residual i)
    q.val n (p.leftDivisorCoefficient S χ) branch ((p.divisorPools.leftData S).combinedBranchForLabel_spec (raw).originalAtlas (primeSupport DE.1) DE.1
      ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label).2).index
    (((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label).literalDictionary =
      ⟨branch.keep.card,
        (SupportCartesian.plainResidual (seed).plain₁ (primeSupport DE.1 ∪ {q.val.val.asIdeal}) branch.plainExtract₁,
        SupportCartesian.plainResidual (seed).plain₂ (primeSupport DE.1 ∪ {q.val.val.asIdeal}) branch.plainExtract₂),
        (fun j => SupportCartesian.primeLive
          ((seed).slots (SlotRestriction.index branch.keep j)) (primeSupport DE.1 ∪ {q.val.val.asIdeal})), index⟩ :=
  (p.divisorPools.leftData S).residualSourceCartesianCover_literalDictionary (raw).originalAtlas
    (primeSupport DE.1) DE.1 ((p.divisorPools.left_columns S).trans p.left_columns)
    (fun i => by rw [p.divisorPools.left_ideal S, p.left_ideal]; exact b.left_residual i) (p.leftDivisorCoefficient S χ) q.val n label

def literalLeftPoolAtoms
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).labels) :
    CanonicalLiteralRectangles.Atoms (K := K) (((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label).slotCount :=
  let branch := (p.divisorPools.leftData S).combinedBranchForLabel (raw).originalAtlas (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label
  let e := literalLeftPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  let input := (seed).secondInput (σ := σ) branch P R (powerIdeal q.val n) firstFixed
    (powerIdeal q.val (2 * n)) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q.val ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q.val (2 * n))
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  (input.onAtlas (((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label)
    (congrArg Sigma.fst e).symm).deleteMask
      (literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) (fun _ hp => by
        rcases Finset.mem_union.mp hp with hp | hp
        · exact support_prime hp
        · rcases Finset.mem_singleton.mp hp with rfl
          exact q.val.val.prime))

theorem literalLeftPoolAtoms_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).labels)
    (i : AllocationColumn K (((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label).slotCount)
    (hi : i ∈ (((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label).reindex.cartesian)
    (hSi : S.val ∣ (p.leftData.ideal
      ((((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label).reindex.index i).val).val) :
    (literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n label).whole i =
      (p.divisorPools.leftData S).residualCoefficient q.val n (p.leftDivisorCoefficient S χ)
          ((((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label).reindex.index i) *
        ((A.exteriorNorm (((p.divisorPools.leftData S).residualPresentation q.val n
          ((((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label).reindex.index i)).residual) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) ((p.divisorPools.leftData S).residualPresentation q.val n
          ((((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label).reindex.index i)).residual.val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  let branch := (p.divisorPools.leftData S).combinedBranchForLabel (raw).originalAtlas (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label
  let index := ((p.divisorPools.leftData S).residualSource_cartesianBranch_of_original_support (raw).originalAtlas
    (primeSupport DE.1) DE.1 ((p.divisorPools.left_columns S).trans p.left_columns) (fun i => by rw [p.divisorPools.left_ideal S, p.left_ideal]; exact b.left_residual i)
    q.val n (p.leftDivisorCoefficient S χ) branch ((p.divisorPools.leftData S).combinedBranchForLabel_spec (raw).originalAtlas (primeSupport DE.1) DE.1
      ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label).2).index
  let T := ((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).branch label
  have e := literalLeftPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  have hc := canonicalLeftPool_atlasCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    (primeSupport DE.1 ∪ {q.val.val.asIdeal}) branch hroot hemb q.val n T index e
    (fun j hj => (p.divisorPools.leftData S).residualSource_original_support_index_val (raw).originalAtlas
      (primeSupport DE.1) DE.1 ((p.divisorPools.left_columns S).trans p.left_columns) (fun i => by rw [p.divisorPools.left_ideal S, p.left_ideal]; exact b.left_residual i)
      (p.leftDivisorCoefficient S χ) q.val n branch ((p.divisorPools.leftData S).combinedBranchForLabel_spec (raw).originalAtlas (primeSupport DE.1) DE.1
      ((p.divisorPools.left_columns S).trans p.left_columns) q.val n label).2 j hj)
    i hi hSi firstFixed hfirst δ₂
  have hprime : ∀ p ∈ (primeSupport DE.1 ∪ {q.val.val.asIdeal}), Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact support_prime hp
    · rw [Finset.mem_singleton] at hp
      subst p
      exact q.val.val.prime
  have hm := branch.atlas_full_mask_one T hprime index e i hi
  unfold literalLeftPoolAtoms
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.deleteMask_whole _ _ i hi, hm, mul_one]
  exact hc

theorem literalRightMainCover_dictionary
    (label : (p.rightSourceCovers (raw).originalAtlas S χ).main.labels) :
    ((p.rightSourceCovers (raw).originalAtlas S χ).main.branch label).literalDictionary =
      ⟨((raw).originalAtlas.branch (primeSupport DE.1) DE.2 label).keep.card,
        (SupportCartesian.plainResidual (seed).plain₁ (primeSupport DE.1)
          ((raw).originalAtlas.branch (primeSupport DE.1) DE.2 label).plainExtract₁,
        SupportCartesian.plainResidual (seed).plain₂ (primeSupport DE.1)
          ((raw).originalAtlas.branch (primeSupport DE.1) DE.2 label).plainExtract₂),
        (fun j => SupportCartesian.primeLive
          ((seed).slots (SlotRestriction.index ((raw).originalAtlas.branch (primeSupport DE.1) DE.2 label).keep j)) (primeSupport DE.1)),
        (fun i => (raw).originalIndex (((raw).originalAtlas.branch (primeSupport DE.1) DE.2 label).reconstruct i))⟩ :=
  (p.divisorPools.rightData S).mainSourceCartesianCover_literalDictionary (raw).originalAtlas
    (primeSupport DE.1) DE.2 ((p.divisorPools.right_columns S).trans p.right_columns)
    (fun i => by rw [p.divisorPools.right_ideal S, p.right_ideal]; exact b.right_residual i) (p.rightDivisorCoefficient S χ) label

def literalRightMainAtoms
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.rightSourceCovers (raw).originalAtlas S χ).main.labels) :
    CanonicalLiteralRectangles.Atoms (K := K) ((p.rightSourceCovers (raw).originalAtlas S χ).main.branch label).slotCount :=
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.2 label
  let e := literalRightMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  let input := (seed).secondInput (σ := σ) branch P R (unitExterior A) firstFixed
    (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  (input.onAtlas ((p.rightSourceCovers (raw).originalAtlas S χ).main.branch label)
    (congrArg Sigma.fst e).symm).deleteMask
      (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))

theorem literalRightMainAtoms_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.rightSourceCovers (raw).originalAtlas S χ).main.labels)
    (i : AllocationColumn K ((p.rightSourceCovers (raw).originalAtlas S χ).main.branch label).slotCount)
    (hi : i ∈ ((p.rightSourceCovers (raw).originalAtlas S χ).main.branch label).reindex.cartesian)
    (hSi : S.val ∣ (p.rightData.ideal
      (((p.rightSourceCovers (raw).originalAtlas S χ).main.branch label).reindex.index i)).val) :
    (literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ label).whole i =
      p.rightDivisorCoefficient S χ (((p.rightSourceCovers (raw).originalAtlas S χ).main.branch label).reindex.index i) *
        ((A.exteriorNorm ((p.divisorPools.rightData S).ideal
          (((p.rightSourceCovers (raw).originalAtlas S χ).main.branch label).reindex.index i)) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) ((p.divisorPools.rightData S).ideal
          (((p.rightSourceCovers (raw).originalAtlas S χ).main.branch label).reindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.2 label
  let T := (p.rightSourceCovers (raw).originalAtlas S χ).main.branch label
  have e := literalRightMainCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  have hc := canonicalRightMain_atlasCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    (primeSupport DE.1) branch hroot hemb T
    (fun _ hm => (Finset.mem_filter.mp hm).1) e i hi hSi firstFixed hfirst δ₂
  have hm := branch.atlas_full_mask_one T (fun _ hp => support_prime hp)
    (fun j => (raw).originalIndex (branch.reconstruct j)) e i hi
  unfold literalRightMainAtoms
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.deleteMask_whole _ _ i hi, hm, mul_one]
  simpa only [p.divisorPools.right_ideal S, p.right_ideal] using hc

theorem literalRightPoolCover_dictionary (q : pool.primes) (n : ℕ)
    (label : ((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).labels) :
    let branch := (p.divisorPools.rightData S).combinedBranchForLabel (raw).originalAtlas (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label
    let index := ((p.divisorPools.rightData S).residualSource_cartesianBranch_of_original_support (raw).originalAtlas
    (primeSupport DE.1) DE.2 ((p.divisorPools.right_columns S).trans p.right_columns) (fun i => by rw [p.divisorPools.right_ideal S, p.right_ideal]; exact b.right_residual i)
    q.val n (p.rightDivisorCoefficient S χ) branch ((p.divisorPools.rightData S).combinedBranchForLabel_spec (raw).originalAtlas (primeSupport DE.1) DE.2
      ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label).2).index
    (((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label).literalDictionary =
      ⟨branch.keep.card,
        (SupportCartesian.plainResidual (seed).plain₁ (primeSupport DE.1 ∪ {q.val.val.asIdeal}) branch.plainExtract₁,
        SupportCartesian.plainResidual (seed).plain₂ (primeSupport DE.1 ∪ {q.val.val.asIdeal}) branch.plainExtract₂),
        (fun j => SupportCartesian.primeLive
          ((seed).slots (SlotRestriction.index branch.keep j)) (primeSupport DE.1 ∪ {q.val.val.asIdeal})), index⟩ :=
  (p.divisorPools.rightData S).residualSourceCartesianCover_literalDictionary (raw).originalAtlas
    (primeSupport DE.1) DE.2 ((p.divisorPools.right_columns S).trans p.right_columns)
    (fun i => by rw [p.divisorPools.right_ideal S, p.right_ideal]; exact b.right_residual i) (p.rightDivisorCoefficient S χ) q.val n label

def literalRightPoolAtoms
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).labels) :
    CanonicalLiteralRectangles.Atoms (K := K) (((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label).slotCount :=
  let branch := (p.divisorPools.rightData S).combinedBranchForLabel (raw).originalAtlas (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label
  let e := literalRightPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  let input := (seed).secondInput (σ := σ) branch P R (powerIdeal q.val n) firstFixed
    (powerIdeal q.val (2 * n)) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q.val ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q.val (2 * n))
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  (input.onAtlas (((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label)
    (congrArg Sigma.fst e).symm).deleteMask
      (literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) (fun _ hp => by
        rcases Finset.mem_union.mp hp with hp | hp
        · exact support_prime hp
        · rcases Finset.mem_singleton.mp hp with rfl
          exact q.val.val.prime))

theorem literalRightPoolAtoms_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (q : pool.primes) (n : ℕ) (label : ((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).labels)
    (i : AllocationColumn K (((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label).slotCount)
    (hi : i ∈ (((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label).reindex.cartesian)
    (hSi : S.val ∣ (p.rightData.ideal
      ((((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label).reindex.index i).val).val) :
    (literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n label).whole i =
      (p.divisorPools.rightData S).residualCoefficient q.val n (p.rightDivisorCoefficient S χ)
          ((((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label).reindex.index i) *
        ((A.exteriorNorm (((p.divisorPools.rightData S).residualPresentation q.val n
          ((((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label).reindex.index i)).residual) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) ((p.divisorPools.rightData S).residualPresentation q.val n
          ((((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label).reindex.index i)).residual.val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  let branch := (p.divisorPools.rightData S).combinedBranchForLabel (raw).originalAtlas (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label
  let index := ((p.divisorPools.rightData S).residualSource_cartesianBranch_of_original_support (raw).originalAtlas
    (primeSupport DE.1) DE.2 ((p.divisorPools.right_columns S).trans p.right_columns) (fun i => by rw [p.divisorPools.right_ideal S, p.right_ideal]; exact b.right_residual i)
    q.val n (p.rightDivisorCoefficient S χ) branch ((p.divisorPools.rightData S).combinedBranchForLabel_spec (raw).originalAtlas (primeSupport DE.1) DE.2
      ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label).2).index
  let T := ((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).branch label
  have e := literalRightPoolCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n label
  have hc := canonicalRightPool_atlasCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    (primeSupport DE.1 ∪ {q.val.val.asIdeal}) branch hroot hemb q.val n T index e
    (fun j hj => (p.divisorPools.rightData S).residualSource_original_support_index_val (raw).originalAtlas
      (primeSupport DE.1) DE.2 ((p.divisorPools.right_columns S).trans p.right_columns) (fun i => by rw [p.divisorPools.right_ideal S, p.right_ideal]; exact b.right_residual i)
      (p.rightDivisorCoefficient S χ) q.val n branch ((p.divisorPools.rightData S).combinedBranchForLabel_spec (raw).originalAtlas (primeSupport DE.1) DE.2
      ((p.divisorPools.right_columns S).trans p.right_columns) q.val n label).2 j hj)
    i hi hSi firstFixed hfirst δ₂
  have hprime : ∀ p ∈ (primeSupport DE.1 ∪ {q.val.val.asIdeal}), Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact support_prime hp
    · rw [Finset.mem_singleton] at hp
      subst p
      exact q.val.val.prime
  have hm := branch.atlas_full_mask_one T hprime index e i hi
  unfold literalRightPoolAtoms
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.deleteMask_whole _ _ i hi, hm, mul_one]
  exact hc

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainAtoms_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainAtoms_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolAtoms_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolAtoms_coefficient
