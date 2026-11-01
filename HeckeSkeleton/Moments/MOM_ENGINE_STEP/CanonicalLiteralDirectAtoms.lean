import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectAtlasCoefficients
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralResidualDeletion
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSecondStages

/-!
# Computed atom tables for the original direct source covers

The only source atlas used here is the original parent's computed
`originalAtlas`. Each actual common-support label selects its existing
occurrence branch. The full two-stage table is constructed from the
original profiles and fixed arithmetic phases and placed on that
existing atlas. The complete original support mask, including passive
first primes, is inserted with its exact value one on the real carrier.

The resulting coefficient identities require only the original first
divisor's individual ideal divisibility. No completed atom table,
whole-column equality or child estimate is an input.
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
theorem literalLeftDirectCover_dictionary
    (label : (p.leftSourceCover (raw).originalAtlas S χ).labels) :
    ((p.leftSourceCover (raw).originalAtlas S χ).branch label).literalDictionary =
      ⟨((raw).originalAtlas.branch (primeSupport DE.1) DE.1 label).keep.card,
        (SupportCartesian.plainResidual (seed).plain₁ (primeSupport DE.1)
          ((raw).originalAtlas.branch (primeSupport DE.1) DE.1 label).plainExtract₁,
        SupportCartesian.plainResidual (seed).plain₂ (primeSupport DE.1)
          ((raw).originalAtlas.branch (primeSupport DE.1) DE.1 label).plainExtract₂),
        (fun j => SupportCartesian.primeLive
          ((seed).slots (SlotRestriction.index
            ((raw).originalAtlas.branch (primeSupport DE.1) DE.1 label).keep j))
          (primeSupport DE.1)),
        (fun i => (raw).originalIndex
          (((raw).originalAtlas.branch (primeSupport DE.1) DE.1 label).reconstruct i))⟩ :=
  p.leftData.sourceCartesianCover_literalDictionary (raw).originalAtlas
    (primeSupport DE.1) DE.1 p.left_columns
    (fun i => by rw [p.left_ideal]; exact b.left_residual i)
    (p.leftDivisorCoefficient S χ) label

/-- This table contains both original rectangles and every actual
retained occurrence. Its supports are the existing direct cover fields. -/
def literalLeftDirectAtoms
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.leftSourceCover (raw).originalAtlas S χ).labels) :
    CanonicalLiteralRectangles.Atoms (K := K)
      ((p.leftSourceCover (raw).originalAtlas S χ).branch label).slotCount :=
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.1 label
  let e := literalLeftDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  let input := (seed).secondInput (σ := σ) branch P R (unitExterior A) firstFixed
    (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  (input.onAtlas ((p.leftSourceCover (raw).originalAtlas S χ).branch label)
    (congrArg Sigma.fst e).symm).deleteMask
      (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))

/-- Both exact transforms of the original coefficient agree with the
computed table at every column of this actual direct cover. -/
theorem literalLeftDirectAtoms_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.leftSourceCover (raw).originalAtlas S χ).labels)
    (i : AllocationColumn K ((p.leftSourceCover (raw).originalAtlas S χ).branch label).slotCount)
    (hi : i ∈ ((p.leftSourceCover (raw).originalAtlas S χ).branch label).reindex.cartesian)
    (hSi : S.val ∣ (p.leftData.ideal
      (((p.leftSourceCover (raw).originalAtlas S χ).branch label).reindex.index i)).val) :
    (literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).whole i =
        p.leftDivisorCoefficient S χ
          (((p.leftSourceCover (raw).originalAtlas S χ).branch label).reindex.index i) *
          ((A.exteriorNorm (b.leftResidual
            (((p.leftSourceCover (raw).originalAtlas S χ).branch label).reindex.index i)) ^
              δ₂ : ℝ) : ℂ) *
          actualIdealResidue (A := A) (σ := σ) (b.leftResidual
            (((p.leftSourceCover (raw).originalAtlas S χ).branch label).reindex.index i)).val
            (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.1 label
  let T := (p.leftSourceCover (raw).originalAtlas S χ).branch label
  have e := literalLeftDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  have hc := canonicalLeftDirect_atlasCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    (primeSupport DE.1) branch hroot hemb T
    (fun _ hm => (Finset.mem_filter.mp hm).1) e i hi hSi firstFixed hfirst δ₂
  have hm := branch.atlas_full_mask_one T (fun _ hp => support_prime hp)
    (fun j => (raw).originalIndex (branch.reconstruct j)) e i hi
  unfold literalLeftDirectAtoms
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.deleteMask_whole _ _ i hi]
  rw [hc, hm, mul_one]

theorem literalRightDirectCover_dictionary
    (label : (p.rightSourceCover (raw).originalAtlas S χ).labels) :
    ((p.rightSourceCover (raw).originalAtlas S χ).branch label).literalDictionary =
      ⟨((raw).originalAtlas.branch (primeSupport DE.1) DE.2 label).keep.card,
        (SupportCartesian.plainResidual (seed).plain₁ (primeSupport DE.1)
          ((raw).originalAtlas.branch (primeSupport DE.1) DE.2 label).plainExtract₁,
        SupportCartesian.plainResidual (seed).plain₂ (primeSupport DE.1)
          ((raw).originalAtlas.branch (primeSupport DE.1) DE.2 label).plainExtract₂),
        (fun j => SupportCartesian.primeLive
          ((seed).slots (SlotRestriction.index
            ((raw).originalAtlas.branch (primeSupport DE.1) DE.2 label).keep j))
          (primeSupport DE.1)),
        (fun i => (raw).originalIndex
          (((raw).originalAtlas.branch (primeSupport DE.1) DE.2 label).reconstruct i))⟩ :=
  p.rightData.sourceCartesianCover_literalDictionary (raw).originalAtlas
    (primeSupport DE.1) DE.2 p.right_columns
    (fun i => by rw [p.right_ideal]; exact b.right_residual i)
    (p.rightDivisorCoefficient S χ) label

/-- This table contains both original rectangles and every actual
retained occurrence. Its supports are the existing direct cover fields. -/
def literalRightDirectAtoms
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.rightSourceCover (raw).originalAtlas S χ).labels) :
    CanonicalLiteralRectangles.Atoms (K := K)
      ((p.rightSourceCover (raw).originalAtlas S χ).branch label).slotCount :=
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.2 label
  let e := literalRightDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  let input := (seed).secondInput (σ := σ) branch P R (unitExterior A) firstFixed
    (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  (input.onAtlas ((p.rightSourceCover (raw).originalAtlas S χ).branch label)
    (congrArg Sigma.fst e).symm).deleteMask
      (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))

/-- Both exact transforms of the original coefficient agree with the
computed table at every column of this actual direct cover. -/
theorem literalRightDirectAtoms_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.rightSourceCover (raw).originalAtlas S χ).labels)
    (i : AllocationColumn K ((p.rightSourceCover (raw).originalAtlas S χ).branch label).slotCount)
    (hi : i ∈ ((p.rightSourceCover (raw).originalAtlas S χ).branch label).reindex.cartesian)
    (hSi : S.val ∣ (p.rightData.ideal
      (((p.rightSourceCover (raw).originalAtlas S χ).branch label).reindex.index i)).val) :
    (literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).whole i =
        p.rightDivisorCoefficient S χ
          (((p.rightSourceCover (raw).originalAtlas S χ).branch label).reindex.index i) *
          ((A.exteriorNorm (b.rightResidual
            (((p.rightSourceCover (raw).originalAtlas S χ).branch label).reindex.index i)) ^
              δ₂ : ℝ) : ℂ) *
          actualIdealResidue (A := A) (σ := σ) (b.rightResidual
            (((p.rightSourceCover (raw).originalAtlas S χ).branch label).reindex.index i)).val
            (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.2 label
  let T := (p.rightSourceCover (raw).originalAtlas S χ).branch label
  have e := literalRightDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  have hc := canonicalRightDirect_atlasCoefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    (primeSupport DE.1) branch hroot hemb T
    (fun _ hm => (Finset.mem_filter.mp hm).1) e i hi hSi firstFixed hfirst δ₂
  have hm := branch.atlas_full_mask_one T (fun _ hp => support_prime hp)
    (fun j => (raw).originalIndex (branch.reconstruct j)) e i hi
  unfold literalRightDirectAtoms
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.deleteMask_whole _ _ i hi]
  rw [hc, hm, mul_one]

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectAtoms_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightDirectAtoms_coefficient
