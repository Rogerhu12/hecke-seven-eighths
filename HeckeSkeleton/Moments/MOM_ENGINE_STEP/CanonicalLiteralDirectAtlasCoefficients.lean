import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectCoefficients
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectAtlas

/-!
# Original direct coefficients on the already constructed source atlas

The table is computed from the original two rectangles and transported
through the existing occurrence dictionary. The actual atlas itself
proves the column membership, ideal product and original index needed
by the two-stage coefficient calculation. No whole-column identity is
requested from the caller. The only arithmetic gate is the original
first divisor, supplied on live common labels by the existing source
support theorem.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
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
variable (support : Finset (Ideal (𝓞 K)))
variable (branch : SupportCartesianBranch
  (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
  (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
  (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots support)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)

include hroot hemb

/-- The actual left direct coefficient is obtained from the original
atom table on the existing cover. The same tuple is used throughout. -/
theorem canonicalLeftDirect_atlasCoefficient
    {columns : Finset (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).Column}
    (T : SourceCartesianAtlas columns p.leftData.ideal)
    (hcolumns : columns ⊆ p.leftData.columns)
    (e : T.literalDictionary =
      ⟨branch.keep.card,
        (SupportCartesian.plainResidual (seed).plain₁ support branch.plainExtract₁,
          SupportCartesian.plainResidual (seed).plain₂ support branch.plainExtract₂),
        (fun j => SupportCartesian.primeLive
          ((seed).slots (SlotRestriction.index branch.keep j)) support),
        (fun i => (raw).originalIndex (branch.reconstruct i))⟩)
    (i : AllocationColumn K T.slotCount) (hi : i ∈ T.reindex.cartesian)
    (hSi : S.val ∣ (p.leftData.ideal (T.reindex.index i)).val)
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) :
    let input := (seed).secondInput (σ := σ) branch P R (unitExterior A) firstFixed
      (unitExterior A) (unitExterior A)
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
      hfirst (unitExterior_generates A)
      CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
    (input.onAtlas T (congrArg Sigma.fst e).symm).whole i =
      p.leftDivisorCoefficient S χ (T.reindex.index i) *
        ((A.exteriorNorm (b.leftResidual (T.reindex.index i)) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (b.leftResidual (T.reindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.onAtlas_whole]
  let j := CanonicalLiteralAtlasAtoms.castColumn (congrArg Sigma.fst e) i
  have hj : j ∈ branch.residualColumns :=
    (CanonicalLiteralAtlasAtoms.dictionary_membership e i).mp hi
  have hindex : T.reindex.index i = (raw).originalIndex (branch.reconstruct j) :=
    CanonicalLiteralAtlasAtoms.dictionary_index e i
  have hideal : (b.leftResidual (T.reindex.index i)).val = allocationColumnIdeal j := by
    have he := T.reindex.ideal_product i hi
    rw [p.left_ideal] at he
    exact he.trans (CanonicalLiteralAtlasAtoms.castColumn_ideal
      (congrArg Sigma.fst e) i).symm
  exact CompleteMovingRowRecipe.canonicalLeftDirect_secondInput hΓ μv ν
    Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D
    δ₁ hδ₁ hδ₁half p S χ support branch hroot hemb
    (T.reindex.index i) (hcolumns (T.reindex.maps i hi)) j hj hindex hideal hSi
    firstFixed hfirst δ₂

/-- The actual right direct coefficient is obtained from the original
atom table on the existing cover. The same tuple is used throughout. -/
theorem canonicalRightDirect_atlasCoefficient
    {columns : Finset (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).Column}
    (T : SourceCartesianAtlas columns p.rightData.ideal)
    (hcolumns : columns ⊆ p.rightData.columns)
    (e : T.literalDictionary =
      ⟨branch.keep.card,
        (SupportCartesian.plainResidual (seed).plain₁ support branch.plainExtract₁,
          SupportCartesian.plainResidual (seed).plain₂ support branch.plainExtract₂),
        (fun j => SupportCartesian.primeLive
          ((seed).slots (SlotRestriction.index branch.keep j)) support),
        (fun i => (raw).originalIndex (branch.reconstruct i))⟩)
    (i : AllocationColumn K T.slotCount) (hi : i ∈ T.reindex.cartesian)
    (hSi : S.val ∣ (p.rightData.ideal (T.reindex.index i)).val)
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) :
    let input := (seed).secondInput (σ := σ) branch P R (unitExterior A) firstFixed
      (unitExterior A) (unitExterior A)
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
      hfirst (unitExterior_generates A)
      CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
    (input.onAtlas T (congrArg Sigma.fst e).symm).whole i =
      p.rightDivisorCoefficient S χ (T.reindex.index i) *
        ((A.exteriorNorm (b.rightResidual (T.reindex.index i)) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (b.rightResidual (T.reindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  dsimp only
  rw [CanonicalLiteralRectangles.Atoms.onAtlas_whole]
  let j := CanonicalLiteralAtlasAtoms.castColumn (congrArg Sigma.fst e) i
  have hj : j ∈ branch.residualColumns :=
    (CanonicalLiteralAtlasAtoms.dictionary_membership e i).mp hi
  have hindex : T.reindex.index i = (raw).originalIndex (branch.reconstruct j) :=
    CanonicalLiteralAtlasAtoms.dictionary_index e i
  have hideal : (b.rightResidual (T.reindex.index i)).val = allocationColumnIdeal j := by
    have he := T.reindex.ideal_product i hi
    rw [p.right_ideal] at he
    exact he.trans (CanonicalLiteralAtlasAtoms.castColumn_ideal
      (congrArg Sigma.fst e) i).symm
  exact CompleteMovingRowRecipe.canonicalRightDirect_secondInput hΓ μv ν
    Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D
    δ₁ hδ₁ hδ₁half p S χ support branch hroot hemb
    (T.reindex.index i) (hcolumns (T.reindex.maps i hi)) j hj hindex hideal hSi
    firstFixed hfirst δ₂

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftDirect_atlasCoefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightDirect_atlasCoefficient
