import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPreparedBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LiveSourceConditions

/-!
# Literal normalization binding on the actual valuation leaves

The actual prime, its valuation exponent and the original subtype are
retained throughout. The literal orbital fibre in the same live leaf
supplies the physical row. Hence this prime avoids the original frozen
divisor, and the original first-divisor gate passes to the residual
ideal. The reconstructed original ideal gives the first Fourier point.

The two rectangles, complete first-support deletion, both Fourier
kernels and every coefficient are the previously computed original
ones. No identity of whole polynomials, replacement source, or final
bound is a constructor argument. The construction works for any
valuation exponent; the source uses its original exponents 1, 6 and 7.
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
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable (retainedScale g : ℝ) (hscale : 0 < retainedScale)
variable (cutoff₂ : ℝ) (hcutoff₂ : 1 ≤ cutoff₂)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
variable (q : pool.primes) (n : ℕ)

section LiteralLeftPoolBinding

variable (hnorm : ∀ h ∈ (p.divisorPools.leftData S).errorRows q.val,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns
  (fun i => (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i).val) (fun i => (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns
  (fun i => (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i).val) (fun i => (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (p.leftSourceCovers (raw).originalAtlas S χ).residual q n
local notation "firstPoint" => (fun i : (p.divisorPools.leftData S).valuationColumns q.val n =>
  -Real.log (A.exteriorNorm (b.leftResidual i.val)))

variable (v : (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey
  ((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n) ((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates
  ((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n) ((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.leftElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "leftAtoms" => literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.1
local notation "rightAtoms" => literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.2.1

include hroot hemb in
private theorem literalLeftPool_leftAtoms_coefficient
    (hdiv : S.val ∣ v.1.val.1)
    (i : AllocationColumn K ((cover).branch v.2.2.1).slotCount)
    (hi : i ∈ ((cover).branch v.2.2.1).reindex.cartesian)
    (hc : ((cover).branch v.2.2.1).reindex.index i ∈ v.block.leftColumns ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns) :
    (leftAtoms).whole i =
      ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).coefficient (((cover).branch v.2.2.1).reindex.index i) *
        ((A.exteriorNorm (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.1).reindex.index i)) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ)
          (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.1).reindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  let idx := ((cover).branch v.2.2.1).reindex.index i
  have hres := v.block.left_divisor_of_common ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns S.val hdiv _ hc
  have hSi : S.val ∣ ((p.divisorPools.leftData S).ideal idx.val).val := by
    rw [((p.divisorPools.leftData S).residualPresentation q.val n idx).reconstructed]
    exact dvd_mul_of_dvd_right hres _
  rw [p.divisorPools.left_ideal S] at hSi
  exact literalLeftPoolAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hroot hemb firstFixed hfirst δ₂ q n v.2.2.1 i hi hSi

include hroot hemb in
private theorem literalLeftPool_rightAtoms_coefficient
    (hdiv : S.val ∣ v.1.val.2)
    (i : AllocationColumn K ((cover).branch v.2.2.2.1).slotCount)
    (hi : i ∈ ((cover).branch v.2.2.2.1).reindex.cartesian)
    (hc : ((cover).branch v.2.2.2.1).reindex.index i ∈ v.block.rightColumns ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns) :
    (rightAtoms).whole i =
      ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).coefficient (((cover).branch v.2.2.2.1).reindex.index i) *
        ((A.exteriorNorm (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.2.1).reindex.index i)) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ)
          (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.2.1).reindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  let idx := ((cover).branch v.2.2.2.1).reindex.index i
  have hres := v.block.right_divisor_of_common ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns S.val hdiv _ hc
  have hSi : S.val ∣ ((p.divisorPools.leftData S).ideal idx.val).val := by
    rw [((p.divisorPools.leftData S).residualPresentation q.val n idx).reconstructed]
    exact dvd_mul_of_dvd_right hres _
  rw [p.divisorPools.left_ideal S] at hSi
  exact literalLeftPoolAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hroot hemb firstFixed hfirst δ₂ q n v.2.2.2.1 i hi hSi

private theorem literalLeftPool_bareLive
    (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover exceptional F firstPoint
      ⟨v, j⟩).Live) :
    (v.leaf exceptional F firstPoint j).Live :=
  (v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hlive

/-- The physical support is read from the actual fibre coefficient.
It proves that removing this valuation leaves the original first
squarefree divisor in both common ideals. -/
private theorem literalLeftPool_live_common
    (hS : Squarefree S.val)
    (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover exceptional F firstPoint
      ⟨v, j⟩).Live) :
    S.val ∣ v.1.val.1 ∧ S.val ∣ v.1.val.2 := by
  have hs := (stage).supported_gated_fiberLeaf_live cover cover exceptional F firstPoint
    ⟨v, j⟩ hlive
  exact ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).activeCommon_old_mask S.val hS
    (fun i _ hci => (p.divisorPools.leftData S).residualSource_nonzero_dvd q.val n
      (p.leftDivisorCoefficient S χ) S.val (p.firstDivisor_dvd_left_frozen S)
      (fun i _ hi => p.leftDivisorCoefficient_nonzero_dvd S χ i hi) hs.1 i hci)
    v.1.val hs.2.1

/-- Full common extraction of the actual valuation leaf. The physical
nonempty condition was not added; it follows from this leaf's weight. -/
def literalLeftPoolExtraction
    (hS : Squarefree S.val)
    (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover exceptional F firstPoint
      ⟨v, j⟩).Live) :
    (v.leaf exceptional F firstPoint j).ConstantAtomExtraction := by
  have hs := literalLeftPool_live_common (v := v) (exceptional := exceptional)
    (F := F) (j := j) hS hlive
  have hb := literalLeftPool_bareLive (v := v) (exceptional := exceptional)
    (F := F) (j := j) hlive
  exact ActualGaussStage.preparedLiteralExtraction
    (v := v) (exceptional := exceptional) (F := F) (x := firstPoint) (j := j)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (hcoeffL := literalLeftPool_leftAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width q n hnorm character dyad v firstFixed hfirst hs.1)
    (hcoeffR := literalLeftPool_rightAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width q n hnorm character dyad v firstFixed hfirst hs.2) hb

def literalLeftPoolRectangles
    (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover exceptional F firstPoint
      ⟨v, j⟩).Live) :=
  v.literalRectangles leftAtoms rightAtoms exceptional F firstPoint j 1
    (literalLeftPool_bareLive (v := v) (exceptional := exceptional) (F := F) (j := j) hlive)

/-- This is the original source point, reconstructed from its actual
valuation quotient and its original prime power. -/
private theorem literalLeftPool_firstPoint :
    ∀ i, firstPoint i = -(1 : ℝ) * Real.log
      (A.exteriorNorm (ExteriorIdealEuler.mul (powerIdeal q.val n) (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i))) := by
  intro i
  have he := ((p.divisorPools.leftData S).residualPresentation q.val n i).reconstructed
  rw [p.divisorPools.left_ideal S, p.left_ideal] at he
  change _ = -(1 : ℝ) * Real.log
    (Ideal.absNorm (q.val.val.asIdeal ^ n * ((p.divisorPools.leftData S).residualPresentation q.val n i).residual.val) : ℝ)
  rw [← he]
  simp only [neg_neg, neg_one_mul, one_mul]

/-- Complete two-rectangle ordinary binding on the same stored leaf,
with no replacement of the actual prime, exponent, row or column. -/
def literalLeftPoolOrdinaryBinding
    (hS : Squarefree S.val)
    (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover exceptional F firstPoint
      ⟨v, j⟩).Live) :
    (literalLeftPoolExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width q n hnorm character dyad v exceptional F firstFixed hfirst j hS hlive).leaf.OrdinaryBinding
      (literalLeftPoolRectangles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        hDiff δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
        dimension width q n hnorm character dyad v exceptional F firstFixed hfirst j hlive) := by
  have hs := literalLeftPool_live_common (v := v) (exceptional := exceptional)
    (F := F) (j := j) hS hlive
  have hb := literalLeftPool_bareLive (v := v) (exceptional := exceptional)
    (F := F) (j := j) hlive
  exact ActualGaussStage.preparedLiteralOrdinaryBinding
    (v := v) (exceptional := exceptional) (F := F) (x := firstPoint) (j := j)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (hcoeffL := literalLeftPool_leftAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width q n hnorm character dyad v firstFixed hfirst hs.1)
    (hcoeffR := literalLeftPool_rightAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width q n hnorm character dyad v firstFixed hfirst hs.2)
    (power := powerIdeal q.val n) (firstSign := 1)
    (literalLeftPool_firstPoint (p := p) (S := S) (χ := χ) (q := q) (n := n)) hb

end LiteralLeftPoolBinding

section LiteralRightPoolBinding

variable (hnorm : ∀ h ∈ (p.divisorPools.rightData S).errorRows q.val,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns
  (fun i => (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i).val) (fun i => (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns
  (fun i => (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i).val) (fun i => (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (p.rightSourceCovers (raw).originalAtlas S χ).residual q n
local notation "firstPoint" => (fun i : (p.divisorPools.rightData S).valuationColumns q.val n =>
  Real.log (A.exteriorNorm (b.rightResidual i.val)))

variable (v : (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey
  ((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n) ((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates
  ((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n) ((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.rightElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "leftAtoms" => literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.1
local notation "rightAtoms" => literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.2.1

include hroot hemb in
private theorem literalRightPool_leftAtoms_coefficient
    (hdiv : S.val ∣ v.1.val.1)
    (i : AllocationColumn K ((cover).branch v.2.2.1).slotCount)
    (hi : i ∈ ((cover).branch v.2.2.1).reindex.cartesian)
    (hc : ((cover).branch v.2.2.1).reindex.index i ∈ v.block.leftColumns ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns) :
    (leftAtoms).whole i =
      ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).coefficient (((cover).branch v.2.2.1).reindex.index i) *
        ((A.exteriorNorm (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.1).reindex.index i)) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ)
          (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.1).reindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  let idx := ((cover).branch v.2.2.1).reindex.index i
  have hres := v.block.left_divisor_of_common ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns S.val hdiv _ hc
  have hSi : S.val ∣ ((p.divisorPools.rightData S).ideal idx.val).val := by
    rw [((p.divisorPools.rightData S).residualPresentation q.val n idx).reconstructed]
    exact dvd_mul_of_dvd_right hres _
  rw [p.divisorPools.right_ideal S] at hSi
  exact literalRightPoolAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hroot hemb firstFixed hfirst δ₂ q n v.2.2.1 i hi hSi

include hroot hemb in
private theorem literalRightPool_rightAtoms_coefficient
    (hdiv : S.val ∣ v.1.val.2)
    (i : AllocationColumn K ((cover).branch v.2.2.2.1).slotCount)
    (hi : i ∈ ((cover).branch v.2.2.2.1).reindex.cartesian)
    (hc : ((cover).branch v.2.2.2.1).reindex.index i ∈ v.block.rightColumns ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns) :
    (rightAtoms).whole i =
      ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).coefficient (((cover).branch v.2.2.2.1).reindex.index i) *
        ((A.exteriorNorm (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.2.1).reindex.index i)) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ)
          (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal (((cover).branch v.2.2.2.1).reindex.index i)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  let idx := ((cover).branch v.2.2.2.1).reindex.index i
  have hres := v.block.right_divisor_of_common ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns S.val hdiv _ hc
  have hSi : S.val ∣ ((p.divisorPools.rightData S).ideal idx.val).val := by
    rw [((p.divisorPools.rightData S).residualPresentation q.val n idx).reconstructed]
    exact dvd_mul_of_dvd_right hres _
  rw [p.divisorPools.right_ideal S] at hSi
  exact literalRightPoolAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hroot hemb firstFixed hfirst δ₂ q n v.2.2.2.1 i hi hSi

private theorem literalRightPool_bareLive
    (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover exceptional F firstPoint
      ⟨v, j⟩).Live) :
    (v.leaf exceptional F firstPoint j).Live :=
  (v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hlive

/-- The physical support is read from the actual fibre coefficient.
It proves that removing this valuation leaves the original first
squarefree divisor in both common ideals. -/
private theorem literalRightPool_live_common
    (hS : Squarefree S.val)
    (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover exceptional F firstPoint
      ⟨v, j⟩).Live) :
    S.val ∣ v.1.val.1 ∧ S.val ∣ v.1.val.2 := by
  have hs := (stage).supported_gated_fiberLeaf_live cover cover exceptional F firstPoint
    ⟨v, j⟩ hlive
  exact ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).activeCommon_old_mask S.val hS
    (fun i _ hci => (p.divisorPools.rightData S).residualSource_nonzero_dvd q.val n
      (p.rightDivisorCoefficient S χ) S.val (p.firstDivisor_dvd_right_frozen S)
      (fun i _ hi => p.rightDivisorCoefficient_nonzero_dvd S χ i hi) hs.1 i hci)
    v.1.val hs.2.1

/-- Full common extraction of the actual valuation leaf. The physical
nonempty condition was not added; it follows from this leaf's weight. -/
def literalRightPoolExtraction
    (hS : Squarefree S.val)
    (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover exceptional F firstPoint
      ⟨v, j⟩).Live) :
    (v.leaf exceptional F firstPoint j).ConstantAtomExtraction := by
  have hs := literalRightPool_live_common (v := v) (exceptional := exceptional)
    (F := F) (j := j) hS hlive
  have hb := literalRightPool_bareLive (v := v) (exceptional := exceptional)
    (F := F) (j := j) hlive
  exact ActualGaussStage.preparedLiteralExtraction
    (v := v) (exceptional := exceptional) (F := F) (x := firstPoint) (j := j)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (hcoeffL := literalRightPool_leftAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width q n hnorm character dyad v firstFixed hfirst hs.1)
    (hcoeffR := literalRightPool_rightAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width q n hnorm character dyad v firstFixed hfirst hs.2) hb

def literalRightPoolRectangles
    (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover exceptional F firstPoint
      ⟨v, j⟩).Live) :=
  v.literalRectangles leftAtoms rightAtoms exceptional F firstPoint j (-1)
    (literalRightPool_bareLive (v := v) (exceptional := exceptional) (F := F) (j := j) hlive)

/-- This is the original source point, reconstructed from its actual
valuation quotient and its original prime power. -/
private theorem literalRightPool_firstPoint :
    ∀ i, firstPoint i = -((-1) : ℝ) * Real.log
      (A.exteriorNorm (ExteriorIdealEuler.mul (powerIdeal q.val n) (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i))) := by
  intro i
  have he := ((p.divisorPools.rightData S).residualPresentation q.val n i).reconstructed
  rw [p.divisorPools.right_ideal S, p.right_ideal] at he
  change _ = -((-1) : ℝ) * Real.log
    (Ideal.absNorm (q.val.val.asIdeal ^ n * ((p.divisorPools.rightData S).residualPresentation q.val n i).residual.val) : ℝ)
  rw [← he]
  simp only [neg_neg, neg_one_mul, one_mul]

/-- Complete two-rectangle ordinary binding on the same stored leaf,
with no replacement of the actual prime, exponent, row or column. -/
def literalRightPoolOrdinaryBinding
    (hS : Squarefree S.val)
    (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover exceptional F firstPoint
      ⟨v, j⟩).Live) :
    (literalRightPoolExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width q n hnorm character dyad v exceptional F firstFixed hfirst j hS hlive).leaf.OrdinaryBinding
      (literalRightPoolRectangles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
        hDiff δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
        dimension width q n hnorm character dyad v exceptional F firstFixed hfirst j hlive) := by
  have hs := literalRightPool_live_common (v := v) (exceptional := exceptional)
    (F := F) (j := j) hS hlive
  have hb := literalRightPool_bareLive (v := v) (exceptional := exceptional)
    (F := F) (j := j) hlive
  exact ActualGaussStage.preparedLiteralOrdinaryBinding
    (v := v) (exceptional := exceptional) (F := F) (x := firstPoint) (j := j)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (hcoeffL := literalRightPool_leftAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width q n hnorm character dyad v firstFixed hfirst hs.1)
    (hcoeffR := literalRightPool_rightAtoms_coefficient hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
      dimension width q n hnorm character dyad v firstFixed hfirst hs.2)
    (power := powerIdeal q.val n) (firstSign := (-1))
    (literalRightPool_firstPoint (p := p) (S := S) (χ := χ) (q := q) (n := n)) hb

end LiteralRightPoolBinding

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolOrdinaryBinding
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolOrdinaryBinding
