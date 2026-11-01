import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActiveGaussColumns
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalActiveColumnNorm

/-!
# Sharp active columns on the actual original direct source

The original single-profile support and original centered comparison
identity give the sharp whole-column bound. The first residual source
then removes its actual full common ideal. Coefficient gates remain in
place; no estimate on a completed child is used.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
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
variable {ω ψ : HeckeCharacter K} {Index : Type*} {data : Index → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (W : NormProfileRecipe data) (ξ : Index)
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 1 < Z)
variable (hbudget : Q.FullJointBudget Z (a.m + a.q))
variable (centered : Bool) (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁half : δ₁ ≤ 1 / 2)

local notation "internal" => Q.fullSupportParameters a Z
local notation "atoms" => (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) internal Z t
local notation "raw" => (atoms).raw Y₁ Y₂


local notation "source" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
local notation "coefficient" => ((atoms).values Y₁ Y₂).coefficient centered

variable (cap : ℕ) (annulus loss cutoffExponent : ℝ)
variable (hannulus : 1 ≤ annulus) (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) amplitude)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
variable (hcutoffPower : cutoff ≤ Z ^ cutoffExponent)

include hannulus hcap hannulusZ domain profiles hrows ht hwindow


theorem literalPrimitiveFirstSource_active_column_norm
    (i : (raw).Column) (hi : i ∈ (raw).exteriorColumns) (hc : coefficient i ≠ 0) :
    A.exteriorNorm ((raw).columnExterior i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z + loss) := by
  have hrows' : ∀ u ∈ pairedRows (data ξ) internal Z, u ∈ rowDomain := by
    simpa only [Q.literalPrimitiveFirstSource_pairedRows] using hrows
  have hd := domain.withSupportLength (Q.fullSupportLength Z)
  have h := (atoms).original_active_column_norm_le_power profiles cap annulus loss
    hannulus hcap hannulusZ (zero_lt_one.trans hZ) hrows' ht hwindow centered
    hd.comparison_scale_left_nonneg hd.comparison_product_eq_power i hi hc
  simpa only [hd.total_length] using h

theorem literalPrimitiveDirectLeft_active_norm
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pieces DE D).rightData.columns
      (fun j => (((source).pieces DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (i : (raw).Column)
    (hi : i ∈ ((source).pieces DE D).leftData.columns)
    (hc : ((source).pieces DE D).leftDivisorCoefficient S χ i ≠ 0) :
    A.exteriorNorm (((source).pieces DE D).leftData.ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z - idealLogLength Z DE.val.1 + loss) := by
  have hfull := literalPrimitiveFirstSource_active_column_norm
    (Q := Q) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t)
    (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (centered := centered)
    (cap := cap) (annulus := annulus) (loss := loss)
    (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ)
    (domain := domain) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow)
  have h := ((source).pieces DE D).canonicalLeft_active_norm_window
    (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv ν
    ((source).block DE) C (source).columns (source).columns (CanonicalRowBall.archTest K A.Sf 1)
    coefficient coefficient (rowBallFiniteFamily K A.Sf 1)
    (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1)
    (source).radius D.val δ₁ hδ₁ hδ₁half S χ Z
    ((internal).n₁ + (internal).n₂ + (internal).z + loss) hZ hfull i hi hc
  convert h using 1 <;> congr 1 <;> ring

theorem literalPrimitiveDirectRight_active_norm
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pieces DE D).rightData.columns
      (fun j => (((source).pieces DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (i : (raw).Column)
    (hi : i ∈ ((source).pieces DE D).rightData.columns)
    (hc : ((source).pieces DE D).rightDivisorCoefficient S χ i ≠ 0) :
    A.exteriorNorm (((source).pieces DE D).rightData.ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z - idealLogLength Z DE.val.2 + loss) := by
  have hfull := literalPrimitiveFirstSource_active_column_norm
    (Q := Q) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t)
    (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (centered := centered)
    (cap := cap) (annulus := annulus) (loss := loss)
    (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ)
    (domain := domain) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow)
  have h := ((source).pieces DE D).canonicalRight_active_norm_window
    (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv ν
    ((source).block DE) C (source).columns (source).columns (CanonicalRowBall.archTest K A.Sf 1)
    coefficient coefficient (rowBallFiniteFamily K A.Sf 1)
    (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1)
    (source).radius D.val δ₁ hδ₁ hδ₁half S χ Z
    ((internal).n₁ + (internal).n₂ + (internal).z + loss) hZ hfull i hi hc
  convert h using 1 <;> congr 1 <;> ring

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveFirstSource_active_column_norm
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectLeft_active_norm
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectRight_active_norm
