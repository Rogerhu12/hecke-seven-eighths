import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralOriginalPoolStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualPredicates
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualCharacters

/-!
# All original amplified second stages and their finite classifiers

The same first source supplies each internal divisor, original prime
pool, main source and three valuation sources. Every row endpoint is
computed from its actual first ideals. The exceptional predicates use
the corresponding original unamplified or amplified moving phases.
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


local notation "firstSource" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

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


variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable (lengthBound columnBound : ℝ)
variable (hlengthBound : 0 ≤ lengthBound) (hcolumnBound : 0 ≤ columnBound)
variable (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
variable (hN : ∀ i ∈ (firstSource).columns,
  (Ideal.absNorm ((firstSource).ideal i).val : ℝ) ≤ Z ^ columnBound)
variable (hloss : 0 ≤ loss) (hcutoffExponent : 0 ≤ cutoffExponent)


variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {step eps : ℝ}
variable (pool : PowerScaleExteriorPool A bad Z (step / 3) eps)
variable (hdensity : 0 < pool.rowDensity
  (literalPrimitivePoolRowExponent (lengthBound := lengthBound) (columnBound := columnBound)
    (loss := loss) (cutoffExponent := cutoffExponent)) columnBound)
variable (hstep : 0 < step)

local notation "source" => Q.literalPrimitivePooledSource
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)

/-- Pool installation leaves the original first normalization ideals intact. -/
def literalPrimitivePooledNormalization : (source).Normalization :=
  (source).canonicalNormalization hZ
    (Q.literalPrimitiveFirstTotal μv ν C hroot hemb W ξ a Z t Y₁ Y₂ hZ hbudget
      centered cutoff hcutoff δ₁ hδ₁ hδ₁half)

/-- The pool retains the actual original signed rows at each internal divisor. -/
theorem literalPrimitiveLeftPooledRows
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pools DE D).rightData.columns
      (fun j => (((source).pools DE D).rightData.ideal j).val)) :
    ∀ h ∈ (((source).pools DE D).divisorPools.leftData S).rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤
        (((source).block DE).literalLeftCoordinates D.val).canonicalRetainedScale
          internal Z (2 * loss + cutoffExponent) := by
  rw [((source).pools DE D).divisorPools.left_rows S]
  exact (Q.literalPrimitiveFirstSource_row_windows μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    cap annulus loss cutoffExponent hannulus hcap hannulusZ domain profiles hrows ht hwindow
    hcutoffPower DE D).1

/-- The pool retains the actual original signed rows at each internal divisor. -/
theorem literalPrimitiveRightPooledRows
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pools DE D).rightData.columns
      (fun j => (((source).pools DE D).rightData.ideal j).val)) :
    ∀ h ∈ (((source).pools DE D).divisorPools.rightData S).rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤
        (((source).block DE).literalRightCoordinates D.val).canonicalRetainedScale
          internal Z (2 * loss + cutoffExponent) := by
  rw [((source).pools DE D).divisorPools.right_rows S]
  exact (Q.literalPrimitiveFirstSource_row_windows μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    cap annulus loss cutoffExponent hannulus hcap hannulusZ domain profiles hrows ht hwindow
    hcutoffPower DE D).2

variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable (cutoff₂ : ℝ) (hcutoff₂ : 1 ≤ cutoff₂)

local notation "leftRows" => Q.literalPrimitiveLeftPooledRows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)

local notation "rightRows" => Q.literalPrimitiveRightPooledRows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)

/-- Both sides contain the actual main, one, six and seven sources. -/
def literalPrimitivePooledStages : (source).SecondStages (E := ℝ) (hDiff := hDiff) :=
  fun DE D => {
    left := fun S χ => (((source).pools DE D).divisorPools.leftData S).literalCanonicalStages
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (ν := ν)
      (((source).pools DE D).leftDivisorCoefficient S χ) P internal
      (((source).block DE).literalLeftCoordinates D.val)
      (2 * loss + cutoffExponent) (by positivity) hstep (leftRows DE D S)
      δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂
    right := fun S χ => (((source).pools DE D).divisorPools.rightData S).literalCanonicalStages
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (ν := ν)
      (((source).pools DE D).rightDivisorCoefficient S χ) P internal
      (((source).block DE).literalRightCoordinates D.val)
      (2 * loss + cutoffExponent) (by positivity) hstep (rightRows DE D S)
      δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂
  }

local notation "stages" => Q.literalPrimitivePooledStages
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)
  (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

/-- The coarse original columns control the same finite physical row codes. -/
def literalPrimitivePooledStagesOriginalFibreRows :
    (stages).OriginalFibreRows
      (PUnit.{1} × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) 0 0 columnBound Z where
  source DE D := {
    left := fun S χ => (((source).pools DE D).divisorPools.leftData S).literalCanonicalStagesOriginalFibreRows
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (ν := ν)
      (((source).pools DE D).leftDivisorCoefficient S χ) P internal
      (((source).block DE).literalLeftCoordinates D.val)
      (2 * loss + cutoffExponent) (by positivity) hstep (leftRows DE D S)
      δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ columnBound hcolumnBound (by
        intro i hi
        rw [((source).pools DE D).divisorPools.left_columns S] at hi
        rw [((source).pools DE D).divisorPools.left_ideal S]
        exact ((source).pools DE D).left_ideal_norm_le (Z ^ columnBound) hN i hi)
    right := fun S χ => (((source).pools DE D).divisorPools.rightData S).literalCanonicalStagesOriginalFibreRows
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (ν := ν)
      (((source).pools DE D).rightDivisorCoefficient S χ) P internal
      (((source).block DE).literalRightCoordinates D.val)
      (2 * loss + cutoffExponent) (by positivity) hstep (rightRows DE D S)
      δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ columnBound hcolumnBound (by
        intro i hi
        rw [((source).pools DE D).divisorPools.right_columns S] at hi
        rw [((source).pools DE D).divisorPools.right_ideal S]
        exact ((source).pools DE D).right_ideal_norm_le (Z ^ columnBound) hN i hi)
  }

/-- These predicates read the original row character, including the
actual amplifier frequency before passive mask reduction. -/
def literalPrimitivePooledPredicates :
    (stages).supported.gated.CoverHybridPredicates (raw).originalAtlas :=
  fun DE D => {
    left := fun S χ => {
      main := (((stages DE D).left S χ).main).supported.gated.literalHybridPredicates
        ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).main)
        ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).main) P R
        (CanonicalLiteralActualCharacters.unamplifiedPhases
          (((source).block DE).literalLeftFixed D.val)
          (CanonicalLiteralFirstPhase.leftElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
          (((source).block DE).literalLeftFixed_generates C D.val))
        Q.moving Q.correction (data ξ).theta
      one p := (((stages DE D).left S χ).one p).supported.gated.literalHybridPredicates
        ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual p 1)
        ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual p 1) P R
        (CanonicalLiteralActualCharacters.amplifiedPhases C
          (((source).block DE).literalLeftFixed D.val)
          (CanonicalLiteralFirstPhase.leftElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
          (((source).block DE).literalLeftFixed_generates C D.val) p.val 1)
        Q.moving Q.correction (data ξ).theta
      six p := (((stages DE D).left S χ).six p).supported.gated.literalHybridPredicates
        ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual p 6)
        ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual p 6) P R
        (CanonicalLiteralActualCharacters.amplifiedPhases C
          (((source).block DE).literalLeftFixed D.val)
          (CanonicalLiteralFirstPhase.leftElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
          (((source).block DE).literalLeftFixed_generates C D.val) p.val 6)
        Q.moving Q.correction (data ξ).theta
      seven p := (((stages DE D).left S χ).seven p).supported.gated.literalHybridPredicates
        ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual p 7)
        ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual p 7) P R
        (CanonicalLiteralActualCharacters.amplifiedPhases C
          (((source).block DE).literalLeftFixed D.val)
          (CanonicalLiteralFirstPhase.leftElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
          (((source).block DE).literalLeftFixed_generates C D.val) p.val 7)
        Q.moving Q.correction (data ξ).theta
    }
    right := fun S χ => {
      main := (((stages DE D).right S χ).main).supported.gated.literalHybridPredicates
        ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).main)
        ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).main) P R
        (CanonicalLiteralActualCharacters.unamplifiedPhases
          (((source).block DE).literalRightFixed D.val)
          (CanonicalLiteralFirstPhase.rightElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
          (((source).block DE).literalRightFixed_generates C D.val))
        Q.moving Q.correction (data ξ).theta
      one p := (((stages DE D).right S χ).one p).supported.gated.literalHybridPredicates
        ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual p 1)
        ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual p 1) P R
        (CanonicalLiteralActualCharacters.amplifiedPhases C
          (((source).block DE).literalRightFixed D.val)
          (CanonicalLiteralFirstPhase.rightElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
          (((source).block DE).literalRightFixed_generates C D.val) p.val 1)
        Q.moving Q.correction (data ξ).theta
      six p := (((stages DE D).right S χ).six p).supported.gated.literalHybridPredicates
        ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual p 6)
        ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual p 6) P R
        (CanonicalLiteralActualCharacters.amplifiedPhases C
          (((source).block DE).literalRightFixed D.val)
          (CanonicalLiteralFirstPhase.rightElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
          (((source).block DE).literalRightFixed_generates C D.val) p.val 6)
        Q.moving Q.correction (data ξ).theta
      seven p := (((stages DE D).right S χ).seven p).supported.gated.literalHybridPredicates
        ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual p 7)
        ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual p 7) P R
        (CanonicalLiteralActualCharacters.amplifiedPhases C
          (((source).block DE).literalRightFixed D.val)
          (CanonicalLiteralFirstPhase.rightElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
          (((source).block DE).literalRightFixed_generates C D.val) p.val 7)
        Q.moving Q.correction (data ξ).theta
    }
  }

/-- Support and coefficient gates preserve the original classifiers. -/
def literalPrimitivePreparedPooledStagesOriginalFibreRows :
    (stages).supported.gated.OriginalFibreRows
      (PUnit.{1} × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) 0 0 columnBound Z :=
  (Q.literalPrimitivePooledStagesOriginalFibreRows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)
    (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)).supported.gated

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledNormalization
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftPooledRows
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightPooledRows
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledStages
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledStagesOriginalFibreRows
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledPredicates
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePreparedPooledStagesOriginalFibreRows
