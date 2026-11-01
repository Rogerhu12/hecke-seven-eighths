import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSectorStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectParentFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PreparedOriginalFibreRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualPredicates
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualCharacters

/-!
# Actual direct second stages from the original moving source

Every second stage uses the actual signed first-divisor rows. The
retained endpoint is computed from the original common and physical
ideals; its enlargement is fixed before the second common label.
The original profile window supplies the physical row bound. The
original full-column norm window supplies the finite fibre dictionary.
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
variable (step : ℝ) (hstep : 0 < step)
variable (hloss : 0 ≤ loss) (hcutoffExponent : 0 ≤ cutoffExponent)

/-- This is fixed before a second common ideal or sector is selected. -/
def literalPrimitiveLeftDirectGeometry
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset) :
    OriginalNominalGeometry (K := K) internal Z step :=
  OriginalNominalGeometry.canonicalDirect
    (((source).block DE).literalLeftCoordinates D.val) (2 * loss + cutoffExponent)
    (zero_lt_one.trans hZ) (by positivity)

def literalPrimitiveRightDirectGeometry
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset) :
    OriginalNominalGeometry (K := K) internal Z step :=
  OriginalNominalGeometry.canonicalDirect
    (((source).block DE).literalRightCoordinates D.val) (2 * loss + cutoffExponent)
    (zero_lt_one.trans hZ) (by positivity)

local notation "leftGeometry" => Q.literalPrimitiveLeftDirectGeometry μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  loss cutoffExponent step hloss hcutoffExponent
local notation "rightGeometry" => Q.literalPrimitiveRightDirectGeometry μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  loss cutoffExponent step hloss hcutoffExponent

include hannulus hcap hannulusZ domain profiles hrows ht hwindow hcutoffPower hstep

/-- The actual left physical rows fit this computed second radius. -/
theorem literalPrimitiveLeftDirectRows
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset) :
    ∀ h ∈ ((source).pieces DE D).leftData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤
        (leftGeometry DE D).retainedScale * Z ^ (leftGeometry DE D).enlargement := by
  intro h hh
  have hp := Q.literalPrimitiveFirstSource_row_windows μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    cap annulus loss cutoffExponent hannulus hcap hannulusZ domain profiles hrows ht hwindow
    hcutoffPower DE D
  exact (hp.1 h hh).trans ((leftGeometry DE D).retainedScale_le_enlarged hZ.le hstep.le)

theorem literalPrimitiveRightDirectRows
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset) :
    ∀ h ∈ ((source).pieces DE D).rightData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤
        (rightGeometry DE D).retainedScale * Z ^ (rightGeometry DE D).enlargement := by
  intro h hh
  have hp := Q.literalPrimitiveFirstSource_row_windows μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    cap annulus loss cutoffExponent hannulus hcap hannulusZ domain profiles hrows ht hwindow
    hcutoffPower DE D
  exact (hp.2 h hh).trans ((rightGeometry DE D).retainedScale_le_enlarged hZ.le hstep.le)

local notation "leftRows" => Q.literalPrimitiveLeftDirectRows μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap annulus loss cutoffExponent hannulus hcap hannulusZ domain profiles hrows ht hwindow
  hcutoffPower step hstep hloss hcutoffExponent
local notation "rightRows" => Q.literalPrimitiveRightDirectRows μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap annulus loss cutoffExponent hannulus hcap hannulusZ domain profiles hrows ht hwindow
  hcutoffPower step hstep hloss hcutoffExponent

variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable (cutoff₂ : ℝ) (hcutoff₂ : 1 ≤ cutoff₂)

/-- All original direct sources are transformed, before the live
carrier or either Fourier variable is considered. -/
def literalPrimitiveDirectStages : (source).SecondStages (E := ℝ) (hDiff := hDiff) :=
  fun DE D => {
    left := fun S χ => ActualGaussStage.literalSectorStage
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ₂ hδ₂ hδ₂half
      (((source).pieces DE D).leftData.directSource
        (((source).pieces DE D).leftDivisorCoefficient S χ))
      (leftGeometry DE D).retainedScale Z (leftGeometry DE D).enlargement
      (leftGeometry DE D).retainedScale_pos (zero_lt_one.trans hZ)
      cutoff₂ hcutoff₂ (leftRows DE D)
    right := fun S χ => ActualGaussStage.literalSectorStage
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ₂ hδ₂ hδ₂half
      (((source).pieces DE D).rightData.directSource
        (((source).pieces DE D).rightDivisorCoefficient S χ))
      (rightGeometry DE D).retainedScale Z (rightGeometry DE D).enlargement
      (rightGeometry DE D).retainedScale_pos (zero_lt_one.trans hZ)
      cutoff₂ hcutoff₂ (rightRows DE D) }

local notation "stages" => Q.literalPrimitiveDirectStages μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap annulus loss cutoffExponent hannulus hcap hannulusZ domain profiles hrows ht hwindow
  hcutoffPower step hstep hloss hcutoffExponent hDiff δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂

/-- The original finite classifier transports the coarse full-column
window. It does not assume a bound on the transformed live fibre. -/
def literalPrimitiveDirectStagesOriginalFibreRows
    (B : ℝ) (hB : 0 ≤ B)
    (hN : ∀ i ∈ (source).columns, (Ideal.absNorm ((source).ideal i).val : ℝ) ≤ Z ^ B) :
    (stages).OriginalFibreRows
      (PUnit.{1} × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) 0 0 B Z where
  source DE D := {
    left := fun S χ => ActualGaussStage.literalSectorStageOriginalFibreRows
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ₂ hδ₂ hδ₂half
      (((source).pieces DE D).leftData.directSource
        (((source).pieces DE D).leftDivisorCoefficient S χ))
      (leftGeometry DE D).retainedScale Z (leftGeometry DE D).enlargement
      (leftGeometry DE D).retainedScale_pos (zero_lt_one.trans hZ)
      cutoff₂ hcutoff₂ (leftRows DE D) B hB hZ.le
      (((source).pieces DE D).left_ideal_norm_le (Z ^ B) hN)
    right := fun S χ => ActualGaussStage.literalSectorStageOriginalFibreRows
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ₂ hδ₂ hδ₂half
      (((source).pieces DE D).rightData.directSource
        (((source).pieces DE D).rightDivisorCoefficient S χ))
      (rightGeometry DE D).retainedScale Z (rightGeometry DE D).enlargement
      (rightGeometry DE D).retainedScale_pos (zero_lt_one.trans hZ)
      cutoff₂ hcutoff₂ (rightRows DE D) B hB hZ.le
      (((source).pieces DE D).right_ideal_norm_le (Z ^ B) hN) }


/-- The first moving phases are the generators already used by the
original signed first-divisor transform. -/
def literalPrimitiveDirectPredicates :
    (stages).prepared.CoverHybridPredicates (raw).originalAtlas :=
  fun DE D => {
    left := fun S χ => ((stages DE D).left S χ).supported.gated.literalHybridPredicates
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
      P R
      (CanonicalLiteralActualCharacters.unamplifiedPhases
        (((source).block DE).literalLeftFixed D.val)
        (CanonicalLiteralFirstPhase.leftElement C ((source).block DE).primes
          ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
          (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
        (((source).block DE).literalLeftFixed_generates C D.val))
      Q.moving Q.correction (data ξ).theta
    right := fun S χ => ((stages DE D).right S χ).supported.gated.literalHybridPredicates
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
      P R
      (CanonicalLiteralActualCharacters.unamplifiedPhases
        (((source).block DE).literalRightFixed D.val)
        (CanonicalLiteralFirstPhase.rightElement C ((source).block DE).primes
          ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
          (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
        (((source).block DE).literalRightFixed_generates C D.val))
      Q.moving Q.correction (data ξ).theta }

/-- The support and coefficient gates keep the same finite row code. -/
def literalPrimitivePreparedDirectStagesOriginalFibreRows
    (B : ℝ) (hB : 0 ≤ B)
    (hN : ∀ i ∈ (source).columns, (Ideal.absNorm ((source).ideal i).val : ℝ) ≤ Z ^ B) :
    (stages).prepared.OriginalFibreRows
      (PUnit.{1} × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) 0 0 B Z :=
  (Q.literalPrimitiveDirectStagesOriginalFibreRows μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    cap annulus loss cutoffExponent hannulus hcap hannulusZ domain profiles hrows ht hwindow
    hcutoffPower step hstep hloss hcutoffExponent hDiff δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂
    B hB hN).prepared

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftDirectRows
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightDirectRows
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectStages
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectStagesOriginalFibreRows

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectPredicates
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePreparedDirectStagesOriginalFibreRows
