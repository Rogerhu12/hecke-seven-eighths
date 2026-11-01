import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSourceCoordinates
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDirectParentWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogMetadata

/-!
# The literal first source from the original moving recipe

The full old support determines the internal split of the original
width. The actual first source, its original Cartesian atlas and its
two first allowances are then constructed from that same recipe.
The original single-profile window proves each first physical cutoff
and both signed Gauss-row windows at the computed retained endpoint.
There is no supplied first source, Gauss data, or row-window certificate.
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

@[simp] theorem fullSupportParameters_idempotent (a : RealParameters) (Z : ℝ) :
    Q.fullSupportParameters (Q.fullSupportParameters a Z) Z =
      Q.fullSupportParameters a Z := by
  unfold fullSupportParameters withSupportLength
  congr 1 <;> ring

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

/-- The first source is selected before any original common label or
Fourier parameter of either transform. Its old deletion support is paid
by the literal internal `q`. -/
def literalPrimitiveFirstSource :
    ActualDirectFirstSource
      (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (E := ℝ) (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv C Z (rowBallFiniteFamily K A.Sf 1)
      centered (data ξ) internal t Y₁ Y₂ cutoff hcutoff :=
  Q.canonicalFullSupportDirectFirstSource μv ν C hroot hemb W ξ internal Z t Y₁ Y₂
    (zero_lt_one.trans hZ)
    (by simpa only [Q.fullSupportParameters_width] using hbudget)
    centered cutoff hcutoff δ₁ hδ₁ hδ₁half

local notation "source" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

/-- The original exterior Cartesian atlas of the same actual source. -/
def literalPrimitiveFirstAtlas : SourceCartesianAtlas (source).columns (source).ideal :=
  (raw).originalAtlas

@[simp] theorem literalPrimitiveFirstAtlas_slotCount :
    (Q.literalPrimitiveFirstAtlas μv ν C hroot hemb W ξ a Z t Y₁ Y₂ hZ hbudget
      centered cutoff hcutoff δ₁ hδ₁ hδ₁half).slotCount = (data ξ).geometry.slotCount := rfl

/-- The first normalization uses the original selected physical
divisor and active common radical, with their full norm lengths. -/
def literalPrimitiveFirstTotal (DE : (source).CommonLabel)
    (D : (((source).block DE).mask (source).mask).powerset) : ℝ :=
  (internal).n₁ + (internal).n₂ + (internal).z + (internal).q +
    idealLogLength Z (firstActiveRadical DE.val.1 DE.val.2) +
    idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val

def literalPrimitiveFirstNormalization : (source).Normalization :=
  (source).canonicalNormalization hZ
    (Q.literalPrimitiveFirstTotal μv ν C hroot hemb W ξ a Z t Y₁ Y₂ hZ hbudget
      centered cutoff hcutoff δ₁ hδ₁ hδ₁half)

@[simp] theorem literalPrimitiveFirstSource_fiber : (source).fiber = 1 := rfl

@[simp] theorem literalPrimitiveFirstSource_mask : (source).mask = ∅ := rfl

theorem literalPrimitiveFirstSource_radius :
    (source).radius.val = Z ^ (-(internal).m) := by
  change (Q.fullSupportRadius Z ((internal).m + (internal).q)
    (zero_lt_one.trans hZ)).val = _
  rw [Q.fullSupportParameters_width]
  exact Q.fullSupportRadius_eq_negative_m a Z hZ

include hZ in
theorem literalPrimitiveFirstSource_oldSupport :
    A.exteriorNorm (Q.moving.effectiveFullSupport Q.remaining) ≤ Z ^ (internal).q :=
  (Q.fullSupportParameters_support_norm a Z hZ).le

theorem literalPrimitiveFirstSource_domain {floor padding : ℝ}
    (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding) :
    PairedEngineDomain centered (data ξ) internal Z Y₁ Y₂ floor padding :=
  domain.withSupportLength (Q.fullSupportLength Z)

theorem literalPrimitiveFirstSource_pairedRows :
    pairedRows (data ξ) internal Z = pairedRows (data ξ) a Z :=
  pairedRows_withSupportLength (data ξ) a (Q.fullSupportLength Z) Z

theorem literalPrimitiveFirstSource_parent :
    pairedStageEnergy centered (data ξ) internal Z t Y₁ Y₂ =
      pairedStageEnergy centered (data ξ) a Z t Y₁ Y₂ :=
  pairedStageEnergy_withSupportLength centered (data ξ) a (Q.fullSupportLength Z) Z t Y₁ Y₂

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

include hannulus hcap hannulusZ domain profiles hrows ht hwindow hcutoffPower

/-- The actual first finite cutoff is bounded by the endpoint computed
from its own original first ideals. Only original atom support windows
and the chosen cutoff power are used. -/
theorem literalPrimitiveFirstSource_physicalCutoff
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset) :
    ((source).source DE).divisorPhysicalCutoff D.val ≤
      (((source).block DE).literalLeftCoordinates D.val).canonicalRetainedScale
        internal Z (2 * loss + cutoffExponent) := by
  have hrows' : ∀ u ∈ pairedRows (data ξ) internal Z, u ∈ rowDomain := by
    simpa only [Q.literalPrimitiveFirstSource_pairedRows] using hrows
  have hd := domain.withSupportLength (Q.fullSupportLength Z)
  have h := Q.canonicalFirstDivisorPhysicalCutoff W ξ internal Z t Y₁ Y₂ C
    cap annulus loss cutoffExponent hannulus hcap hannulusZ hd profiles hrows' ht hwindow
    cutoff hcutoff hcutoffPower DE D.val
  change ((source).source DE).divisorPhysicalCutoff D.val ≤ _ at h
  rw [Q.fullSupportParameters_idempotent] at h
  convert h using 1
  simp only [OriginalNominalIdeals.canonicalRetainedScale,
    OriginalNominalIdeals.firstFrequency,
    ((source).block DE).literalLeftCoordinates_first,
    ((source).block DE).literalLeftCoordinates_opposite,
    ((source).block DE).literalLeftCoordinates_complementary]
  rw [hd.total_length]

/-- Both signed Gauss rows come from this same original finite
divisor source. The right endpoint equals the left endpoint before
either second-stage enlargement is applied. -/
theorem literalPrimitiveFirstSource_row_windows
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset) :
    (∀ h ∈ ((source).pieces DE D).leftData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤
        (((source).block DE).literalLeftCoordinates D.val).canonicalRetainedScale
          internal Z (2 * loss + cutoffExponent)) ∧
    (∀ h ∈ ((source).pieces DE D).rightData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤
        (((source).block DE).literalRightCoordinates D.val).canonicalRetainedScale
          internal Z (2 * loss + cutoffExponent)) := by
  have hcut := Q.literalPrimitiveFirstSource_physicalCutoff μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    cap annulus loss cutoffExponent hannulus hcap hannulusZ domain profiles hrows ht hwindow
    hcutoffPower DE D
  have h := canonicalFirstGaussData_divisor_row_windows C (source).columns (source).columns
    (source).ideal (source).ideal DE.val DE.property ((source).source DE) D.val _ hcut
  refine ⟨h.1, ?_⟩
  simpa only [OriginalNominalIdeals.canonicalRetainedScale,
    ((source).block DE).literalRightCoordinates_firstFrequency] using h.2

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveFirstSource
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveFirstNormalization
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveFirstSource_physicalCutoff
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveFirstSource_row_windows
