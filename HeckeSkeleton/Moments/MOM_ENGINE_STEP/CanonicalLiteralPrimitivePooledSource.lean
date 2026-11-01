import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalParentWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectLeafNormWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFirstPhysicalWindows

/-!
# The same original first source with one actual prime pool

The complete original columns bound the common and selected physical
mask ideals. Together with the original profile endpoint and the
nonnegative internal row length, these give one fixed coarse row
window. The actual pool is then installed on the same first source,
with unit frozen ideals and its displayed original row density.
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


variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable (lengthBound columnBound : ℝ)
variable (hlengthBound : 0 ≤ lengthBound) (hcolumnBound : 0 ≤ columnBound)
variable (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
variable (hN : ∀ i ∈ (source).columns,
  (Ideal.absNorm ((source).ideal i).val : ℝ) ≤ Z ^ columnBound)
variable (hloss : 0 ≤ loss) (hcutoffExponent : 0 ≤ cutoffExponent)

/-- Only original length bounds enter the pool-density row exponent. -/
def literalPrimitivePoolRowExponent : ℝ :=
  2 * lengthBound + 2 * columnBound + 2 * loss + cutoffExponent

local notation "rowExponent" => literalPrimitivePoolRowExponent
  (lengthBound := lengthBound) (columnBound := columnBound)
  (loss := loss) (cutoffExponent := cutoffExponent)

include htotal hN href in
theorem literalPrimitiveFirstFrequency_upper
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset) :
    (((source).block DE).literalLeftCoordinates D.val).firstFrequency internal Z ≤
      2 * lengthBound + 2 * columnBound := by
  let b := (source).block DE
  have hDE := actual_common_pair_properties (source).columns (source).columns
    (fun i => ((source).ideal i).val) (fun i => ((source).ideal i).val) DE
  have hnorm := actual_common_pair_norm (source).columns (source).columns
    (fun i => ((source).ideal i).val) (fun i => ((source).ideal i).val) (Z ^ columnBound)
    (fun i _ => ((source).ideal i).property.1) (fun i _ => ((source).ideal i).property.1)
    hN hN DE
  have hactiveDvd : firstActiveRadical DE.val.1 DE.val.2 ∣ DE.val.1 := by
    rw [← b.activeIdeal_eq, ← b.common_left]
    exact firstActiveIdeal_dvd_common b.primes b.leftMultiplicity b.rightMultiplicity b.left_positive
  have hactiveNorm : (Ideal.absNorm (firstActiveRadical DE.val.1 DE.val.2) : ℝ) ≤
      Z ^ columnBound := (norm_le_of_dvd hDE.1 hactiveDvd).trans hnorm.1
  have hactive : idealLogLength Z (firstActiveRadical DE.val.1 DE.val.2) ≤ columnBound := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [rpow_idealLogLength Z hZ _ (firstActiveRadical_ne_zero _ _)]
    exact hactiveNorm
  have hsub : D.val ⊆ b.mask ∅ := Finset.mem_powerset.mp D.property
  have hdiv := original_submask_generator_dvd hsub
  have hmask := sIntegerElementNorm_le_of_dvd A.Sf
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅)).val
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).property
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅)).property hdiv
  have hphysicalNorm : A.exteriorNorm (firstPhysicalDivisorIdeal (A := A) D.val) ≤
      Z ^ columnBound := by
    rw [firstPhysicalDivisorIdeal_norm]
    exact hmask.trans ((b.principal_mask_norm_le_common C).trans hnorm.1)
  have hphysical : idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val ≤
      columnBound := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [rpow_idealLogLength Z hZ _ (firstPhysicalDivisorIdeal D.val).property.1]
    exact hphysicalNorm
  have hc := idealLogLength_nonneg Z hZ DE.val.1 hDE.1
  have hd := idealLogLength_nonneg Z hZ DE.val.2 hDE.2.1
  have hm := Q.fullSupportParameters_m_nonneg_of_pairedRow a Z hZ hbudget ξ reference href
  have ht : (internal).n₁ + (internal).n₂ + (internal).z ≤ lengthBound := htotal
  simp only [OriginalNominalIdeals.firstFrequency,
    b.literalLeftCoordinates_first, b.literalLeftCoordinates_opposite,
    b.literalLeftCoordinates_complementary]
  linarith

include hannulus hcap hannulusZ domain profiles hrows ht hwindow hcutoffPower
  htotal hN href in
/-- Both original signed rows fit the same coarse density exponent.
The actual second radii continue to use their sharper endpoints. -/
theorem literalPrimitivePool_row_windows
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset) :
    (∀ h ∈ ((source).pieces DE D).leftData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ rowExponent) ∧
    (∀ h ∈ ((source).pieces DE D).rightData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ rowExponent) := by
  have hw := Q.literalPrimitiveFirstSource_row_windows μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    cap annulus loss cutoffExponent hannulus hcap hannulusZ domain profiles hrows ht hwindow
    hcutoffPower DE D
  have hf := literalPrimitiveFirstFrequency_upper
    (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
    (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (reference := reference) (href := href) (lengthBound := lengthBound)
    (columnBound := columnBound) (htotal := htotal) (hN := hN) DE D
  have hl : (((source).block DE).literalLeftCoordinates D.val).canonicalRetainedScale
      internal Z (2 * loss + cutoffExponent) ≤ Z ^ rowExponent := by
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp only [literalPrimitivePoolRowExponent]
    linarith
  have hr : (((source).block DE).literalRightCoordinates D.val).canonicalRetainedScale
      internal Z (2 * loss + cutoffExponent) ≤ Z ^ rowExponent := by
    simpa only [OriginalNominalIdeals.canonicalRetainedScale,
      ((source).block DE).literalRightCoordinates_firstFrequency] using hl
  exact ⟨fun h hh => (hw.1 h hh).trans hl, fun h hh => (hw.2 h hh).trans hr⟩

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {step eps : ℝ}
variable (pool : PowerScaleExteriorPool A bad Z (step / 3) eps)
variable (hdensity : 0 < pool.rowDensity rowExponent columnBound)

/-- This is the original first source with the same one-pool amplifier.
The frozen ideals are units; the actual first internal divisor is still
adjoined by the existing divisor-pool construction. -/
def literalPrimitivePooledSource :
    ActualFirstSource
      (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (E := ℝ) (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv C pool (rowBallFiniteFamily K A.Sf 1)
      centered (data ξ) internal t Y₁ Y₂ cutoff hcutoff :=
  (source).withOriginalPool pool 1 1 one_ne_zero one_ne_zero rowExponent rowExponent
    0 0 columnBound (by dsimp only [literalPrimitivePoolRowExponent]; positivity)
    (by dsimp only [literalPrimitivePoolRowExponent]; positivity) hcolumnBound
    (fun DE D => (literalPrimitivePool_row_windows
      (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
      (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
      (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
      (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
      (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
      (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow)
      (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
      (lengthBound := lengthBound) (columnBound := columnBound) (htotal := htotal) (hN := hN) DE D).1)
    (fun DE D => (literalPrimitivePool_row_windows
      (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
      (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
      (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
      (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
      (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
      (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow)
      (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
      (lengthBound := lengthBound) (columnBound := columnBound) (htotal := htotal) (hN := hN) DE D).2)
    (by simp only [map_one, Nat.cast_one, Real.rpow_zero])
    (by simp only [map_one, Nat.cast_one, Real.rpow_zero]) hN
    (by simpa only [zero_add] using hdensity) (by simpa only [zero_add] using hdensity)

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveFirstFrequency_upper
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePool_row_windows
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledSource
