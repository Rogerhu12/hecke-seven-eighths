import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectTerminalBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveTerminalLedgers
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalFirstTerminalWindows

/-!
# Actual direct amplitude windows before original-source summation

Both windows below belong to the already constructed direct terminal
family. The complete tuple count and signed physical fibres are computed
from its original columns. The sharp zero exponent is combined with the
same first-profile shift, while a fixed physical saving pays the tail.
No amplitude, final ledger, source multiplicity, or terminal estimate is
an input to these constructors.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
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

namespace CanonicalPrimitiveDirectTerminalWindows

/-- A fixed row-ball seminorm times the original individual profile
constant. Its moving source and ideal labels have not been selected. -/
def profileConstant (cap : ℕ) (amplitude : ℝ) (s : Finset (ℕ × ℕ)) : ℝ :=
  (2 * amplitude ^ (cap + 2)) ^ 2 *
    s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
      (CanonicalRowBall.archTest K A.Sf 1)

theorem profileConstant_nonneg (cap : ℕ) (amplitude : ℝ) (s : Finset (ℕ × ℕ)) :
    0 ≤ profileConstant (A := A) cap amplitude s :=
  mul_nonneg (sq_nonneg _) (apply_nonneg _ _)

/-- The explicit small power left after the actual first and second
zero exponents cancel. The two original support losses remain visible. -/
def zeroLoss (padding step loss cutoffExponent lengthBound columnBound δ ε : ℝ) : ℝ :=
  padding + 5 * step / 3 + (2 * loss + cutoffExponent) + 2 * loss +
    (4 * max lengthBound columnBound + 2) * δ +
      2 * (max lengthBound columnBound + 1) * ε

end CanonicalPrimitiveDirectTerminalWindows

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
local notation "raw" => atoms.raw Y₁ Y₂


local notation "source" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

variable (cap : ℕ) (annulus loss cutoffExponent : ℝ)
variable (hannulus : 1 ≤ annulus) (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (orders : Finset (ℕ × ℕ)) (amplitude : ℝ)
variable (profiles : RawProfileWindow rowDomain heightDomain window
  (OriginalProfileAtomBounds.profileOrders orders) (data ξ) amplitude)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
variable (hcutoffPower : cutoff ≤ Z ^ cutoffExponent)
variable (step : ℝ) (hstep : 0 < step)
variable (hloss : 0 ≤ loss) (hcutoffExponent : 0 ≤ cutoffExponent)

variable (lo : ℝ) (hlo : 0 < lo) (hloOne : lo ≤ 1)
variable (hlowerThreshold : (lo ^ (cap + 2))⁻¹ ≤ Z ^ loss)
variable (hlowerWindow : window ⊆ Set.Ici lo) (hamplitude : 1 ≤ amplitude)
variable (leftExponent rightExponent lengthBound columnBound : ℝ)
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable (hleftPower : Z ^ a.n₁ ≤ Z ^ leftExponent)
variable (hrightPower : Z ^ a.n₂ ≤ Z ^ rightExponent)
variable (hY₁le : Y₁ ≤ Z ^ leftExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
variable (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
variable (hcolumn : leftExponent + rightExponent + (data ξ).geometry.totalLength + loss ≤ columnBound)
variable (hlossOne : loss ≤ 1)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable (sTail sZero : Finset (ℕ × ℕ)) (Nsave decay : ℝ) (hdecay : 1 < decay)

local notation "degree" => CanonicalOriginalTerminalPowers.primitiveDegree
  cap lengthBound columnBound step loss cutoffExponent
local notation "cutoff₂" => CanonicalOriginalTerminalPowers.primitiveCutoff
  cap lengthBound columnBound step loss cutoffExponent Nsave decay Z
local notation "hcutoff₂" => CanonicalOriginalTerminalPowers.primitiveCutoff_ge_one
  cap lengthBound columnBound step loss cutoffExponent Nsave decay Z hZ.le hdecay
local notation "leftGeometry" => Q.literalPrimitiveLeftDirectGeometry μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  loss cutoffExponent step hloss hcutoffExponent
local notation "rightGeometry" => Q.literalPrimitiveRightDirectGeometry μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  loss cutoffExponent step hloss hcutoffExponent
local notation "stages" => Q.literalPrimitiveDirectStages μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap annulus loss cutoffExponent hannulus hcap hannulusZ domain profiles hrows ht hwindow
  hcutoffPower step hstep hloss hcutoffExponent hDiff δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂

local notation "terminal" => Q.literalPrimitiveDirectDualCalibration
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay)

local notation "leftBounds" => Q.literalPrimitiveDirectDualCalibration_left_bounds
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay)

local notation "rightBounds" => Q.literalPrimitiveDirectDualCalibration_right_bounds
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay)

local notation "firstTotal" => Q.literalPrimitiveFirstTotal μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
local notation "firstShift" => fun DE D =>
  Q.literalPrimitiveFirstProfileShift μv ν C hroot hemb W ξ a Z t Y₁ Y₂
    hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half DE D (firstTotal DE D)
local notation "zeroConstant" =>
  CanonicalPrimitiveDirectTerminalWindows.profileConstant (A := A) cap amplitude sZero
local notation "tailConstant" =>
  CanonicalPrimitiveDirectTerminalWindows.profileConstant (A := A) cap amplitude sTail

/-- Direct rows are exactly the signed original orbit representatives.
The original internal divisor and phase do not change their fibre. -/
theorem literalPrimitiveDirectStages_fiber_le_one
    (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset)
    (S : divisorPool (source.pieces DE D).rightData.columns
      (fun j => ((source.pieces DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    ((stages DE D).left S χ).fiber ≤ 1 ∧ ((stages DE D).right S χ).fiber ≤ 1 := by
  constructor
  · change engineOrbitMultiplicity
      (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (source.pieces DE D).leftData.rows ≤ 1
    exact canonicalFirstLeftGaussData_orbit_multiplicity_le_one C
      source.columns source.columns source.ideal source.ideal DE.val DE.property _
  · change engineOrbitMultiplicity
      (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (source.pieces DE D).rightData.rows ≤ 1
    exact canonicalFirstRightGaussData_orbit_multiplicity_le_one C
      source.columns source.columns source.ideal source.ideal DE.val DE.property _

include domain in
private theorem left_sharp_zero_exponent
    (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset) :
    (leftGeometry DE D).sharpZeroExponent loss δ₁ =
      -(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
        2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss -
          idealLogLength Z DE.val.1) * δ₁ +
            ((leftGeometry DE D).retainedLength + (leftGeometry DE D).enlargement) + 2 * loss := by
  change -(a.n₁ + a.n₂ + a.z) +
    2 * (a.n₁ + a.n₂ + a.z + loss - idealLogLength Z DE.val.1) * δ₁ +
      ((leftGeometry DE D).retainedLength + (leftGeometry DE D).enlargement) +
        2 * loss - 0 = _
  rw [← domain.total_length, sub_zero]

include domain in
private theorem right_sharp_zero_exponent
    (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset) :
    (rightGeometry DE D).sharpZeroExponent loss δ₁ =
      -(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
        2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss -
          idealLogLength Z DE.val.2) * δ₁ +
            ((rightGeometry DE D).retainedLength + (rightGeometry DE D).enlargement) + 2 * loss := by
  change -(a.n₁ + a.n₂ + a.z) +
    2 * (a.n₁ + a.n₂ + a.z + loss - idealLogLength Z DE.val.2) * δ₁ +
      ((rightGeometry DE D).retainedLength + (rightGeometry DE D).enlargement) +
        2 * loss - 0 = _
  rw [← domain.total_length, sub_zero]

/-- The zero window is constructed for the same whole direct family.
The compulsory divisor is still paid by its actual sharp calibration. -/
def literalPrimitiveDirectZeroAmplitudeWindows (εzero : ℝ) (hεzero : 0 ≤ εzero) :
    stages.CombinedZeroAmplitudeWindows terminal εzero
      (CanonicalPrimitiveDirectTerminalWindows.zeroLoss
        padding step loss cutoffExponent lengthBound columnBound δ₁ εzero)
      zeroConstant 1 firstTotal firstShift := by
  have hN := Q.literalPrimitiveFirstSource_column_norm μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    cap annulus loss leftExponent rightExponent columnBound hannulus hcap hannulusZ
    hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le profiles hrows ht hwindow hcolumn
  have htotal' : a.n₁ + a.n₂ + (data ξ).geometry.totalLength ≤ max lengthBound columnBound := by
    simpa only [← domain.total_length] using htotal.trans (le_max_left _ _)
  have hbox : 0 ≤ max lengthBound columnBound :=
    (add_nonneg (add_nonneg domain.plain_left_nonneg domain.plain_right_nonneg)
      (Finset.sum_nonneg (fun i _ => ((data ξ).geometry.slots i).length_pos.le))).trans htotal'
  refine
    { exponentL := fun DE D _ _ => (leftGeometry DE D).sharpZeroExponent loss δ₁
      exponentR := fun DE D _ _ => (rightGeometry DE D).sharpZeroExponent loss δ₁
      fiber_left := ?_
      fiber_right := ?_
      tuples_left := fun DE D S χ => (leftBounds DE D S χ).1.le
      tuples_right := fun DE D S χ => (rightBounds DE D S χ).1.le
      amplitude_left := ?_
      amplitude_right := ?_
      exponent_left := ?_
      exponent_right := ?_ }
  · intro DE D S χ
    exact (Q.literalPrimitiveDirectStages_fiber_le_one
      (μv := μv) (ν := ν) (C := C) (hroot := hroot)
      (hemb := hemb) (W := W) (ξ := ξ) (a := a)
      (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
      (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff)
      (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
      (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
      (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
      (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows)
      (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
      (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lengthBound := lengthBound)
      (columnBound := columnBound) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂)
      (hδ₂half := hδ₂half) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) DE D S χ).1
  · intro DE D S χ
    exact (Q.literalPrimitiveDirectStages_fiber_le_one
      (μv := μv) (ν := ν) (C := C) (hroot := hroot)
      (hemb := hemb) (W := W) (ξ := ξ) (a := a)
      (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
      (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff)
      (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
      (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
      (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
      (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows)
      (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
      (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lengthBound := lengthBound)
      (columnBound := columnBound) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂)
      (hδ₂half := hδ₂half) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) DE D S χ).2
  · intro DE D S χ hfiber
    have he := Q.left_sharp_zero_exponent μv ν C hroot hemb W ξ
      a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
      loss cutoffExponent domain step hloss hcutoffExponent DE D
    simpa only [CanonicalPrimitiveDirectTerminalWindows.profileConstant, he] using
      ((leftBounds DE D S χ).2.2 hfiber).2
  · intro DE D S χ hfiber
    have he := Q.right_sharp_zero_exponent μv ν C hroot hemb W ξ
      a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
      loss cutoffExponent domain step hloss hcutoffExponent DE D
    simpa only [CanonicalPrimitiveDirectTerminalWindows.profileConstant, he] using
      ((rightBounds DE D S χ).2.2 hfiber).2
  · intro DE D S χ _
    have hproduct : ((terminal DE D).left S χ).zeroProductExponent ≤
        2 * (max lengthBound columnBound + 1) := by
      rw [(leftBounds DE D S χ).2.1]
      exact CanonicalOriginalTerminalPowers.zeroProductExponent_le _ _ _ _ hbox htotal'
        (idealLogLength_nonneg Z hZ _
          (nonZeroDivisors.coe_ne_zero (leftGeometry DE D).ideals.first)) hlossOne
    have h := Q.literalPrimitiveGeometry_zero_ledger μv ν C hroot hemb W ξ
      a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
      step DE D false (leftGeometry DE D) rfl hstep.le lengthBound columnBound htotal hN
      domain loss εzero ((terminal DE D).left S χ).zeroProductExponent
      (firstTotal DE D) hlossOne hεzero hproduct
    have hfirst : (leftGeometry DE D).ideals.first.val = DE.val.1 := rfl
    have hopposite : (leftGeometry DE D).ideals.opposite.val = DE.val.2 := rfl
    have herr : (leftGeometry DE D).supportError = 2 * loss + cutoffExponent := rfl
    simpa only [OriginalNominalGeometry.boundary, hfirst, hopposite, herr,
      CanonicalPrimitiveDirectTerminalWindows.zeroLoss] using h
  · intro DE D S χ _
    have hproduct : ((terminal DE D).right S χ).zeroProductExponent ≤
        2 * (max lengthBound columnBound + 1) := by
      rw [(rightBounds DE D S χ).2.1]
      exact CanonicalOriginalTerminalPowers.zeroProductExponent_le _ _ _ _ hbox htotal'
        (idealLogLength_nonneg Z hZ _
          (nonZeroDivisors.coe_ne_zero (rightGeometry DE D).ideals.first)) hlossOne
    have h := Q.literalPrimitiveGeometry_zero_ledger μv ν C hroot hemb W ξ
      a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
      step DE D true (rightGeometry DE D) rfl hstep.le lengthBound columnBound htotal hN
      domain loss εzero ((terminal DE D).right S χ).zeroProductExponent
      (firstTotal DE D) hlossOne hεzero hproduct
    have hfirst : (rightGeometry DE D).ideals.first.val = DE.val.2 := rfl
    have hopposite : (rightGeometry DE D).ideals.opposite.val = DE.val.1 := rfl
    have herr : (rightGeometry DE D).supportError = 2 * loss + cutoffExponent := rfl
    simpa only [OriginalNominalGeometry.boundary, hfirst, hopposite, herr,
      firstActiveRadical_swap_of_support DE.val.1 DE.val.2 (source.block DE).common_support_eq,
      CanonicalPrimitiveDirectTerminalWindows.zeroLoss] using h

/-- The fixed tail saving is chosen in the original length box. It
pays the actual first allowance on both sides of every original class. -/
def literalPrimitiveDirectTailAmplitudeWindows (hsaving : 2 * columnBound ≤ Nsave) :
    stages.CombinedTailAmplitudeWindows terminal loss tailConstant 1 firstTotal firstShift := by
  have hN := Q.literalPrimitiveFirstSource_column_norm μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    cap annulus loss leftExponent rightExponent columnBound hannulus hcap hannulusZ
    hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le profiles hrows ht hwindow hcolumn
  refine
    { exponentL := fun _ _ _ _ => 0
      exponentR := fun _ _ _ _ => 0
      fiber_left := ?_
      fiber_right := ?_
      tuples_left := fun DE D S χ => (leftBounds DE D S χ).1.le
      tuples_right := fun DE D S χ => (rightBounds DE D S χ).1.le
      amplitude_left := ?_
      amplitude_right := ?_
      exponent_left := ?_
      exponent_right := ?_ }
  · intro DE D S χ
    exact (Q.literalPrimitiveDirectStages_fiber_le_one
      (μv := μv) (ν := ν) (C := C) (hroot := hroot)
      (hemb := hemb) (W := W) (ξ := ξ) (a := a)
      (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
      (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff)
      (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
      (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
      (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
      (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows)
      (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
      (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lengthBound := lengthBound)
      (columnBound := columnBound) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂)
      (hδ₂half := hδ₂half) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) DE D S χ).1
  · intro DE D S χ
    exact (Q.literalPrimitiveDirectStages_fiber_le_one
      (μv := μv) (ν := ν) (C := C) (hroot := hroot)
      (hemb := hemb) (W := W) (ξ := ξ) (a := a)
      (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
      (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff)
      (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
      (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
      (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
      (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows)
      (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
      (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lengthBound := lengthBound)
      (columnBound := columnBound) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂)
      (hδ₂half := hδ₂half) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) DE D S χ).2
  · intro DE D S χ hfiber
    exact (((leftBounds DE D S χ).2.2 hfiber).1).trans_eq (by
      dsimp only [CanonicalPrimitiveDirectTerminalWindows.profileConstant]
      rw [Real.rpow_zero, mul_one]
      ring)
  · intro DE D S χ hfiber
    exact (((rightBounds DE D S χ).2.2 hfiber).1).trans_eq (by
      dsimp only [CanonicalPrimitiveDirectTerminalWindows.profileConstant]
      rw [Real.rpow_zero, mul_one]
      ring)
  · intro DE D S χ _
    have h := Q.literalPrimitiveGeometry_tail_ledger μv ν C hroot hemb W ξ
      a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
      step DE D false (leftGeometry DE D) rfl columnBound hN loss Nsave
      (firstTotal DE D) hloss hsaving
    have hfirst : (leftGeometry DE D).ideals.first.val = DE.val.1 := rfl
    have hopposite : (leftGeometry DE D).ideals.opposite.val = DE.val.2 := rfl
    simpa only [zero_sub, OriginalNominalGeometry.boundary, hfirst, hopposite] using h
  · intro DE D S χ _
    have h := Q.literalPrimitiveGeometry_tail_ledger μv ν C hroot hemb W ξ
      a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
      step DE D true (rightGeometry DE D) rfl columnBound hN loss Nsave
      (firstTotal DE D) hloss hsaving
    have hfirst : (rightGeometry DE D).ideals.first.val = DE.val.2 := rfl
    have hopposite : (rightGeometry DE D).ideals.opposite.val = DE.val.1 := rfl
    simpa only [zero_sub, OriginalNominalGeometry.boundary, hfirst, hopposite,
      firstActiveRadical_swap_of_support DE.val.1 DE.val.2 (source.block DE).common_support_eq] using h

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectStages_fiber_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectZeroAmplitudeWindows
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectTailAmplitudeWindows
