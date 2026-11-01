import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitivePooledTerminalWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalFirstTerminalWindows

/-!
# Complete original pooled terminal budgets

The constants for the original common labels and shared divisor are
chosen before the moving rows, coefficients, scale and prime pool.
The actual first windows and all original main and 1/6/7 amplitude
windows are constructed inside each bound. Both terminal sums retain
the original first normalization and the same complete source.
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



namespace CanonicalPrimitivePooledTerminalBudget

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (cap : ℕ) (columnBound εsum : ℝ)
variable (hcolumnBound : 0 ≤ columnBound) (hεsum : 0 < εsum)

local notation "zeroExists" => actual_pool_second_dual_zero_from_combined_windows
  (E := ℝ) (W := ℝ) (C := C)
  (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  (μv := μv) (hDiff := hDiff) (finiteTest := rowBallFiniteFamily K A.Sf 1)
  (2 * (cap + 2)) columnBound εsum hcolumnBound hεsum
local notation "tailExists" => actual_pool_second_dual_tail_from_combined_windows
  (E := ℝ) (W := ℝ) (C := C)
  (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  (μv := μv) (hDiff := hDiff) (finiteTest := rowBallFiniteFamily K A.Sf 1)
  (2 * (cap + 2)) columnBound εsum hcolumnBound hεsum

/-- Fixed before every source and scale. -/
def zeroSumConstant : ℝ := Classical.choose zeroExists

/-- The same ordering of quantifiers for the complete tail sum. -/
def tailSumConstant : ℝ := Classical.choose tailExists

theorem zeroSumConstant_pos :
    0 < zeroSumConstant μv C hDiff cap columnBound εsum hcolumnBound hεsum :=
  (Classical.choose_spec zeroExists).1

theorem tailSumConstant_pos :
    0 < tailSumConstant μv C hDiff cap columnBound εsum hcolumnBound hεsum :=
  (Classical.choose_spec tailExists).1

end CanonicalPrimitivePooledTerminalBudget

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


variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable (hlengthBound : 0 ≤ lengthBound) (hcolumnBound : 0 ≤ columnBound)
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {eps : ℝ}
variable (pool : PowerScaleExteriorPool A bad Z (step / 3) eps)
variable (hdensity : 0 < pool.rowDensity
  (literalPrimitivePoolRowExponent (lengthBound := lengthBound) (columnBound := columnBound)
    (loss := loss) (cutoffExponent := cutoffExponent)) columnBound)

local notation "columnNorm" => Q.literalPrimitiveFirstSource_column_norm μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap annulus loss leftExponent rightExponent columnBound hannulus hcap hannulusZ
  hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le profiles hrows ht hwindow hcolumn

local notation "degree" => CanonicalOriginalTerminalPowers.primitiveDegree
  cap lengthBound columnBound step loss cutoffExponent
local notation "cutoff₂" => CanonicalOriginalTerminalPowers.primitiveCutoff
  cap lengthBound columnBound step loss cutoffExponent Nsave decay Z
local notation "hcutoff₂" => CanonicalOriginalTerminalPowers.primitiveCutoff_ge_one
  cap lengthBound columnBound step loss cutoffExponent Nsave decay Z hZ.le hdecay
local notation "source" => Q.literalPrimitivePooledSource
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent) (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (reference := reference) (href := href) (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (htotal := htotal) (hN := columnNorm) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (pool := pool) (hdensity := hdensity)

local notation "leftRows" => Q.literalPrimitiveLeftPooledRows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent) (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (reference := reference) (href := href) (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (htotal := htotal) (hN := columnNorm) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (pool := pool) (hdensity := hdensity)

local notation "rightRows" => Q.literalPrimitiveRightPooledRows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent) (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (reference := reference) (href := href) (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (htotal := htotal) (hN := columnNorm) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (pool := pool) (hdensity := hdensity)

local notation "stages" => Q.literalPrimitivePooledStages
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent) (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (reference := reference) (href := href) (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (htotal := htotal) (hN := columnNorm) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (pool := pool) (hdensity := hdensity)
  (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half) («cutoff₂» := cutoff₂) («hcutoff₂» := hcutoff₂)

local notation "leftMainGeometry" => OriginalNominalGeometry.canonicalMain
  (a := internal) (step := step)
local notation "rightMainGeometry" => OriginalNominalGeometry.canonicalMain
  (a := internal) (step := step)
local notation "valuationGeometry" => OriginalNominalGeometry.canonicalPoolError
  (a := internal) pool

local notation "terminal" => Q.literalPrimitivePooledDualCalibration
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) (reference := reference) (href := href)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (pool := pool) (hdensity := hdensity)



local notation "rowExponent" => literalPrimitivePoolRowExponent
  (lengthBound := lengthBound) (columnBound := columnBound)
  (loss := loss) (cutoffExponent := cutoffExponent)
local notation "fiberCap" => CanonicalPrimitivePooledTerminalWindows.fiberCap rowExponent step
local notation "firstTotal" => Q.literalPrimitiveFirstTotal μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
local notation "firstShift" => fun DE D =>
  Q.literalPrimitiveFirstProfileShift μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half DE D (firstTotal DE D)
local notation "tailProfile" => (2 * amplitude ^ (cap + 2)) ^ 2 *
  sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (CanonicalRowBall.archTest K A.Sf 1)
local notation "zeroProfile" => (2 * amplitude ^ (cap + 2)) ^ 2 *
  sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (CanonicalRowBall.archTest K A.Sf 1)
local notation "firstKernel" => ActualGaussStage.canonicalRowBallKernel
  (A := A) (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  μv ν δ₁ hδ₁ hδ₁half
local notation "kernelBound" => (firstTerminalFourierControl (W := ℝ)).seminorms.sup
  (schwartzSeminormFamily ℝ ℝ ℂ) firstKernel

variable (hlarge : 2 * (rowExponent / ((step / 3) / 2) +
  columnBound / ((step / 3) / 2)) ≤ Z ^ (step / 3 - eps))
variable (εsum : ℝ) (hεsum : 0 < εsum)

local notation "originalWindows" => Q.literalPrimitiveFirstTerminalWindows μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap annulus loss leftExponent rightExponent columnBound hannulus hcap hannulusZ hcolumnBound
  hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le profiles hrows ht hwindow hcolumn
local notation "zeroSumConstant" => CanonicalPrimitivePooledTerminalBudget.zeroSumConstant
  μv C hDiff cap columnBound εsum hcolumnBound hεsum
local notation "tailSumConstant" => CanonicalPrimitivePooledTerminalBudget.tailSumConstant
  μv C hDiff cap columnBound εsum hcolumnBound hεsum

local notation "zeroWindows" => Q.literalPrimitivePooledZeroAmplitudeWindows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) (reference := reference) (href := href)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (pool := pool) (hdensity := hdensity)
  (hlarge := hlarge)

local notation "tailWindows" => Q.literalPrimitivePooledTailAmplitudeWindows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) (reference := reference) (href := href)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (pool := pool) (hdensity := hdensity)
  (hlarge := hlarge)

/-- The complete original pooled zero terminal, with the actual
first normalization and one shared internal divisor. -/
theorem literalPrimitivePooledDualZeroBudget_le
    (εzero Czero : ℝ) (hεzero : 0 ≤ εzero) (hCzero : 0 ≤ Czero) :
    (stages).dualSecondZeroBudget terminal ((source).canonicalNormalization hZ firstTotal)
      εzero Czero / Z ^ (a.m + a.q) ≤
    poolTerminalConstant K (step / 3) rowExponent * fiberCap * Czero *
      orbitalFieldFactor K * kernelBound * zeroProfile * zeroSumConstant *
      Z ^ ((CanonicalPrimitivePooledTerminalWindows.zeroLoss
        padding step loss cutoffExponent lengthBound columnBound δ₁ εzero eps) + εsum) := by
  let O : (source).CombinedTerminalOriginalWindows columnBound (a.m + a.q)
      (orbitalFieldFactor K) kernelBound firstTotal firstShift := {
    oldMask := (originalWindows).oldMask
    old_squarefree := (originalWindows).old_squarefree
    old_ne_zero := (originalWindows).old_ne_zero
    old_divides := (originalWindows).old_divides
    column_norm := (originalWindows).column_norm
    maskIdeal := (originalWindows).maskIdeal
    mask_ne_zero := (originalWindows).mask_ne_zero
    mask_norm := (originalWindows).mask_norm
    original_mask := (originalWindows).original_mask
    first_profile := (originalWindows).first_profile
    first_kernel := (originalWindows).first_kernel }
  have hsum := (Classical.choose_spec
    (actual_pool_second_dual_zero_from_combined_windows
      (E := ℝ) (W := ℝ) (C := C)
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (finiteTest := rowBallFiniteFamily K A.Sf 1)
      (2 * (cap + 2)) columnBound εsum hcolumnBound hεsum)).2
  have hprofile : 0 ≤ zeroProfile := mul_nonneg (sq_nonneg _)
    ((sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)).apply_nonneg _)
  have hM : 0 ≤ rowExponent := by
    dsimp only [literalPrimitivePoolRowExponent]
    positivity
  have h := hsum Z (step / 3) eps bad pool centered (data ξ) internal
    t Y₁ Y₂ cutoff hcutoff source stages sTail sZero degree Nsave decay terminal
    εzero Czero (a.m + a.q)
    (CanonicalPrimitivePooledTerminalWindows.zeroLoss
        padding step loss cutoffExponent lengthBound columnBound δ₁ εzero eps)
    (orbitalFieldFactor K) kernelBound zeroProfile rowExponent fiberCap hCzero
    (orbitalFieldFactor_nonneg K) (apply_nonneg _ _) hprofile hM
    firstTotal firstShift O (zeroWindows εzero hεzero)
  have hfiber : (source).fiber = 1 := rfl
  have hmask : O.oldMask = (1 : Ideal (𝓞 K)) := rfl
  simpa only [hfiber, hmask, map_one, Nat.cast_one, one_mul, div_one] using h

/-- The complete original pooled tail terminal, with the actual
first normalization and one shared internal divisor. -/
theorem literalPrimitivePooledDualTailBudget_le
    (Cerror : ℝ) (hCerror : 0 ≤ Cerror) (hsaving : 2 * columnBound ≤ Nsave) :
    (stages).dualSecondTailBudget terminal ((source).canonicalNormalization hZ firstTotal)
      Cerror / Z ^ (a.m + a.q) ≤
    poolTerminalConstant K (step / 3) rowExponent * fiberCap * Cerror *
      orbitalFieldFactor K * kernelBound * tailProfile * tailSumConstant *
      Z ^ (eps + εsum) := by
  let O : (source).CombinedTerminalOriginalWindows columnBound (a.m + a.q)
      (orbitalFieldFactor K) kernelBound firstTotal firstShift := {
    oldMask := (originalWindows).oldMask
    old_squarefree := (originalWindows).old_squarefree
    old_ne_zero := (originalWindows).old_ne_zero
    old_divides := (originalWindows).old_divides
    column_norm := (originalWindows).column_norm
    maskIdeal := (originalWindows).maskIdeal
    mask_ne_zero := (originalWindows).mask_ne_zero
    mask_norm := (originalWindows).mask_norm
    original_mask := (originalWindows).original_mask
    first_profile := (originalWindows).first_profile
    first_kernel := (originalWindows).first_kernel }
  have hsum := (Classical.choose_spec
    (actual_pool_second_dual_tail_from_combined_windows
      (E := ℝ) (W := ℝ) (C := C)
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (finiteTest := rowBallFiniteFamily K A.Sf 1)
      (2 * (cap + 2)) columnBound εsum hcolumnBound hεsum)).2
  have hprofile : 0 ≤ tailProfile := mul_nonneg (sq_nonneg _)
    ((sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)).apply_nonneg _)
  have hM : 0 ≤ rowExponent := by
    dsimp only [literalPrimitivePoolRowExponent]
    positivity
  have h := hsum Z (step / 3) eps bad pool centered (data ξ) internal
    t Y₁ Y₂ cutoff hcutoff source stages sTail sZero degree Nsave decay terminal
    Cerror (a.m + a.q)
    eps
    (orbitalFieldFactor K) kernelBound tailProfile rowExponent fiberCap hCerror
    (orbitalFieldFactor_nonneg K) (apply_nonneg _ _) hprofile hM
    firstTotal firstShift O (tailWindows hsaving)
  have hfiber : (source).fiber = 1 := rfl
  have hmask : O.oldMask = (1 : Ideal (𝓞 K)) := rfl
  simpa only [hfiber, hmask, map_one, Nat.cast_one, one_mul, div_one] using h

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitivePooledTerminalBudget.zeroSumConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitivePooledTerminalBudget.tailSumConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledDualZeroBudget_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledDualTailBudget_le
