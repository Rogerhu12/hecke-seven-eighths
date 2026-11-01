import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalPooledTerminalGeometry

/-!
# Summable amplitudes of the actual original pool stages

The exact original tuple count is paid by the fixed maximum valuation
seven. The full zero-product exponent remains independent of the tail
product exponent. Original main and error amplitudes retain their same
shared divisor and acquire only the literal pool norm charge.
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
  (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

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


local notation "leftMainBounds" => Q.literalPrimitivePooledDualCalibration_left_main_bounds
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) (reference := reference) (href := href)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (pool := pool) (hdensity := hdensity)

local notation "leftValuationBounds" => Q.literalPrimitivePooledDualCalibration_left_valuation_bounds
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) (reference := reference) (href := href)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (pool := pool) (hdensity := hdensity)

local notation "rightMainBounds" => Q.literalPrimitivePooledDualCalibration_right_main_bounds
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) (reference := reference) (href := href)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (pool := pool) (hdensity := hdensity)

local notation "rightValuationBounds" => Q.literalPrimitivePooledDualCalibration_right_valuation_bounds
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
local notation "tupleDegree" => 2 * (cap + 2)
local notation "tailProfile" => (2 * amplitude ^ (cap + 2)) ^ 2 *
  sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (CanonicalRowBall.archTest K A.Sf 1)
local notation "zeroProfile" => (2 * amplitude ^ (cap + 2)) ^ 2 *
  sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (CanonicalRowBall.archTest K A.Sf 1)
local notation "geometry" => fun DE : source.CommonLabel =>
  fun D : ((source.block DE).mask source.mask).powerset =>
  (source.block DE).pooledTerminalGeometry internal pool D.val
    (2 * loss + cutoffExponent) (by positivity)

/-- The left main and 1/6/7 amplitudes on their actual common divisor. -/
theorem literalPrimitivePooledTerminal_left_atoms
    (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset)
    (S : divisorPool (source.pools DE D).rightData.columns
      (fun j => ((source.pools DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (tag : PoolSourceTag pool) :
    (((terminal DE D).left S χ).tag tag).windows.multiplicity ≤
        idealDivisorCount (DE.val.1 ^ 2) ^ tupleDegree * 15 ^ tupleDegree ∧
      (((terminal DE D).left S χ).tag tag).zeroProductExponent ≤
        2 * (max lengthBound columnBound + 1) ∧
      ((((stages DE D).left S χ).tag tag).fiber ≠ 0 →
        (((terminal DE D).left S χ).tag tag).tailAmplitude ≤
          tailProfile * poolTagNormCharge pool tag / (Ideal.absNorm S.val : ℝ) ∧
        (((terminal DE D).left S χ).tag tag).zeroAmplitude ≤
          (zeroProfile * poolTagNormCharge pool tag / (Ideal.absNorm S.val : ℝ)) *
            Z ^ (geometry DE D false tag).sharpZeroExponent loss δ₁) := by
  have hDE := actual_common_pair_properties firstSource.columns firstSource.columns
    (fun i => (firstSource.ideal i).val) (fun i => (firstSource.ideal i).val) DE
  have htotal' : a.n₁ + a.n₂ + (data ξ).geometry.totalLength ≤
      max lengthBound columnBound := by
    rw [← domain.total_length]
    exact htotal.trans (le_max_left _ _)
  have hbound : 0 ≤ max lengthBound columnBound := hlengthBound.trans (le_max_left _ _)
  have htail : 0 ≤ tailProfile := mul_nonneg (sq_nonneg _)
    ((sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)).apply_nonneg _)
  have hzero : 0 ≤ zeroProfile := mul_nonneg (sq_nonneg _)
    ((sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)).apply_nonneg _)
  have tailBound (b : PoolSourceTag pool) (v : ℝ)
      (hv : v ≤ ((2 * amplitude ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
        sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
          (CanonicalRowBall.archTest K A.Sf 1)) :
      v ≤ tailProfile * poolTagNormCharge pool b / (Ideal.absNorm S.val : ℝ) := by
    calc
      v ≤ tailProfile / (Ideal.absNorm S.val : ℝ) := hv.trans_eq (by ring)
      _ ≤ _ := div_le_div_of_nonneg_right
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (one_le_poolTagNormCharge pool b) htail)
        (Nat.cast_nonneg _)
  have zeroBound (b : PoolSourceTag pool) (v : ℝ)
      (hv : v ≤ (zeroProfile / (Ideal.absNorm S.val : ℝ)) *
        Z ^ ((geometry DE D false b).sharpZeroExponent loss δ₁ +
          (geometry DE D false b).tag.poolLength step)) :
      v ≤ (zeroProfile * poolTagNormCharge pool b / (Ideal.absNorm S.val : ℝ)) *
        Z ^ (geometry DE D false b).sharpZeroExponent loss δ₁ := by
    have hb := (source.block DE).pooledTerminalGeometry_charge internal pool D.val
      (2 * loss + cutoffExponent) (by positivity) false b
    have hs := terminal_amplitude_shift_by_charge Z zeroProfile (Ideal.absNorm S.val : ℝ)
      ((geometry DE D false b).sharpZeroExponent loss δ₁ + (geometry DE D false b).tag.poolLength step)
      ((geometry DE D false b).tag.poolLength step) (poolTagNormCharge pool b)
      (zero_lt_one.trans hZ) hzero (Nat.cast_nonneg _) hb
    exact hv.trans (by simpa only [add_sub_cancel_right] using hs)
  have hvaluation (valuation : AmplifierValuation) (prime : pool.primes) :
      (((terminal DE D).left S χ).tag (valuation.sourceTag prime)).windows.multiplicity ≤
          idealDivisorCount (DE.val.1 ^ 2) ^ tupleDegree * 15 ^ tupleDegree ∧
        (((terminal DE D).left S χ).tag (valuation.sourceTag prime)).zeroProductExponent ≤
          2 * (max lengthBound columnBound + 1) ∧
        ((((stages DE D).left S χ).tag (valuation.sourceTag prime)).fiber ≠ 0 →
          (((terminal DE D).left S χ).tag (valuation.sourceTag prime)).tailAmplitude ≤
            tailProfile * poolTagNormCharge pool (valuation.sourceTag prime) / (Ideal.absNorm S.val : ℝ) ∧
          (((terminal DE D).left S χ).tag (valuation.sourceTag prime)).zeroAmplitude ≤
            (zeroProfile * poolTagNormCharge pool (valuation.sourceTag prime) / (Ideal.absNorm S.val : ℝ)) *
              Z ^ (geometry DE D false (valuation.sourceTag prime)).sharpZeroExponent loss δ₁) := by
    have h := leftValuationBounds DE D S χ valuation prime
    refine ⟨?_, ?_, ?_⟩
    · rw [h.1]
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      cases valuation <;> norm_num [AmplifierValuation.multiplicity]
    · rw [h.2.1]
      exact CanonicalOriginalTerminalPowers.zeroProductExponent_le
        _ _ loss (max lengthBound columnBound) hbound htotal'
        (idealLogLength_nonneg Z hZ _
          (mul_ne_zero hDE.1 (powerIdeal prime.val valuation.multiplicity).property.1)) hlossOne
    · intro hf
      have hamp := h.2.2 hf
      refine ⟨tailBound _ _ hamp.1, zeroBound _ _ ?_⟩
      simpa only [OriginalNominalGeometry.sharpZeroExponent,
        FirstCommonCharacterBlock.pooledTerminalGeometry_valuation,
        OriginalNominalGeometry.canonicalPoolError, OriginalNominalGeometry.forPoolError,
        FirstCommonCharacterBlock.literalLeftCoordinates_first,
        Bool.false_eq_true, if_false, if_true, sub_add_cancel, domain.total_length] using hamp.2
  rcases tag with u | prime | prime | prime
  · have h := leftMainBounds DE D S χ
    refine ⟨?_, ?_, ?_⟩
    · rw [h.1]
      exact Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0 < (15 : ℕ)) tupleDegree)
    · rw [h.2.1]
      exact CanonicalOriginalTerminalPowers.zeroProductExponent_le
        _ _ loss (max lengthBound columnBound) hbound htotal'
        (idealLogLength_nonneg Z hZ DE.val.1 hDE.1) hlossOne
    · intro hf
      have hamp := h.2.2 hf
      refine ⟨tailBound _ _ hamp.1, zeroBound _ _ ?_⟩
      simpa only [OriginalNominalGeometry.sharpZeroExponent,
        FirstCommonCharacterBlock.pooledTerminalGeometry,
        OriginalNominalGeometry.canonicalMain, OriginalNominalGeometry.forMain,
        FirstCommonCharacterBlock.literalLeftCoordinates_first,
        Bool.false_eq_true, if_false, if_true, sub_add_cancel, domain.total_length] using hamp.2
  · exact hvaluation .one prime
  · exact hvaluation .six prime
  · exact hvaluation .seven prime

/-- The right main and 1/6/7 amplitudes on their actual common divisor. -/
theorem literalPrimitivePooledTerminal_right_atoms
    (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset)
    (S : divisorPool (source.pools DE D).rightData.columns
      (fun j => ((source.pools DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (tag : PoolSourceTag pool) :
    (((terminal DE D).right S χ).tag tag).windows.multiplicity ≤
        idealDivisorCount (DE.val.2 ^ 2) ^ tupleDegree * 15 ^ tupleDegree ∧
      (((terminal DE D).right S χ).tag tag).zeroProductExponent ≤
        2 * (max lengthBound columnBound + 1) ∧
      ((((stages DE D).right S χ).tag tag).fiber ≠ 0 →
        (((terminal DE D).right S χ).tag tag).tailAmplitude ≤
          tailProfile * poolTagNormCharge pool tag / (Ideal.absNorm S.val : ℝ) ∧
        (((terminal DE D).right S χ).tag tag).zeroAmplitude ≤
          (zeroProfile * poolTagNormCharge pool tag / (Ideal.absNorm S.val : ℝ)) *
            Z ^ (geometry DE D true tag).sharpZeroExponent loss δ₁) := by
  have hDE := actual_common_pair_properties firstSource.columns firstSource.columns
    (fun i => (firstSource.ideal i).val) (fun i => (firstSource.ideal i).val) DE
  have htotal' : a.n₁ + a.n₂ + (data ξ).geometry.totalLength ≤
      max lengthBound columnBound := by
    rw [← domain.total_length]
    exact htotal.trans (le_max_left _ _)
  have hbound : 0 ≤ max lengthBound columnBound := hlengthBound.trans (le_max_left _ _)
  have htail : 0 ≤ tailProfile := mul_nonneg (sq_nonneg _)
    ((sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)).apply_nonneg _)
  have hzero : 0 ≤ zeroProfile := mul_nonneg (sq_nonneg _)
    ((sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)).apply_nonneg _)
  have tailBound (b : PoolSourceTag pool) (v : ℝ)
      (hv : v ≤ ((2 * amplitude ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
        sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
          (CanonicalRowBall.archTest K A.Sf 1)) :
      v ≤ tailProfile * poolTagNormCharge pool b / (Ideal.absNorm S.val : ℝ) := by
    calc
      v ≤ tailProfile / (Ideal.absNorm S.val : ℝ) := hv.trans_eq (by ring)
      _ ≤ _ := div_le_div_of_nonneg_right
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (one_le_poolTagNormCharge pool b) htail)
        (Nat.cast_nonneg _)
  have zeroBound (b : PoolSourceTag pool) (v : ℝ)
      (hv : v ≤ (zeroProfile / (Ideal.absNorm S.val : ℝ)) *
        Z ^ ((geometry DE D true b).sharpZeroExponent loss δ₁ +
          (geometry DE D true b).tag.poolLength step)) :
      v ≤ (zeroProfile * poolTagNormCharge pool b / (Ideal.absNorm S.val : ℝ)) *
        Z ^ (geometry DE D true b).sharpZeroExponent loss δ₁ := by
    have hb := (source.block DE).pooledTerminalGeometry_charge internal pool D.val
      (2 * loss + cutoffExponent) (by positivity) true b
    have hs := terminal_amplitude_shift_by_charge Z zeroProfile (Ideal.absNorm S.val : ℝ)
      ((geometry DE D true b).sharpZeroExponent loss δ₁ + (geometry DE D true b).tag.poolLength step)
      ((geometry DE D true b).tag.poolLength step) (poolTagNormCharge pool b)
      (zero_lt_one.trans hZ) hzero (Nat.cast_nonneg _) hb
    exact hv.trans (by simpa only [add_sub_cancel_right] using hs)
  have hvaluation (valuation : AmplifierValuation) (prime : pool.primes) :
      (((terminal DE D).right S χ).tag (valuation.sourceTag prime)).windows.multiplicity ≤
          idealDivisorCount (DE.val.2 ^ 2) ^ tupleDegree * 15 ^ tupleDegree ∧
        (((terminal DE D).right S χ).tag (valuation.sourceTag prime)).zeroProductExponent ≤
          2 * (max lengthBound columnBound + 1) ∧
        ((((stages DE D).right S χ).tag (valuation.sourceTag prime)).fiber ≠ 0 →
          (((terminal DE D).right S χ).tag (valuation.sourceTag prime)).tailAmplitude ≤
            tailProfile * poolTagNormCharge pool (valuation.sourceTag prime) / (Ideal.absNorm S.val : ℝ) ∧
          (((terminal DE D).right S χ).tag (valuation.sourceTag prime)).zeroAmplitude ≤
            (zeroProfile * poolTagNormCharge pool (valuation.sourceTag prime) / (Ideal.absNorm S.val : ℝ)) *
              Z ^ (geometry DE D true (valuation.sourceTag prime)).sharpZeroExponent loss δ₁) := by
    have h := rightValuationBounds DE D S χ valuation prime
    refine ⟨?_, ?_, ?_⟩
    · rw [h.1]
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      cases valuation <;> norm_num [AmplifierValuation.multiplicity]
    · rw [h.2.1]
      exact CanonicalOriginalTerminalPowers.zeroProductExponent_le
        _ _ loss (max lengthBound columnBound) hbound htotal'
        (idealLogLength_nonneg Z hZ _
          (mul_ne_zero hDE.2.1 (powerIdeal prime.val valuation.multiplicity).property.1)) hlossOne
    · intro hf
      have hamp := h.2.2 hf
      refine ⟨tailBound _ _ hamp.1, zeroBound _ _ ?_⟩
      simpa only [OriginalNominalGeometry.sharpZeroExponent,
        FirstCommonCharacterBlock.pooledTerminalGeometry_valuation,
        OriginalNominalGeometry.canonicalPoolError, OriginalNominalGeometry.forPoolError,
        FirstCommonCharacterBlock.literalRightCoordinates_first,
        Bool.false_eq_true, if_false, if_true, sub_add_cancel, domain.total_length] using hamp.2
  rcases tag with u | prime | prime | prime
  · have h := rightMainBounds DE D S χ
    refine ⟨?_, ?_, ?_⟩
    · rw [h.1]
      exact Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0 < (15 : ℕ)) tupleDegree)
    · rw [h.2.1]
      exact CanonicalOriginalTerminalPowers.zeroProductExponent_le
        _ _ loss (max lengthBound columnBound) hbound htotal'
        (idealLogLength_nonneg Z hZ DE.val.2 hDE.2.1) hlossOne
    · intro hf
      have hamp := h.2.2 hf
      refine ⟨tailBound _ _ hamp.1, zeroBound _ _ ?_⟩
      simpa only [OriginalNominalGeometry.sharpZeroExponent,
        FirstCommonCharacterBlock.pooledTerminalGeometry,
        OriginalNominalGeometry.canonicalMain, OriginalNominalGeometry.forMain,
        FirstCommonCharacterBlock.literalRightCoordinates_first,
        Bool.false_eq_true, if_false, if_true, sub_add_cancel, domain.total_length] using hamp.2
  · exact hvaluation .one prime
  · exact hvaluation .six prime
  · exact hvaluation .seven prime

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledTerminal_left_atoms
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledTerminal_right_atoms
