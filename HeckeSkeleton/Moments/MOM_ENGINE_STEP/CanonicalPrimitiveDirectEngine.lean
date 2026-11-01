import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectConclusion
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveFirstTerminalConstants
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveFirstTerminalNonneg
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveSecondTerminalUniform
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineMassChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineOriginalWindows

/-!
# The actual direct branch at fixed engine choices

The fixed original profile window supplies both transformations and all
terminal estimates. The original prime window produces every analytic
input before a normalized child is selected. All sources, first Fourier
charts, second kernels and descendants are those of the existing direct
factory. The original mesh is preserved independently of the analytic
cutoff loss and is charged once in the mass exponent. The only source
estimate supplied at this internal boundary is the exact exceptional
budget of that same prepared source.
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

open CanonicalPrimitiveEngineChoices

namespace CompleteMovingRowRecipe

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (b : Box) (mesh : ℝ) (hmesh : 0 ≤ mesh) (orders : Finset (ℕ × ℕ))
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (first : CanonicalPrimitiveFirstTerminalConstants.Fixed μv ν C hDiff b orders)
variable (second : CanonicalPrimitiveSecondTerminalConstants.Fixed
  (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  μv hDiff C (rowBallFiniteFamily K A.Sf 1) b)
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {Index : Type*} {data : Index → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)
variable (W : NormProfileRecipe data) (ξ : Index)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable (hbudget : Q.FullJointBudget Z (a.m + a.q))
variable (hwidth : a.m + a.q ≤ b.widthMax) (hpadding : padding ≤ b.paddingMax)
variable (hcap : (data ξ).geometry.slotCount ≤ b.cap) (hlarge : b.fullThreshold ≤ Z)
variable (hfit : (data ξ).geometry.fitsMesh mesh)
variable (hslotsZero : (data ξ).geometry.slotCount = 0)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
variable (amplitude : ℝ) (hamplitude : 1 ≤ amplitude)
variable (profiles : RawProfileWindow rowDomain heightDomain (Set.Icc b.lo b.hi)
  (OriginalProfileAtomBounds.profileOrders orders ∪
    CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
  (data ξ) amplitude)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (htime : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable (heightC : ℝ)
variable (analyticWindow : CanonicalOriginalPrimeAnalyticProvider.Window
  (A := A) (P := P) (R := R) (data ξ).theta b.rawNormBound heightC)
variable (boundary : a.κ < 1 → FiniteOrderBoundary (K := K) ((a.κ + 1) / 2))
variable (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta)
variable (hbackground : (data ξ).plainBackground⁻¹ ∈ (data ξ).theta ∨
  ¬ FiniteOrder (data ξ).plainBackground)
variable (hslot : ∀ i, (data ξ).slotCoefficient i ∈ (data ξ).theta)
variable (hslotInverse : ∀ i, ((data ξ).slotCoefficient i)⁻¹ ∈ (data ξ).theta)

local notation "canonicalLeft" => canonicalComparisonScale centered (Z ^ a.n₁) Y₁
local notation "canonicalRight" => canonicalComparisonScale centered (Z ^ a.n₂) Y₂
local notation "canonicalDomain" => domain.canonicalComparisonScales
local notation "hZ" => domain.scale
local notation "window₁" => profiles.restrictOrders Finset.subset_union_left
local notation "window₂" => profiles.restrictOrders Finset.subset_union_right
local notation "scaleWindows" =>
  CanonicalPrimitiveEngineOriginalWindows.scale_windows b domain hwidth hpadding
local notation "hY₁" => (scaleWindows).1
local notation "hY₂" => (scaleWindows).2.1
local notation "hleftPower" => (scaleWindows).2.2.1
local notation "hrightPower" => (scaleWindows).2.2.2.1
local notation "hY₁le" => (scaleWindows).2.2.2.2.1
local notation "hY₂le" => (scaleWindows).2.2.2.2.2.1
local notation "htotal" => (scaleWindows).2.2.2.2.2.2.1
local notation "hcolumn" => (scaleWindows).2.2.2.2.2.2.2
local notation "hannulusZ" =>
  (b.threshold_windows Z (b.fullThreshold_spec.2.1.trans hlarge)).1
local notation "hlowerThreshold" =>
  (b.threshold_windows Z (b.fullThreshold_spec.2.1.trans hlarge)).2.1
local notation "chosenContour" => CanonicalPrimitiveEngineMassChoices.contour
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
local notation "hcontourPos" => CanonicalPrimitiveEngineMassChoices.contour_pos
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
local notation "hcontourQuarter" => CanonicalPrimitiveEngineMassChoices.contour_le_quarter
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
local notation "control" => CanonicalPrimitiveEngineControl.value amplitude t
local notation "internal" => Q.fullSupportParameters a Z
local notation "raw" => ((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ)
  internal Z t).raw canonicalLeft canonicalRight
local notation "source" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t canonicalLeft canonicalRight hZ hbudget centered
  (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one (hZ).le) b.tilt b.tilt_pos b.tilt_le_half


local notation "stages" => Q.literalPrimitiveDirectStages
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (step := b.step) (hstep := b.step_pos)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))

local notation "exceptional" => Q.literalPrimitiveDirectPredicates
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (step := b.step) (hstep := b.step_pos)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))

local notation "normalization" => Q.literalPrimitiveFirstNormalization μv ν C hroot hemb W ξ
  a Z t canonicalLeft canonicalRight hZ hbudget centered
  (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one (hZ).le) b.tilt b.tilt_pos b.tilt_le_half

local notation "computedInput" => literalPrimitiveDirectInput
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := mesh) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := hmesh) (hfit := hfit) (hsmall := b.width_margin) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (hcutoffPower₂ := (b.secondCutoff_le Z (hZ).le))
  (reference := reference) (href := href) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (originalBound := amplitude) (horiginalBound := (zero_le_one.trans hamplitude))
  (originalWindow := window₂) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (hprimeOrders := hprimeOrders)
  (δ := chosenContour) (analyticHeight := (heightC * (1 + Real.log Z))) (hδ := hcontourPos) (hδhi := hcontourQuarter)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (columnBound := b.columnBound) (normBox := b.rawNormBound) (heightC := heightC)
  (analyticWindow := analyticWindow) (boundary := boundary) (hslotInverse := hslotInverse)
  (hheight := le_rfl)
  (hbox := by dsimp only [Box.rawNormBound]; linarith)
  (leftExponent := b.lengthBound) (rightExponent := b.lengthBound)
  (hleftPower := hleftPower) (hrightPower := hrightPower)
  (hY₁le := hY₁le) (hY₂le := hY₂le) (hcolumn := hcolumn)

local notation "terminal" => Q.literalPrimitiveDirectDualCalibration
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le)) (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (orders := orders) (amplitude := amplitude) (profiles := window₁) (hrows := hrows) (ht := htime) (hwindow := (fun _ h => h.2)) (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (step := b.step)
  (hstep := b.step_pos) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le) (lo := b.lo) (hlo := b.lo_pos) (hloOne := b.lo_le_one) (hlowerThreshold := hlowerThreshold) (hlowerWindow := (fun _ h => h.1)) (hamplitude := hamplitude) (leftExponent := b.lengthBound) (rightExponent := b.lengthBound) (lengthBound := b.lengthBound)
  (columnBound := b.columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := b.loss_le_one) (hDiff := hDiff) (δ₂ := b.tilt)
  (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half) (sTail := second.sTail) (sZero := second.sZero) (Nsave := b.saving) (decay := b.secondDecay) (hdecay := b.secondDecay_gt_one)

local notation "secondConstant" =>
  CanonicalPrimitiveSecondTerminalUniform.Csecond μv ν C hDiff b second
local notation "massConstant" => CanonicalPrimitiveEngineMassChoices.constant
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
local notation "firstZero" => (source).dualZeroCost hDiff / Z ^ (a.m + a.q)
local notation "firstTail" =>
  (first.Ctail * (b.firstBox.cutoff Z) ^ (1 - b.firstBox.decay) * (source).tailCost first.sTail) /
    Z ^ (a.m + a.q)
local notation "secondZero" => (stages).dualSecondZeroBudget terminal normalization
  b.tilt second.Czero / Z ^ (a.m + a.q)
local notation "secondTail" => (stages).dualSecondTailBudget terminal normalization
  second.Cerror / Z ^ (a.m + a.q)
local notation "exceptionalCost" =>
  (stages).prepared.exceptionalBudget (raw).originalAtlas exceptional normalization / Z ^ (a.m + a.q)

/-- The exact exceptional term left to the independent original
exceptional producer. No change of rows or coefficients occurs here. -/
def literalPrimitiveDirectEngineExceptionalCost : ℝ := exceptionalCost


local notation "zeroBudget" => Q.literalPrimitiveDirectDualZeroBudget_le
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le)) (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (orders := orders) (amplitude := amplitude) (profiles := window₁) (hrows := hrows) (ht := htime) (hwindow := (fun _ h => h.2)) (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (step := b.step)
  (hstep := b.step_pos) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le) (lo := b.lo) (hlo := b.lo_pos) (hloOne := b.lo_le_one) (hlowerThreshold := hlowerThreshold) (hlowerWindow := (fun _ h => h.1)) (hamplitude := hamplitude) (leftExponent := b.lengthBound) (rightExponent := b.lengthBound) (lengthBound := b.lengthBound)
  (columnBound := b.columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := b.loss_le_one) (hDiff := hDiff) (δ₂ := b.tilt)
  (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half) (sTail := second.sTail) (sZero := second.sZero) (Nsave := b.saving) (decay := b.secondDecay) (hdecay := b.secondDecay_gt_one)
  (hcolumnBound := b.columnBound_nonneg) (εsum := b.ε / 8)
  (hεsum := div_pos b.ε_pos (by norm_num))

local notation "tailBudget" => Q.literalPrimitiveDirectDualTailBudget_le
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le)) (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (orders := orders) (amplitude := amplitude) (profiles := window₁) (hrows := hrows) (ht := htime) (hwindow := (fun _ h => h.2)) (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (step := b.step)
  (hstep := b.step_pos) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le) (lo := b.lo) (hlo := b.lo_pos) (hloOne := b.lo_le_one) (hlowerThreshold := hlowerThreshold) (hlowerWindow := (fun _ h => h.1)) (hamplitude := hamplitude) (leftExponent := b.lengthBound) (rightExponent := b.lengthBound) (lengthBound := b.lengthBound)
  (columnBound := b.columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := b.loss_le_one) (hDiff := hDiff) (δ₂ := b.tilt)
  (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half) (sTail := second.sTail) (sZero := second.sZero) (Nsave := b.saving) (decay := b.secondDecay) (hdecay := b.secondDecay_gt_one)
  (hcolumnBound := b.columnBound_nonneg) (εsum := b.ε / 8)
  (hεsum := div_pos b.ε_pos (by norm_num))

local notation "conclusion" => literalPrimitiveDirectConclusion
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := mesh) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := hmesh) (hfit := hfit) (hsmall := b.width_margin) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (hcutoffPower₂ := (b.secondCutoff_le Z (hZ).le))
  (reference := reference) (href := href) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (originalBound := amplitude) (horiginalBound := (zero_le_one.trans hamplitude))
  (originalWindow := window₂) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (hprimeOrders := hprimeOrders)
  (δ := chosenContour) (analyticHeight := (heightC * (1 + Real.log Z))) (hδ := hcontourPos) (hδhi := hcontourQuarter)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (hδsum := by linarith [b.tilt_le_quarter]) (herrorPos := b.error_pos)
  (hannulusThreshold := b.fullThreshold_spec.2.2.2.1.trans hlarge)
  (hscaleThreshold := (b.fullThreshold_spec.2.2.2.2 Z hlarge).1)
  (hpaidError := b.support_error_le)
  (profileDegree := 1) (heightDegree := 0)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound) (widthMax := b.widthMax)
  (massLoss := CanonicalPrimitiveEngineMassChoices.massLoss b) (heightConstant := heightC)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (hwidthMax := b.width_nonneg) (hmassLoss := CanonicalPrimitiveEngineMassChoices.massLoss_pos b)
  (htotal := htotal) (hwidth := hwidth)
  (hN := Q.literalPrimitiveFirstSource_column_norm μv ν C hroot hemb W ξ
    a Z t canonicalLeft canonicalRight hZ hbudget centered
    (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one (hZ).le) b.tilt b.tilt_pos b.tilt_le_half
    b.cap b.hi b.loss b.lengthBound b.lengthBound b.columnBound b.hi_ge_one hcap hannulusZ
    hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le window₂ hrows htime (fun _ h => h.2) hcolumn)
  (T := |t|) (control := control) (hT := abs_nonneg t)
  (hcontrol := CanonicalPrimitiveEngineControl.height_le amplitude t hamplitude)
  (hprofile := by simpa only [pow_one] using
    CanonicalPrimitiveEngineControl.amplitude_le amplitude t hamplitude)
  (hheight := by simp only [pow_zero, mul_one])
  (htilt₁ := CanonicalPrimitiveEngineMassChoices.tilt_eq_actual b)
  (htilt₂ := CanonicalPrimitiveEngineMassChoices.tilt_eq_actual b)
  (hcontour := CanonicalPrimitiveEngineMassChoices.contour_eq_actual
    (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC)

variable (finalConstant exceptionalConstant terminalExponent exceptionalExponent : ℝ)
variable (finalDegree exceptionalDegree : ℕ)
variable (hfinalConstant : 0 ≤ finalConstant) (hexceptionalConstant : 0 ≤ exceptionalConstant)
variable (hfirstDegree : firstDualOriginalProfileDegree b.cap 1 ≤ finalDegree)
variable (hsecondDegree : 2 * (b.cap + 2) ≤ finalDegree)
variable (hexceptionalDegree : exceptionalDegree ≤ finalDegree)
variable (hmassDegree : CanonicalPrimitiveEngineMassChoices.degree b ≤ finalDegree)
variable (hterminalExponent : b.paddingMax + 3 * b.step + b.ε ≤ terminalExponent)
variable (hexceptionalExponent : exceptionalExponent ≤ terminalExponent)
variable (hterminalConstant : 2 * first.Cfirst + 2 * secondConstant + exceptionalConstant ≤ finalConstant)
variable (hmassConstant : massConstant ≤ finalConstant)

/-- The complete direct branch from original windows and fixed mother
constants. Every normalized input and every nonexceptional estimate is
constructed internally, before invoking the same-family conclusion. -/
def literalPrimitiveDirectEngine
    (hexceptional : exceptionalCost ≤
      exceptionalConstant * control ^ exceptionalDegree * Z ^ exceptionalExponent) :
    PairedEngineConclusion (Ω := WithLp 2 (ℝ × ℝ)) centered (data ξ) a Z t Y₁ Y₂
      b.step (b.ε + mesh) terminalExponent finalConstant (control ^ finalDegree)
      (MovingEngineChildAdmissible A P R
        (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (data ξ)
        Set.univ (Set.Icc (0 : ℝ) b.hi) orders Z) := by
  have hcontrol : 1 ≤ control := CanonicalPrimitiveEngineControl.one_le amplitude t hamplitude
  have hprofile : amplitude ≤ control ^ (1 : ℕ) := by
    simpa only [pow_one] using CanonicalPrimitiveEngineControl.amplitude_le amplitude t hamplitude
  have hfirst := first.bound Q W ξ hroot hemb a Z t Y₁ Y₂ amplitude control
    hamplitude hcontrol hprofile centered domain hbudget hwidth hpadding hcap
    (b.fullThreshold_spec.2.2.1.trans hlarge) window₁ hrows htime (fun _ h => h.2)
    b.tilt b.tilt_pos b.tilt_le_half
  have hfirstZeroBound : firstZero ≤
      first.Cfirst * control ^ firstDualOriginalProfileDegree b.cap 1 * Z ^ (b.ε / 8) :=
    hfirst.2.1
  have hfirstTailBound : firstTail ≤
      first.Cfirst * control ^ firstDualOriginalProfileDegree b.cap 1 * Z ^ (-b.saving) :=
    hfirst.2.2.1
  have hparent : pairedStageEnergy centered (data ξ) a Z t canonicalLeft canonicalRight /
      Z ^ (a.m + a.q) ≤ firstZero + firstTail + (source).rawRowCost hDiff / Z ^ (a.m + a.q) := by
    simpa only [pairedStageEnergy_canonicalComparisonScales] using hfirst.2.2.2
  have hz := zeroBudget b.tilt second.Czero b.tilt_pos.le second.Czero_pos.le
  change secondZero ≤ CanonicalPrimitiveSecondTerminalUniform.coefficient
    μv ν C hDiff b second false false amplitude *
      Z ^ CanonicalPrimitiveSecondTerminalUniform.exponent b false false padding at hz
  have hzfixed := hz.trans (CanonicalPrimitiveSecondTerminalUniform.bound
    μv ν C hDiff b second false false amplitude control Z padding
    (zero_le_one.trans hamplitude) hcontrol (by simpa only [pow_one] using hprofile) (hZ).le hpadding)
  have ht := tailBudget second.Cerror second.Cerror_nonneg b.saving_ge_column
  change secondTail ≤ CanonicalPrimitiveSecondTerminalUniform.coefficient
    μv ν C hDiff b second false true amplitude *
      Z ^ CanonicalPrimitiveSecondTerminalUniform.exponent b false true padding at ht
  have htfixed := ht.trans (CanonicalPrimitiveSecondTerminalUniform.bound
    μv ν C hDiff b second false true amplitude control Z padding
    (zero_le_one.trans hamplitude) hcontrol (by simpa only [pow_one] using hprofile) (hZ).le hpadding)
  have hfirstExponent : b.ε / 8 ≤ terminalExponent := by
    linarith [b.padding_nonneg, b.step_pos, b.ε_pos]
  have htailExponent : -b.saving ≤ terminalExponent := by
    linarith [b.padding_nonneg, b.step_pos, b.ε_pos, b.saving_pos]
  have hz₁ := hfirstZeroBound.trans (CanonicalPrimitiveEngineControl.monomial_mono
    first.Cfirst_pos.le le_rfl hcontrol (hZ).le hfirstDegree hfirstExponent)
  have ht₁ := hfirstTailBound.trans (CanonicalPrimitiveEngineControl.monomial_mono
    first.Cfirst_pos.le le_rfl hcontrol (hZ).le hfirstDegree htailExponent)
  have hsecondPos := CanonicalPrimitiveSecondTerminalUniform.Csecond_pos μv ν C hDiff b second
  have hz₂ := hzfixed.trans (CanonicalPrimitiveEngineControl.monomial_mono
    hsecondPos.le le_rfl hcontrol (hZ).le hsecondDegree hterminalExponent)
  have ht₂ := htfixed.trans (CanonicalPrimitiveEngineControl.monomial_mono
    hsecondPos.le le_rfl hcontrol (hZ).le hsecondDegree hterminalExponent)
  have he := hexceptional.trans (CanonicalPrimitiveEngineControl.monomial_mono
    hexceptionalConstant le_rfl hcontrol (hZ).le hexceptionalDegree hexceptionalExponent)
  have hterminals : firstZero + secondZero + exceptionalCost + (firstTail + secondTail) ≤
      finalConstant * control ^ finalDegree * Z ^ terminalExponent := by
    calc
      _ ≤ first.Cfirst * control ^ finalDegree * Z ^ terminalExponent +
          secondConstant * control ^ finalDegree * Z ^ terminalExponent +
          exceptionalConstant * control ^ finalDegree * Z ^ terminalExponent +
          (first.Cfirst * control ^ finalDegree * Z ^ terminalExponent +
           secondConstant * control ^ finalDegree * Z ^ terminalExponent) :=
        add_le_add (add_le_add (add_le_add hz₁ hz₂) he) (add_le_add ht₁ ht₂)
      _ = (2 * first.Cfirst + 2 * secondConstant + exceptionalConstant) *
          control ^ finalDegree * Z ^ terminalExponent := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hterminalConstant
          (pow_nonneg (zero_le_one.trans hcontrol) _))
        (Real.rpow_nonneg (zero_le_one.trans (hZ).le) _)
  have hmass := (CanonicalPrimitiveEngineMassChoices.direct_bound
    (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC control Z hcontrol (hZ).le).trans
      (CanonicalPrimitiveEngineControl.monomial_mono hfinalConstant hmassConstant
        hcontrol (hZ).le hmassDegree le_rfl)
  have hden : 0 ≤ Z ^ (a.m + a.q) := Real.rpow_nonneg (zero_le_one.trans (hZ).le) _
  have hznonneg : 0 ≤ firstZero := div_nonneg ((source).dualZeroCost_nonneg hDiff) hden
  have htnonneg : 0 ≤ firstTail := div_nonneg
    (mul_nonneg (mul_nonneg first.Ctail_nonneg
      (Real.rpow_nonneg (zero_le_one.trans (b.firstBox.cutoff_ge_one (hZ).le)) _))
      ((source).tailCost_nonneg first.sTail)) hden
  have henonneg : 0 ≤ exceptionalCost := div_nonneg
    ((stages).prepared.exceptionalBudget_nonneg normalization (raw).originalAtlas exceptional) hden
  let out := conclusion terminal second.Cerror_nonneg second.Czero_pos.le
    (second.direct_bound Z) computedInput firstZero firstTail exceptionalCost
    hznonneg htnonneg henonneg hparent le_rfl hterminals hmass
  exact out.ofCanonicalComparisonScales

local notation "backgroundFamily" => literalPrimitiveDirectFamily
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := mesh) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := hmesh) (hfit := hfit) (hsmall := b.width_margin) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (hcutoffPower₂ := (b.secondCutoff_le Z (hZ).le))
  (reference := reference) (href := href) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (originalBound := amplitude) (horiginalBound := (zero_le_one.trans hamplitude))
  (originalWindow := window₂) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (hprimeOrders := hprimeOrders)
  (δ := chosenContour) (analyticHeight := (heightC * (1 + Real.log Z))) (hδ := hcontourPos) (hδhi := hcontourQuarter)
  (hone := hone) (hbackground := hbackground) (hslot := hslot) computedInput

local notation "backgroundRaw" => literalPrimitiveDirectFamily_raw_plainBackground
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := mesh) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := hmesh) (hfit := hfit) (hsmall := b.width_margin) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (hcutoffPower₂ := (b.secondCutoff_le Z (hZ).le))
  (reference := reference) (href := href) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (originalBound := amplitude) (horiginalBound := (zero_le_one.trans hamplitude))
  (originalWindow := window₂) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (hprimeOrders := hprimeOrders)
  (δ := chosenContour) (analyticHeight := (heightC * (1 + Real.log Z))) (hδ := hcontourPos) (hδhi := hcontourQuarter)
  (hone := hone) (hbackground := hbackground) (hslot := hslot) computedInput

variable (hexceptional : exceptionalCost ≤
  exceptionalConstant * control ^ exceptionalDegree * Z ^ exceptionalExponent)

local notation "backgroundEngine" => Q.literalPrimitiveDirectEngine
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (mesh := mesh) (hmesh := hmesh) (orders := orders)
  (hprimeOrders := hprimeOrders) (first := first) (second := second)
  (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
  (hcap := hcap) (hlarge := hlarge) (hfit := hfit) (hslotsZero := hslotsZero)
  (reference := reference) (href := href) (amplitude := amplitude) (hamplitude := hamplitude)
  (profiles := profiles) (hrows := hrows) (htime := htime) (hprime := hprime)
  (heightC := heightC) (analyticWindow := analyticWindow) (boundary := boundary)
  (hone := hone) (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
  (finalConstant := finalConstant) (exceptionalConstant := exceptionalConstant)
  (terminalExponent := terminalExponent) (exceptionalExponent := exceptionalExponent)
  (finalDegree := finalDegree) (exceptionalDegree := exceptionalDegree)
  (hfinalConstant := hfinalConstant) (hexceptionalConstant := hexceptionalConstant)
  (hfirstDegree := hfirstDegree) (hsecondDegree := hsecondDegree)
  (hexceptionalDegree := hexceptionalDegree) (hmassDegree := hmassDegree)
  (hterminalExponent := hterminalExponent) (hexceptionalExponent := hexceptionalExponent)
  (hterminalConstant := hterminalConstant) (hmassConstant := hmassConstant)
  (hexceptional := hexceptional)

/-- Exact background identity for the existing direct engine, through
its same finite enumeration and comparison-scale transport. -/
theorem literalPrimitiveDirectEngine_samePlainBackground :
    (backgroundEngine).SamePlainBackground := by
  change ∀ (i : Fin (Fintype.card ((backgroundFamily).active Finset.univ)))
      (z : WithLp 2 (ℝ × ℝ)),
    (((backgroundFamily).leftData Finset.univ
      ((Fintype.equivFin ((backgroundFamily).active Finset.univ)).symm i) z).plainBackground =
        (data ξ).plainBackground) ∧
    (((backgroundFamily).rightData Finset.univ
      ((Fintype.equivFin ((backgroundFamily).active Finset.univ)).symm i) z).plainBackground =
        (data ξ).plainBackground)
  exact fun i z => CanonicalPlainBackgroundTransport.selectedFin
    backgroundFamily (data ξ) backgroundRaw i z

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectEngine

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectEngine_samePlainBackground
