import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.EngineAnnulusSupport
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.LiteralPooledFamilyAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalMeshPooledEngine

/-!
# Actual support inheritance for the original-mesh pooled engine

The engine's public children are precisely the original sigma family's
frozen children under its existing finite reindexing. The comparison
scale transport changes only the parent estimate. Reading these same
children therefore exposes their positive annulus and strict prime
support without changing any numerical output field.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineInduction

open HeckeSkeleton.Moments.EngineStep

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

open CanonicalPrimitiveEngineChoices HeckeGeneral.Bridge

namespace OriginalMeshPooledSupport

open EngineStep.CompleteMovingRowRecipe

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (b : Box) (orders : Finset (ℕ × ℕ))
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
variable (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : (data ξ).geometry.fitsMesh mesh)
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
local notation "chosenContour" => EngineInduction.OriginalMeshEngineMass.contour
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
local notation "hcontourPos" => EngineInduction.OriginalMeshEngineMass.contour_pos
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
local notation "hcontourQuarter" => EngineInduction.OriginalMeshEngineMass.contour_le_quarter
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
local notation "control" => CanonicalPrimitiveEngineControl.value amplitude t
local notation "internal" => Q.fullSupportParameters a Z
local notation "raw" => ((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ)
  internal Z t).raw canonicalLeft canonicalRight
local notation "firstSource" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t canonicalLeft canonicalRight hZ hbudget centered
  (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one (hZ).le) b.tilt b.tilt_pos b.tilt_le_half


local notation "hN" => Q.literalPrimitiveFirstSource_column_norm μv ν C hroot hemb W ξ
  a Z t canonicalLeft canonicalRight hZ hbudget centered
  (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one (hZ).le) b.tilt b.tilt_pos b.tilt_le_half
  b.cap b.hi b.loss b.lengthBound b.lengthBound b.columnBound b.hi_ge_one hcap hannulusZ
  hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le window₂ hrows htime (fun _ h => h.2) hcolumn

variable (Drecipe : ComparisonPoissonCoefficientData K A)
variable (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
variable {bad : Finset (HeightOneSpectrum (𝓞 K))}
variable (pool : PowerScaleExteriorPool A bad Z (b.step / 3) b.loss)
variable (hdensity : 0 < pool.rowDensity b.rowBound b.columnBound)
variable (hmassLarge : EngineInduction.OriginalMeshEngineMass.pooledThreshold (A := A) b ≤ Z)

local notation "source" => Q.literalPrimitivePooledSource
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)

local notation "stages" => Q.literalPrimitivePooledStages
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)
  (hstep := b.step_pos) (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))

local notation "exceptional" => Q.literalPrimitivePooledPredicates
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)
  (hstep := b.step_pos) (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))

local notation "normalization" => Q.literalPrimitivePooledNormalization
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)

local notation "computedInput" => literalPrimitivePooledInput
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := mesh) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := hmesh) (hfit := hfit) (hsmall := b.width_margin)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (hcutoffPower₂ := (b.secondCutoff_le Z (hZ).le))
  (reference := reference) (href := href) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (originalBound := amplitude) (horiginalBound := (zero_le_one.trans hamplitude))
  (originalWindow := window₂) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (hprimeOrders := hprimeOrders)
  (δ := chosenContour) (analyticHeight := (heightC * (1 + Real.log Z))) (hδ := hcontourPos) (hδhi := hcontourQuarter)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
  (normBox := b.rawNormBound) (heightC := heightC)
  (analyticWindow := analyticWindow) (boundary := boundary) (hslotInverse := hslotInverse)
  (hheight := le_rfl)
  (hbox := by dsimp only [Box.rawNormBound]; linarith)

local notation "terminal" => Q.literalPrimitivePooledDualCalibration
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le)) (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (orders := orders) (amplitude := amplitude) (profiles := window₁) (hrows := hrows) (ht := htime) (hwindow := (fun _ h => h.2)) (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (step := b.step)
  (hstep := b.step_pos) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le) (lo := b.lo) (hlo := b.lo_pos) (hloOne := b.lo_le_one) (hlowerThreshold := hlowerThreshold) (hlowerWindow := (fun _ h => h.1)) (hamplitude := hamplitude) (leftExponent := b.lengthBound) (rightExponent := b.lengthBound) (lengthBound := b.lengthBound)
  (columnBound := b.columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := b.loss_le_one) (hDiff := hDiff) (δ₂ := b.tilt)
  (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half) (sTail := second.sTail) (sZero := second.sZero) (Nsave := b.saving) (decay := b.secondDecay) (hdecay := b.secondDecay_gt_one) (reference := reference) (href := href)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg) (pool := pool) (hdensity := hdensity)

local notation "secondConstant" =>
  CanonicalPrimitiveSecondTerminalUniform.Csecond μv ν C hDiff b second
local notation "massConstant" => EngineInduction.OriginalMeshEngineMass.constant
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
local notation "firstZero" => (firstSource).dualZeroCost hDiff / Z ^ (a.m + a.q)
local notation "firstTail" =>
  (first.Ctail * (b.firstBox.cutoff Z) ^ (1 - b.firstBox.decay) * (firstSource).tailCost first.sTail) /
    Z ^ (a.m + a.q)
local notation "secondZero" => (stages).dualSecondZeroBudget terminal normalization
  b.tilt second.Czero / Z ^ (a.m + a.q)
local notation "secondTail" => (stages).dualSecondTailBudget terminal normalization
  second.Cerror / Z ^ (a.m + a.q)
local notation "exceptionalCost" =>
  (stages).supported.gated.exceptionalBudget (raw).originalAtlas exceptional normalization / Z ^ (a.m + a.q)


local notation "zeroBudget" => Q.literalPrimitivePooledDualZeroBudget_le
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le)) (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (orders := orders) (amplitude := amplitude) (profiles := window₁) (hrows := hrows) (ht := htime) (hwindow := (fun _ h => h.2)) (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (step := b.step)
  (hstep := b.step_pos) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le) (lo := b.lo) (hlo := b.lo_pos) (hloOne := b.lo_le_one) (hlowerThreshold := hlowerThreshold) (hlowerWindow := (fun _ h => h.1)) (hamplitude := hamplitude) (leftExponent := b.lengthBound) (rightExponent := b.lengthBound) (lengthBound := b.lengthBound)
  (columnBound := b.columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := b.loss_le_one) (hDiff := hDiff) (δ₂ := b.tilt)
  (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half) (sTail := second.sTail) (sZero := second.sZero) (Nsave := b.saving) (decay := b.secondDecay) (hdecay := b.secondDecay_gt_one) (reference := reference) (href := href)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg) (pool := pool) (hdensity := hdensity)
  (hlarge := (b.threshold_windows Z (b.fullThreshold_spec.2.1.trans hlarge)).2.2)
  (εsum := b.ε / 8) (hεsum := div_pos b.ε_pos (by norm_num))

local notation "tailBudget" => Q.literalPrimitivePooledDualTailBudget_le
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le)) (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (orders := orders) (amplitude := amplitude) (profiles := window₁) (hrows := hrows) (ht := htime) (hwindow := (fun _ h => h.2)) (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (step := b.step)
  (hstep := b.step_pos) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le) (lo := b.lo) (hlo := b.lo_pos) (hloOne := b.lo_le_one) (hlowerThreshold := hlowerThreshold) (hlowerWindow := (fun _ h => h.1)) (hamplitude := hamplitude) (leftExponent := b.lengthBound) (rightExponent := b.lengthBound) (lengthBound := b.lengthBound)
  (columnBound := b.columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := b.loss_le_one) (hDiff := hDiff) (δ₂ := b.tilt)
  (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half) (sTail := second.sTail) (sZero := second.sZero) (Nsave := b.saving) (decay := b.secondDecay) (hdecay := b.secondDecay_gt_one) (reference := reference) (href := href)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg) (pool := pool) (hdensity := hdensity)
  (hlarge := (b.threshold_windows Z (b.fullThreshold_spec.2.1.trans hlarge)).2.2)
  (εsum := b.ε / 8) (hεsum := div_pos b.ε_pos (by norm_num))

local notation "conclusion" => literalPrimitivePooledConclusion
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := mesh) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := hmesh) (hfit := hfit) (hsmall := b.width_margin)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (hcutoffPower₂ := (b.secondCutoff_le Z (hZ).le))
  (reference := reference) (href := href) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (originalBound := amplitude) (horiginalBound := (zero_le_one.trans hamplitude))
  (originalWindow := window₂) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (hprimeOrders := hprimeOrders)
  (δ := chosenContour) (analyticHeight := (heightC * (1 + Real.log Z))) (hδ := hcontourPos) (hδhi := hcontourQuarter)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
  (hδsum := by linarith [b.tilt_le_quarter]) (herrorPos := b.error_pos)
  (hannulusThreshold := (pow_le_pow_right₀ b.hi_ge_one
    (by omega : b.cap ≤ 2 * b.cap)).trans (b.fullThreshold_spec.2.2.2.2 Z hlarge).1)
  (hscaleThreshold := (b.fullThreshold_spec.2.2.2.2 Z hlarge).1)
  (hpaidError := b.support_error_le)
  (profileDegree := 1) (heightDegree := 0) (widthMax := b.widthMax)
  (massLoss := EngineInduction.OriginalMeshEngineMass.massLoss b) (heightConstant := heightC)
  (hwidthMax := b.width_nonneg) (hmassLoss := EngineInduction.OriginalMeshEngineMass.massLoss_pos b)
  (hwidth := hwidth)
  (T := |t|) (control := control) (hT := abs_nonneg t)
  (hcontrol := CanonicalPrimitiveEngineControl.height_le amplitude t hamplitude)
  (hprofile := by simpa only [pow_one] using
    CanonicalPrimitiveEngineControl.amplitude_le amplitude t hamplitude)
  (hheight := by simp only [pow_zero, mul_one])
  (htilt₁ := EngineInduction.OriginalMeshEngineMass.tilt_eq_actual b)
  (htilt₂ := EngineInduction.OriginalMeshEngineMass.tilt_eq_actual b)
  (hcontour := EngineInduction.OriginalMeshEngineMass.contour_eq_actual
    (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC)
  (heps := b.loss_pos) (hepsSmall := b.pool_separation.2)

variable (finalConstant exceptionalConstant terminalExponent exceptionalExponent : ℝ)
variable (finalDegree exceptionalDegree : ℕ)
variable (hfinalConstant : 0 ≤ finalConstant) (hexceptionalConstant : 0 ≤ exceptionalConstant)
variable (hfirstDegree : firstDualOriginalProfileDegree b.cap 1 ≤ finalDegree)
variable (hsecondDegree : 2 * (b.cap + 2) ≤ finalDegree)
variable (hexceptionalDegree : exceptionalDegree ≤ finalDegree)
variable (hmassDegree : EngineInduction.OriginalMeshEngineMass.degree b ≤ finalDegree)
variable (hterminalExponent : b.paddingMax + 3 * b.step + b.ε ≤ terminalExponent)
variable (hexceptionalExponent : exceptionalExponent ≤ terminalExponent)
variable (hterminalConstant : 2 * first.Cfirst + 2 * secondConstant + exceptionalConstant ≤ finalConstant)
variable (hmassConstant : massConstant ≤ finalConstant)

local notation "actualFamily" => literalPrimitivePooledFamily
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := mesh) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := hmesh) (hfit := hfit) (hsmall := b.width_margin)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (hcutoffPower₂ := (b.secondCutoff_le Z (hZ).le))
  (reference := reference) (href := href) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (originalBound := amplitude) (horiginalBound := (zero_le_one.trans hamplitude))
  (originalWindow := window₂) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (hprimeOrders := hprimeOrders)
  (δ := chosenContour) (analyticHeight := (heightC * (1 + Real.log Z))) (hδ := hcontourPos) (hδhi := hcontourQuarter)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
  computedInput

local notation "familySupport" => LiteralPooledFamilySupport.literalPrimitivePooled_family_annulusSupport
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := mesh) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := hmesh) (hfit := hfit) (hsmall := b.width_margin)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (hcutoffPower₂ := (b.secondCutoff_le Z (hZ).le))
  (reference := reference) (href := href) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (originalBound := amplitude) (horiginalBound := (zero_le_one.trans hamplitude))
  (originalWindow := window₂) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (hprimeOrders := hprimeOrders)
  (δ := chosenContour) (analyticHeight := (heightC * (1 + Real.log Z))) (hδ := hcontourPos) (hδhi := hcontourQuarter)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
  computedInput

variable (hexceptional : exceptionalCost ≤
  exceptionalConstant * control ^ exceptionalDegree * Z ^ exceptionalExponent)

local notation "engine" =>
  EngineStep.CompleteMovingRowRecipe.literalOriginalMeshPooledEngine
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff)
  (b := b) (orders := orders) (hprimeOrders := hprimeOrders) (first := first)
  (second := second) (Q := Q) (W := W) (ξ := ξ)
  (hroot := hroot) (hemb := hemb) (a := a) (Z := Z)
  (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
  (hcap := hcap) (hlarge := hlarge) (mesh := mesh) (hmesh := hmesh)
  (hfit := hfit) (reference := reference) (href := href) (amplitude := amplitude)
  (hamplitude := hamplitude) (profiles := profiles) (hrows := hrows) (htime := htime)
  (hprime := hprime) (heightC := heightC) (analyticWindow := analyticWindow) (boundary := boundary)
  (hone := hone) (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
  (Drecipe := Drecipe) (hD := hD) (pool := pool) (hdensity := hdensity)
  (hmassLarge := hmassLarge) (finalConstant := finalConstant) (exceptionalConstant := exceptionalConstant) (terminalExponent := terminalExponent)
  (exceptionalExponent := exceptionalExponent) (finalDegree := finalDegree) (exceptionalDegree := exceptionalDegree) (hfinalConstant := hfinalConstant)
  (hexceptionalConstant := hexceptionalConstant) (hfirstDegree := hfirstDegree) (hsecondDegree := hsecondDegree) (hexceptionalDegree := hexceptionalDegree)
  (hmassDegree := hmassDegree) (hterminalExponent := hterminalExponent) (hexceptionalExponent := hexceptionalExponent) (hterminalConstant := hterminalConstant)
  (hmassConstant := hmassConstant) (hexceptional := hexceptional)

/-- Both support proofs concern the exact public output of the
original-mesh pooled producer. -/
theorem annulusSupport : EngineAnnulusSupport engine b.lo b.hi orders := by
  constructor
  · change ∀ (i : Fin (Fintype.card ((actualFamily).active Finset.univ)))
        (z : WithLp 2 (ℝ × ℝ)),
      InFixedProfileWindow Set.univ Set.univ (Set.Icc (b.lo / b.hi) b.hi) orders
          ((actualFamily).leftData Finset.univ
            ((Fintype.equivFin ((actualFamily).active Finset.univ)).symm i) z) ∧
        InFixedProfileWindow Set.univ Set.univ (Set.Icc (b.lo / b.hi) b.hi) orders
          ((actualFamily).rightData Finset.univ
            ((Fintype.equivFin ((actualFamily).active Finset.univ)).symm i) z)
    exact fun i z => (familySupport).window
      ((Fintype.equivFin ((actualFamily).active Finset.univ)).symm i) z
  · change ∀ (i : Fin (Fintype.card ((actualFamily).active Finset.univ)))
        (z : WithLp 2 (ℝ × ℝ)),
      (∀ j t, Function.support
        ((((actualFamily).leftData Finset.univ
          ((Fintype.equivFin ((actualFamily).active Finset.univ)).symm i) z).geometry.slots j).profile t) ⊆
          Set.Ioo (1 : ℝ) 2) ∧
        (∀ j t, Function.support
          ((((actualFamily).rightData Finset.univ
            ((Fintype.equivFin ((actualFamily).active Finset.univ)).symm i) z).geometry.slots j).profile t) ⊆
          Set.Ioo (1 : ℝ) 2)
    exact fun i z => (familySupport).prime
      ((Fintype.equivFin ((actualFamily).active Finset.univ)).symm i) z

variable (narrowLo narrowHi : ℝ) (hnarrowLo : 0 < narrowLo) (hnarrowHi : 1 ≤ narrowHi)
variable (hnarrowHiLe : narrowHi ≤ b.hi)
variable (narrowProfiles : RawProfileWindow rowDomain heightDomain (Set.Icc narrowLo narrowHi)
  (OriginalProfileAtomBounds.profileOrders orders ∪
    CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
  (data ξ) amplitude)

local notation "narrowWindow₂" => narrowProfiles.restrictOrders Finset.subset_union_right
local notation "narrowThreshold" =>
  (pow_le_pow_left₀ (zero_le_one.trans hnarrowHi) hnarrowHiLe (b.cap + 2)).trans hannulusZ
local notation "narrowPrime" => (show
    ∀ i, Function.support (narrowProfiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2 from by
  intro i y hy
  apply hprime i
  simpa only [Function.mem_support, ← profiles.prime_eq, ← narrowProfiles.prime_eq] using hy)

local notation "narrowFamily" => literalPrimitivePooledFamily
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := mesh) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := hmesh) (hfit := hfit) (hsmall := b.width_margin)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (hcutoffPower₂ := (b.secondCutoff_le Z (hZ).le))
  (reference := reference) (href := href) (lo := narrowLo) (hi := narrowHi) (hlo := hnarrowLo) (hhi := hnarrowHi)
  (orders := orders) (originalBound := amplitude) (horiginalBound := (zero_le_one.trans hamplitude))
  (originalWindow := narrowWindow₂) (hrows := hrows) (htime := htime) (hprime := narrowPrime)
  (hcap := hcap) (hannulusZ := narrowThreshold) (domain := canonicalDomain) (hprimeOrders := hprimeOrders)
  (δ := chosenContour) (analyticHeight := (heightC * (1 + Real.log Z))) (hδ := hcontourPos) (hδhi := hcontourQuarter)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
  computedInput

local notation "narrowCertificate" => LiteralPooledFamilySupport.literalPrimitivePooled_family_originalSupport
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := mesh) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := hmesh) (hfit := hfit) (hsmall := b.width_margin)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (hcutoffPower₂ := (b.secondCutoff_le Z (hZ).le))
  (reference := reference) (href := href) (lo := narrowLo) (hi := narrowHi) (hlo := hnarrowLo) (hhi := hnarrowHi)
  (orders := orders) (originalBound := amplitude) (horiginalBound := (zero_le_one.trans hamplitude))
  (originalWindow := narrowWindow₂) (hrows := hrows) (htime := htime) (hprime := narrowPrime)
  (hcap := hcap) (hannulusZ := narrowThreshold) (domain := canonicalDomain) (hprimeOrders := hprimeOrders)
  (δ := chosenContour) (analyticHeight := (heightC * (1 + Real.log Z))) (hδ := hcontourPos) (hδhi := hcontourQuarter)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
  computedInput

/-- The actual numerical normalization may use a wider box. Its
literal calibration is unchanged by the independent original window,
so the same selected children retain the original smaller support. -/
theorem narrowAnnulusSupport : EngineAnnulusSupport engine narrowLo narrowHi orders := by
  have original : FamilyOriginalSupport actualFamily narrowLo narrowHi :=
    FamilyOriginalSupport.congrData narrowCertificate (fun _ _ => rfl) (fun _ _ => rfl)
  have tightFamily := original.strengthen Finset.univ hnarrowLo.le hnarrowHi (familySupport).window
  constructor
  · change ∀ (i : Fin (Fintype.card ((actualFamily).active Finset.univ)))
        (z : WithLp 2 (ℝ × ℝ)),
      InFixedProfileWindow Set.univ Set.univ (Set.Icc (narrowLo / narrowHi) narrowHi) orders
          ((actualFamily).leftData Finset.univ
            ((Fintype.equivFin ((actualFamily).active Finset.univ)).symm i) z) ∧
        InFixedProfileWindow Set.univ Set.univ (Set.Icc (narrowLo / narrowHi) narrowHi) orders
          ((actualFamily).rightData Finset.univ
            ((Fintype.equivFin ((actualFamily).active Finset.univ)).symm i) z)
    exact fun i z => tightFamily.window
      ((Fintype.equivFin ((actualFamily).active Finset.univ)).symm i) z
  · change ∀ (i : Fin (Fintype.card ((actualFamily).active Finset.univ)))
        (z : WithLp 2 (ℝ × ℝ)),
      (∀ j t, Function.support
        ((((actualFamily).leftData Finset.univ
          ((Fintype.equivFin ((actualFamily).active Finset.univ)).symm i) z).geometry.slots j).profile t) ⊆
          Set.Ioo (1 : ℝ) 2) ∧
        (∀ j t, Function.support
          ((((actualFamily).rightData Finset.univ
            ((Fintype.equivFin ((actualFamily).active Finset.univ)).symm i) z).geometry.slots j).profile t) ⊆
          Set.Ioo (1 : ℝ) 2)
    exact fun i z => tightFamily.prime
      ((Fintype.equivFin ((actualFamily).active Finset.univ)).symm i) z

end OriginalMeshPooledSupport
end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshPooledSupport.annulusSupport

#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshPooledSupport.narrowAnnulusSupport
