import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledIndexedWeight
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledKernelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveMassCoefficient
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRawWidth
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalIdealWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveTerminalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStageFibres
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualSourceMass

/-!
# Computed coefficient windows on the actual pooled dispatcher

The main, one, six and seven branches retain their exact geometries
and the common fixed Fourier kernels.  The moving tag exponent is
recorded separately for the original amplified arithmetic index.
The full sixth root is bounded by its actual second common ideal.
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
local notation "raw" => atoms.raw Y₁ Y₂


local notation "firstSource" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable (cap : ℕ) (loss cutoffExponent : ℝ)
variable (hloss : 0 ≤ loss) (hcutoffExponent : 0 ≤ cutoffExponent)
variable (step error mesh : ℝ) (hstep : 0 < step) (herror : 0 ≤ error) (hmesh : 0 ≤ mesh)
variable (hfit : (data ξ).geometry.fitsMesh mesh)
variable (hsmall : 2 * (2 * loss + cutoffExponent) ≤ step)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable (cutoff₂ : ℝ) (hcutoff₂ : 1 ≤ cutoff₂)
variable (hcutoffPower : cutoff ≤ Z ^ cutoffExponent)
variable (hcutoffPower₂ : cutoff₂ ≤ Z ^ cutoffExponent)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain : Set ℝ}
variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
variable (orders : Finset (ℕ × ℕ)) (originalBound : ℝ) (horiginalBound : 0 ≤ originalBound)
variable (originalWindow : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi)
  (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
  (data ξ) originalBound)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (htime : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (originalWindow.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (hannulusZ : hi ^ (cap + 2) ≤ Z ^ loss)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (δ analyticHeight : ℝ) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)
variable (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta)
variable (hbackground : (data ξ).plainBackground⁻¹ ∈ (data ξ).theta ∨
  ¬ FiniteOrder (data ξ).plainBackground)
variable (hslot : ∀ i, (data ξ).slotCoefficient i ∈ (data ξ).theta)

variable (lengthBound columnBound : ℝ)
variable (hlengthBound : 0 ≤ lengthBound) (hcolumnBound : 0 ≤ columnBound)
variable (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
variable (hN : ∀ i ∈ firstSource.columns,
  (Ideal.absNorm (firstSource.ideal i).val : ℝ) ≤ Z ^ columnBound)
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {eps : ℝ}
variable (pool : PowerScaleExteriorPool A bad Z (step / 3) eps)
variable (hdensity : 0 < pool.rowDensity
  (literalPrimitivePoolRowExponent (lengthBound := lengthBound) (columnBound := columnBound)
    (loss := loss) (cutoffExponent := cutoffExponent)) columnBound)

local notation "source" => Q.literalPrimitivePooledSource
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)

local notation "stages" => Q.literalPrimitivePooledStages
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)
  (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

local notation "exceptional" => Q.literalPrimitivePooledPredicates
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)
  (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

local notation "normalization" => Q.literalPrimitivePooledNormalization
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)

local notation "leftRows" => Q.literalPrimitiveLeftPooledRows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
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
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)

/-- No primitive source family or aggregate estimate is supplied.
All cases are selected from the same original live finite key. -/
local notation "factories" => literalPrimitivePooledFactory
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)

variable (hδsum : δ₁ + δ₂ ≤ 1 / 2)
variable (herrorPos : 0 < error)
variable (hannulusThreshold : hi ^ cap ≤ Z ^ error)
variable (hscaleThreshold : hi ^ (2 * cap) ≤ Z ^ error)
variable (hpaidError : 2 * loss + cutoffExponent ≤ error)

local notation "sourceCertificates" => literalPrimitivePooledSourceIntegral
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)

local notation "arithmetic" => stages.supported.gated.arithmeticLabels raw.originalAtlas
  hcap exceptional normalization
local notation "tag" => stages.supported.gated.arithmeticTag raw.originalAtlas
  exceptional normalization

local notation "massCertificates" => literalPrimitivePooledKernelMass
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
  (hδsum := hδsum)

local notation "indexCertificates" => literalPrimitivePooledIndexedWeight
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
  (hδsum := hδsum) (herrorPos := herrorPos)
  (hannulusThreshold := hannulusThreshold) (hscaleThreshold := hscaleThreshold)
  (hpaidError := hpaidError)

local notation "unitIndex" =>
  ((sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).index : ℝ)
local notation "fixedFirstKernel" =>
  (CanonicalLiteralKernelConstants.firstOrders K A σ ω ψ cap (orders.sup Prod.snd)).sup
    (schwartzSeminormFamily ℝ ℝ ℂ)
    (ActualGaussStage.canonicalRowBallKernel
      (A := A) (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν δ₁ hδ₁ hδ₁half)
local notation "fixedSecondKernel" =>
  (CanonicalLiteralKernelConstants.secondOrders K A σ ω ψ cap (orders.sup Prod.snd)).sup
    (schwartzSeminormFamily ℝ ℝ ℂ)
    (ActualGaussStage.canonicalRowBallKernel
      (A := A) (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν δ₂ hδ₂ hδ₂half)

/-- This is the geometry already used by the selected original pool tag. -/
def literalPrimitivePooledGeometryAt
    (j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization) :
    OriginalNominalGeometry (K := K) internal Z step := by
  rcases j with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩
  · rcases leaf with leaf | (⟨prime, leaf⟩ | (⟨prime, leaf⟩ | ⟨prime, leaf⟩))
    · let baseGeometry := OriginalNominalGeometry.canonicalMain
        (a := internal) (Z := Z) (step := step)
        ((source.block DE).literalLeftCoordinates D.val) (2 * loss + cutoffExponent)
        (zero_lt_one.trans hZ) (by positivity)
      exact baseGeometry.atSecondPattern leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity
        leaf.1.block.left_positive leaf.1.block.right_positive
        (leaf.1.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ leaf.1.rowLabel)
    · let baseGeometry := OriginalNominalGeometry.canonicalPoolError
        (a := internal) pool .one prime ((source.block DE).literalLeftCoordinates D.val)
        (2 * loss + cutoffExponent) (by positivity : 0 ≤ 2 * loss + cutoffExponent)
      exact baseGeometry.atSecondPattern leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity
        leaf.1.block.left_positive leaf.1.block.right_positive
        (leaf.1.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ leaf.1.rowLabel)
    · let baseGeometry := OriginalNominalGeometry.canonicalPoolError
        (a := internal) pool .six prime ((source.block DE).literalLeftCoordinates D.val)
        (2 * loss + cutoffExponent) (by positivity : 0 ≤ 2 * loss + cutoffExponent)
      exact baseGeometry.atSecondPattern leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity
        leaf.1.block.left_positive leaf.1.block.right_positive
        (leaf.1.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ leaf.1.rowLabel)
    · let baseGeometry := OriginalNominalGeometry.canonicalPoolError
        (a := internal) pool .seven prime ((source.block DE).literalLeftCoordinates D.val)
        (2 * loss + cutoffExponent) (by positivity : 0 ≤ 2 * loss + cutoffExponent)
      exact baseGeometry.atSecondPattern leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity
        leaf.1.block.left_positive leaf.1.block.right_positive
        (leaf.1.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ leaf.1.rowLabel)
  · rcases leaf with leaf | (⟨prime, leaf⟩ | (⟨prime, leaf⟩ | ⟨prime, leaf⟩))
    · let baseGeometry := OriginalNominalGeometry.canonicalMain
        (a := internal) (Z := Z) (step := step)
        ((source.block DE).literalRightCoordinates D.val) (2 * loss + cutoffExponent)
        (zero_lt_one.trans hZ) (by positivity)
      exact baseGeometry.atSecondPattern leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity
        leaf.1.block.left_positive leaf.1.block.right_positive
        (leaf.1.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ leaf.1.rowLabel)
    · let baseGeometry := OriginalNominalGeometry.canonicalPoolError
        (a := internal) pool .one prime ((source.block DE).literalRightCoordinates D.val)
        (2 * loss + cutoffExponent) (by positivity : 0 ≤ 2 * loss + cutoffExponent)
      exact baseGeometry.atSecondPattern leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity
        leaf.1.block.left_positive leaf.1.block.right_positive
        (leaf.1.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ leaf.1.rowLabel)
    · let baseGeometry := OriginalNominalGeometry.canonicalPoolError
        (a := internal) pool .six prime ((source.block DE).literalRightCoordinates D.val)
        (2 * loss + cutoffExponent) (by positivity : 0 ≤ 2 * loss + cutoffExponent)
      exact baseGeometry.atSecondPattern leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity
        leaf.1.block.left_positive leaf.1.block.right_positive
        (leaf.1.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ leaf.1.rowLabel)
    · let baseGeometry := OriginalNominalGeometry.canonicalPoolError
        (a := internal) pool .seven prime ((source.block DE).literalRightCoordinates D.val)
        (2 * loss + cutoffExponent) (by positivity : 0 ≤ 2 * loss + cutoffExponent)
      exact baseGeometry.atSecondPattern leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity
        leaf.1.block.left_positive leaf.1.block.right_positive
        (leaf.1.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ leaf.1.rowLabel)

def literalPrimitivePooledRootLength
    (j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization) : ℝ := by
  rcases j with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩
  all_goals
    rcases leaf with leaf | (⟨prime, leaf⟩ | (⟨prime, leaf⟩ | ⟨prime, leaf⟩))
  all_goals
    exact idealLogLength Z (secondSixthRootIdeal leaf.1.block.primes
      leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity).val

local notation "geometryAt" => literalPrimitivePooledGeometryAt
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (hstep := hstep)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (hcutoffPower := hcutoffPower)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hhi := hhi) (orders := orders)
  (originalBound := originalBound) (originalWindow := originalWindow)
  (hrows := hrows) (htime := htime) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)

local notation "rootLengthAt" => literalPrimitivePooledRootLength
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (hstep := hstep)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (hcutoffPower := hcutoffPower)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hhi := hhi) (orders := orders)
  (originalBound := originalBound) (originalWindow := originalWindow)
  (hrows := hrows) (htime := htime) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)

local notation "rawWidthAt" => fun j =>
  (geometryAt j).literalRowParameter (2 * loss + cutoffExponent) +
    (geometryAt j).literalSupportParameter (rootLengthAt j)
local notation "movingAt" => fun j =>
  (stages.supported.gated.originalNominalTagAt raw.originalAtlas j.val).movingLength Z +
    (stages.supported.gated.originalNominalTagAt raw.originalAtlas j.val).poolLength step

theorem literalPrimitivePooledKernelMass_coefficient
    (j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization) :
    (massCertificates j).coefficient =
      CanonicalLiteralPrimitiveMassCoefficient.kernelCoefficient K A σ ω ψ cap orders
        lo hi hlo δ₁ δ₂ δ mesh Z analyticHeight (rawWidthAt j) originalBound
        fixedFirstKernel fixedSecondKernel := by
  rcases j with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩
  all_goals
    rcases leaf with leaf | (⟨prime, leaf⟩ | (⟨prime, leaf⟩ | ⟨prime, leaf⟩)) <;> rfl

theorem literalPrimitivePooledIndexedWeight_cost
    (j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization) :
    (indexCertificates j).cost =
      CanonicalLiteralPrimitiveMassCoefficient.indexCoefficient K cap hi originalBound unitIndex
        Z error mesh internal.m
        (internal.n₁ + internal.n₂ + (data ξ).geometry.totalLength)
        (idealLogLength Z (firstPhysicalDivisorIdeal (A := A) j.val.2.1.val).val)
        (idealLogLength Z (firstActiveRadical j.val.1.val.1 j.val.1.val.2)) δ₁ δ₂ (movingAt j) := by
  rcases j with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩
  all_goals
    rcases leaf with leaf | (⟨prime, leaf⟩ | (⟨prime, leaf⟩ | ⟨prime, leaf⟩)) <;> rfl

/-- The main and residual columns divide the same original columns,
so every actual second common ideal obeys the original full window. -/
theorem literalPrimitivePooled_rawWidth_le
    (j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization) :
    rawWidthAt j ≤ a.m + a.q + columnBound + (2 * loss + cutoffExponent) := by
  have hn := (stages.supported.gated j.val.1 j.val.2.1).commonLabel_norm_le
    raw.originalAtlas raw.originalAtlas (Z ^ columnBound) hN hN j.val.2.2
  have hwidth : internal.m + internal.q = a.m + a.q := Q.fullSupportParameters_width a Z
  rcases j with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩
  · rcases leaf with leaf | (⟨prime, leaf⟩ | (⟨prime, leaf⟩ | ⟨prime, leaf⟩))
    · have hg := (geometryAt ⟨⟨DE, D, S, χ, .inl (.inl leaf)⟩, hj⟩).literalRawWidth_le_second_box
        hZ hstep.le (2 * loss + cutoffExponent) columnBound leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity rfl (by
          change (Ideal.absNorm (primePowerProduct leaf.1.block.primes
            leaf.1.block.leftMultiplicity).val : ℝ) ≤ Z ^ columnBound
          rw [leaf.1.block.common_left]
          exact hn.1)
      exact hg.trans_eq (by rw [hwidth])
    · have hg := (geometryAt ⟨⟨DE, D, S, χ, .inl (.inr (.inl ⟨prime, leaf⟩))⟩, hj⟩).literalRawWidth_le_second_box
        hZ hstep.le (2 * loss + cutoffExponent) columnBound leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity rfl (by
          change (Ideal.absNorm (primePowerProduct leaf.1.block.primes
            leaf.1.block.leftMultiplicity).val : ℝ) ≤ Z ^ columnBound
          rw [leaf.1.block.common_left]
          exact hn.1)
      exact hg.trans_eq (by rw [hwidth])
    · have hg := (geometryAt ⟨⟨DE, D, S, χ, .inl (.inr (.inr (.inl ⟨prime, leaf⟩)))⟩, hj⟩).literalRawWidth_le_second_box
        hZ hstep.le (2 * loss + cutoffExponent) columnBound leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity rfl (by
          change (Ideal.absNorm (primePowerProduct leaf.1.block.primes
            leaf.1.block.leftMultiplicity).val : ℝ) ≤ Z ^ columnBound
          rw [leaf.1.block.common_left]
          exact hn.1)
      exact hg.trans_eq (by rw [hwidth])
    · have hg := (geometryAt ⟨⟨DE, D, S, χ, .inl (.inr (.inr (.inr ⟨prime, leaf⟩)))⟩, hj⟩).literalRawWidth_le_second_box
        hZ hstep.le (2 * loss + cutoffExponent) columnBound leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity rfl (by
          change (Ideal.absNorm (primePowerProduct leaf.1.block.primes
            leaf.1.block.leftMultiplicity).val : ℝ) ≤ Z ^ columnBound
          rw [leaf.1.block.common_left]
          exact hn.1)
      exact hg.trans_eq (by rw [hwidth])
  · rcases leaf with leaf | (⟨prime, leaf⟩ | (⟨prime, leaf⟩ | ⟨prime, leaf⟩))
    · have hg := (geometryAt ⟨⟨DE, D, S, χ, .inr (.inl leaf)⟩, hj⟩).literalRawWidth_le_second_box
        hZ hstep.le (2 * loss + cutoffExponent) columnBound leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity rfl (by
          change (Ideal.absNorm (primePowerProduct leaf.1.block.primes
            leaf.1.block.leftMultiplicity).val : ℝ) ≤ Z ^ columnBound
          rw [leaf.1.block.common_left]
          exact hn.1)
      exact hg.trans_eq (by rw [hwidth])
    · have hg := (geometryAt ⟨⟨DE, D, S, χ, .inr (.inr (.inl ⟨prime, leaf⟩))⟩, hj⟩).literalRawWidth_le_second_box
        hZ hstep.le (2 * loss + cutoffExponent) columnBound leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity rfl (by
          change (Ideal.absNorm (primePowerProduct leaf.1.block.primes
            leaf.1.block.leftMultiplicity).val : ℝ) ≤ Z ^ columnBound
          rw [leaf.1.block.common_left]
          exact hn.1)
      exact hg.trans_eq (by rw [hwidth])
    · have hg := (geometryAt ⟨⟨DE, D, S, χ, .inr (.inr (.inr (.inl ⟨prime, leaf⟩)))⟩, hj⟩).literalRawWidth_le_second_box
        hZ hstep.le (2 * loss + cutoffExponent) columnBound leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity rfl (by
          change (Ideal.absNorm (primePowerProduct leaf.1.block.primes
            leaf.1.block.leftMultiplicity).val : ℝ) ≤ Z ^ columnBound
          rw [leaf.1.block.common_left]
          exact hn.1)
      exact hg.trans_eq (by rw [hwidth])
    · have hg := (geometryAt ⟨⟨DE, D, S, χ, .inr (.inr (.inr (.inr ⟨prime, leaf⟩)))⟩, hj⟩).literalRawWidth_le_second_box
        hZ hstep.le (2 * loss + cutoffExponent) columnBound leaf.1.block.primes
        leaf.1.block.leftMultiplicity leaf.1.block.rightMultiplicity rfl (by
          change (Ideal.absNorm (primePowerProduct leaf.1.block.primes
            leaf.1.block.leftMultiplicity).val : ℝ) ≤ Z ^ columnBound
          rw [leaf.1.block.common_left]
          exact hn.1)
      exact hg.trans_eq (by rw [hwidth])

/-- The original first lengths bound the exact tilt of every pool tag. -/
theorem literalPrimitivePooled_firstNumericWindows
    (j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization) :
    0 ≤ internal.m ∧
      internal.n₁ + internal.n₂ + (data ξ).geometry.totalLength ≤ lengthBound ∧
      idealLogLength Z (firstPhysicalDivisorIdeal (A := A) j.val.2.1.val).val ≤ columnBound ∧
      idealLogLength Z (firstActiveRadical j.val.1.val.1 j.val.1.val.2) ≤ columnBound := by
  have hm := Q.literalPrimitiveCommon_m_nonneg μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half j.val.1
  have hi := Q.literalPrimitiveFirstIdealLengths μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    columnBound hN j.val.1 j.val.2.1
  refine ⟨hm, ?_, hi.2.2.2, hi.2.2.1⟩
  simpa only [domain.total_length] using htotal

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledKernelMass_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledIndexedWeight_cost
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooled_rawWidth_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooled_firstNumericWindows
