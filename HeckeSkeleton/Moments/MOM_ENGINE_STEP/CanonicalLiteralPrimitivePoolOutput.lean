import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePoolSourceIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolPassiveOutput

/-!
# Complete output facts for the original pool factories

Each certificate refers to the same actual curried factory and the
measure of its original source integral. The internally repartitioned
row/support width is transported to the original parent parameters;
the chosen children and their complete moving recipes are unchanged.
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
variable (hN : ∀ i ∈ (firstSource).columns,
  (Ideal.absNorm ((firstSource).ideal i).val : ℝ) ≤ Z ^ columnBound)
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

local notation "leftFactory" => literalPrimitiveLeftPoolFactory
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

local notation "rightFactory" => literalPrimitiveRightPoolFactory
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

local notation "leftSourceIntegral" => literalPrimitiveLeftPoolSourceIntegral
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

local notation "rightSourceIntegral" => literalPrimitiveRightPoolSourceIntegral
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

section LeftValuation

variable (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
variable (S : divisorPool ((source).pools DE D).rightData.columns
  (fun j => (((source).pools DE D).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle) (valuation : AmplifierValuation) (prime : pool.primes)

local notation "baseGeometry" => OriginalNominalGeometry.canonicalPoolError
  (a := internal) pool valuation prime (((source).block DE).literalLeftCoordinates D.val)
  (2 * loss + cutoffExponent) (by positivity : 0 ≤ 2 * loss + cutoffExponent)
local notation "rowWindow" => (((source).pools DE D).divisorPools.leftData S).literalPoolRows internal
  (((source).block DE).literalLeftCoordinates D.val) (2 * loss + cutoffExponent)
  (by positivity) hstep (leftRows DE D S) valuation prime
local notation "poolStage" => (((source).pools DE D).divisorPools.leftData S).literalValuationStage
  (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  (μv := μv) (hDiff := hDiff) (ν := ν)
  (((source).pools DE D).leftDivisorCoefficient S χ) P internal (((source).block DE).literalLeftCoordinates D.val)
  (2 * loss + cutoffExponent) (by positivity) hstep (leftRows DE D S)
  δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ valuation prime
local notation "cover" => ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual prime valuation.multiplicity)
local notation "predicate" => (poolStage).supported.gated.literalHybridPredicates cover cover P R
  (CanonicalLiteralActualCharacters.amplifiedPhases C
    (((source).block DE).literalLeftFixed D.val)
    (CanonicalLiteralFirstPhase.leftElement C ((source).block DE).primes
      ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
    (((source).block DE).literalLeftFixed_generates C D.val) prime.val valuation.multiplicity)
  Q.moving Q.correction (data ξ).theta

/-- Each valuation uses its own actual residual source, without recoding its prime. -/
def literalPrimitiveLeftPoolOutput
    (leaf : (poolStage).supported.gated.CoveredLeafKey cover cover)
    (hS : Squarefree S.val)
    (hlive : ((poolStage).supported.gated.fiberCoveredLeaf cover cover predicate
      ((source).charts DE D).kernel (fun i => ((source).charts DE D).leftPoint i.val) leaf).Live) :
    (leftFactory DE D S χ valuation prime leaf hS hlive).Output P R (data ξ) a step
      Set.univ (Set.Icc (0 : ℝ) hi) orders
      (leftSourceIntegral DE D S χ valuation prime leaf hS hlive).measure := by
  let v := leaf.1
  let geometry := (baseGeometry).atSecondPattern v.block.primes
    v.block.leftMultiplicity v.block.rightMultiplicity v.block.left_positive v.block.right_positive
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
  have hprofile := ActualGaussStage.canonicalSector_fiberLeaf_rowProfile_one
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (μv := μv) (hDiff := hDiff) (ν := ν)
    P δ₂ hδ₂ hδ₂half ((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ))
    (baseGeometry).retainedScale Z (baseGeometry).enlargement
    (baseGeometry).retainedScale_pos (zero_lt_one.trans hZ) cutoff₂ hcutoff₂ rowWindow
    0 0 (fun _ _ => (PUnit.unit : PUnit.{1})) (fun _ _ i => Fin.elim0 i)
    cover cover predicate ((source).charts DE D).kernel (fun i => ((source).charts DE D).leftPoint i.val) leaf hlive
  have hfirstIdeal : geometry.ideals.first.val = DE.val.1 :=
    ((source).block DE).literalLeftCoordinates_first D.val
  have hoppositeIdeal : geometry.ideals.opposite.val = DE.val.2 :=
    ((source).block DE).literalLeftCoordinates_opposite D.val
  have hremoved : idealLogLength Z (powerIdeal prime.val valuation.multiplicity).val =
      geometry.skeleton.w := by
    change idealLogLength Z (prime.val.val.asIdeal ^ valuation.multiplicity) =
      (valuation.multiplicity : ℝ) * idealLogLength Z prime.val.val.asIdeal
    exact idealLogLength_pow Z prime.val.val.asIdeal valuation.multiplicity
  have hactive : ∀ i ∈ ((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ)).columns,
      ((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ)).coefficient i ≠ 0 →
      A.exteriorNorm (((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ)).ideal i) ≤
        Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + loss) := by
    intro i _ hci
    change A.exteriorNorm (((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ)).ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z -
        idealLogLength Z geometry.ideals.first.val - geometry.skeleton.w + loss)
    rw [hfirstIdeal, ← hremoved]
    exact literalPrimitiveLeftPool_active_norm
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
      (pool := pool) (hdensity := hdensity) DE D S χ prime.val valuation.multiplicity i hci
  let output := literalLeftPoolPassiveOutput
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂)
    (b := (source).block DE) (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1)
    (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ)
    (q := prime) (n := valuation.multiplicity) (valuation := valuation) (valuation_eq := rfl)
    (hDiff := hDiff) (hroot := hroot) (hemb := hemb)
    (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (retainedScale := (baseGeometry).retainedScale) (g := (baseGeometry).enlargement)
    (hscale := (baseGeometry).retainedScale_pos) (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
    (Θ := PUnit.{1}) (dimension := 0) (width := 0)
    (reference := reference) (href := by
      simpa only [Q.literalPrimitiveFirstSource_pairedRows] using href)
    (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi) (orders := orders)
    (originalBound := originalBound) (horiginalBound := horiginalBound)
    (originalWindow := originalWindow) (hreference := hrows reference href)
    (htime := htime) (hprime := hprime)
    (domain := domain.withSupportLength (Q.fullSupportLength Z))
    (step := step) (error := error) (mesh := mesh) (hstep := hstep)
    (herror := herror) (hmesh := hmesh) (hfit := hfit) (hprimeOrders := hprimeOrders)
    (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
    (hone := hone) (hbackground := hbackground) (hslot := hslot)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (v := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
    (firstFixed := ((source).block DE).literalLeftFixed D.val) (hfirst := ((source).block DE).literalLeftFixed_generates C D.val) (j := leaf.2)
    (hS := hS) (hlive := hlive) (profileBound := 1) (hprofileBound := by norm_num)
    (hprofile := hprofile) (geometry := geometry) (hretained := rfl) (henlargement := rfl)
    (hsecond := rfl) (hopposite := rfl) (hunit := rfl) (hnonunit := rfl)
    (direct := by intro h; change OriginalNominalTag.error valuation prime.val.val = .direct at h; cases h) (columnLoss := loss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hloss) (hcutoffExponent := hcutoffExponent)
    (hsmall := hsmall) (hcutoffPower := hcutoffPower₂) (hactiveColumns := hactive)
    (oldSupport := literalPrimitiveFirstSource_oldSupport (Q := Q) (a := a) (Z := Z) (hZ := hZ))
    (firstIdeal := hfirstIdeal) (oppositeIdeal := hoppositeIdeal)
    (physicalDivisor := rfl) (branchTag := rfl) (hexceptional := rfl)
  exact output.withParentParameters (Q.fullSupportParameters_width a Z) rfl

end LeftValuation

section RightValuation

variable (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
variable (S : divisorPool ((source).pools DE D).rightData.columns
  (fun j => (((source).pools DE D).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle) (valuation : AmplifierValuation) (prime : pool.primes)

local notation "baseGeometry" => OriginalNominalGeometry.canonicalPoolError
  (a := internal) pool valuation prime (((source).block DE).literalRightCoordinates D.val)
  (2 * loss + cutoffExponent) (by positivity : 0 ≤ 2 * loss + cutoffExponent)
local notation "rowWindow" => (((source).pools DE D).divisorPools.rightData S).literalPoolRows internal
  (((source).block DE).literalRightCoordinates D.val) (2 * loss + cutoffExponent)
  (by positivity) hstep (rightRows DE D S) valuation prime
local notation "poolStage" => (((source).pools DE D).divisorPools.rightData S).literalValuationStage
  (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  (μv := μv) (hDiff := hDiff) (ν := ν)
  (((source).pools DE D).rightDivisorCoefficient S χ) P internal (((source).block DE).literalRightCoordinates D.val)
  (2 * loss + cutoffExponent) (by positivity) hstep (rightRows DE D S)
  δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ valuation prime
local notation "cover" => ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual prime valuation.multiplicity)
local notation "predicate" => (poolStage).supported.gated.literalHybridPredicates cover cover P R
  (CanonicalLiteralActualCharacters.amplifiedPhases C
    (((source).block DE).literalRightFixed D.val)
    (CanonicalLiteralFirstPhase.rightElement C ((source).block DE).primes
      ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
    (((source).block DE).literalRightFixed_generates C D.val) prime.val valuation.multiplicity)
  Q.moving Q.correction (data ξ).theta

/-- Each valuation uses its own actual residual source, without recoding its prime. -/
def literalPrimitiveRightPoolOutput
    (leaf : (poolStage).supported.gated.CoveredLeafKey cover cover)
    (hS : Squarefree S.val)
    (hlive : ((poolStage).supported.gated.fiberCoveredLeaf cover cover predicate
      ((source).charts DE D).kernel (fun i => -((source).charts DE D).rightPoint i.val) leaf).Live) :
    (rightFactory DE D S χ valuation prime leaf hS hlive).Output P R (data ξ) a step
      Set.univ (Set.Icc (0 : ℝ) hi) orders
      (rightSourceIntegral DE D S χ valuation prime leaf hS hlive).measure := by
  let v := leaf.1
  let geometry := (baseGeometry).atSecondPattern v.block.primes
    v.block.leftMultiplicity v.block.rightMultiplicity v.block.left_positive v.block.right_positive
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
  have hprofile := ActualGaussStage.canonicalSector_fiberLeaf_rowProfile_one
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (μv := μv) (hDiff := hDiff) (ν := ν)
    P δ₂ hδ₂ hδ₂half ((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ))
    (baseGeometry).retainedScale Z (baseGeometry).enlargement
    (baseGeometry).retainedScale_pos (zero_lt_one.trans hZ) cutoff₂ hcutoff₂ rowWindow
    0 0 (fun _ _ => (PUnit.unit : PUnit.{1})) (fun _ _ i => Fin.elim0 i)
    cover cover predicate ((source).charts DE D).kernel (fun i => -((source).charts DE D).rightPoint i.val) leaf hlive
  have hfirstIdeal : geometry.ideals.first.val = DE.val.2 :=
    ((source).block DE).literalRightCoordinates_first D.val
  have hoppositeIdeal : geometry.ideals.opposite.val = DE.val.1 :=
    ((source).block DE).literalRightCoordinates_opposite D.val
  have hremoved : idealLogLength Z (powerIdeal prime.val valuation.multiplicity).val =
      geometry.skeleton.w := by
    change idealLogLength Z (prime.val.val.asIdeal ^ valuation.multiplicity) =
      (valuation.multiplicity : ℝ) * idealLogLength Z prime.val.val.asIdeal
    exact idealLogLength_pow Z prime.val.val.asIdeal valuation.multiplicity
  have hactive : ∀ i ∈ ((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ)).columns,
      ((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ)).coefficient i ≠ 0 →
      A.exteriorNorm (((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ)).ideal i) ≤
        Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + loss) := by
    intro i _ hci
    change A.exteriorNorm (((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ)).ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z -
        idealLogLength Z geometry.ideals.first.val - geometry.skeleton.w + loss)
    rw [hfirstIdeal, ← hremoved]
    exact literalPrimitiveRightPool_active_norm
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
      (pool := pool) (hdensity := hdensity) DE D S χ prime.val valuation.multiplicity i hci
  let output := literalRightPoolPassiveOutput
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂)
    (b := (source).block DE) (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1)
    (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ)
    (q := prime) (n := valuation.multiplicity) (valuation := valuation) (valuation_eq := rfl)
    (hDiff := hDiff) (hroot := hroot) (hemb := hemb)
    (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (retainedScale := (baseGeometry).retainedScale) (g := (baseGeometry).enlargement)
    (hscale := (baseGeometry).retainedScale_pos) (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
    (Θ := PUnit.{1}) (dimension := 0) (width := 0)
    (reference := reference) (href := by
      simpa only [Q.literalPrimitiveFirstSource_pairedRows] using href)
    (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi) (orders := orders)
    (originalBound := originalBound) (horiginalBound := horiginalBound)
    (originalWindow := originalWindow) (hreference := hrows reference href)
    (htime := htime) (hprime := hprime)
    (domain := domain.withSupportLength (Q.fullSupportLength Z))
    (step := step) (error := error) (mesh := mesh) (hstep := hstep)
    (herror := herror) (hmesh := hmesh) (hfit := hfit) (hprimeOrders := hprimeOrders)
    (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
    (hone := hone) (hbackground := hbackground) (hslot := hslot)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (v := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
    (firstFixed := ((source).block DE).literalRightFixed D.val) (hfirst := ((source).block DE).literalRightFixed_generates C D.val) (j := leaf.2)
    (hS := hS) (hlive := hlive) (profileBound := 1) (hprofileBound := by norm_num)
    (hprofile := hprofile) (geometry := geometry) (hretained := rfl) (henlargement := rfl)
    (hsecond := rfl) (hopposite := rfl) (hunit := rfl) (hnonunit := rfl)
    (direct := by intro h; change OriginalNominalTag.error valuation prime.val.val = .direct at h; cases h) (columnLoss := loss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hloss) (hcutoffExponent := hcutoffExponent)
    (hsmall := hsmall) (hcutoffPower := hcutoffPower₂) (hactiveColumns := hactive)
    (oldSupport := literalPrimitiveFirstSource_oldSupport (Q := Q) (a := a) (Z := Z) (hZ := hZ))
    (firstIdeal := hfirstIdeal) (oppositeIdeal := hoppositeIdeal)
    (physicalDivisor := rfl) (branchTag := rfl) (hexceptional := rfl)
  exact output.withParentParameters (Q.fullSupportParameters_width a Z) rfl

end RightValuation

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftPoolOutput
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightPoolOutput
