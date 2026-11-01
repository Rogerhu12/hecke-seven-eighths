import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledMassWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveMassConstants
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledScalar
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PrimitivePooledFactoryFibres

/-!
# Uniform mass of the complete original amplified family

Every main and valuation 1/6/7 source retains its actual passive family.
The exact original tag scalar pays its moving power in the one amplified
arithmetic index. Physical fibres, passive labels and both divisor sums
are bounded from the original data, with all constants fixed first.
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

local notation "coefficientIdentity" => literalPrimitivePooledKernelMass_coefficient
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

local notation "costIdentity" => literalPrimitivePooledIndexedWeight_cost
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

local notation "sourceMass" => literalPrimitivePooled_kernelMass
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

local notation "outerIndex" => literalPrimitivePooled_outer_index
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

local notation "fibreBound" => literalPrimitivePooledFamily_index_fibre
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

local notation "widthWindow" => literalPrimitivePooled_rawWidth_le
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

local notation "firstWindows" => literalPrimitivePooled_firstNumericWindows
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

local notation "scalarBound" => literalPrimitivePooled_originalScalar_moving_index_le
  (Q := Q)
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (hi := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hhi := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (lo := lo) (orders := orders) (originalBound := originalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)
  (step := step) (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

local notation "arithmetic" => stages.supported.gated.arithmeticLabels raw.originalAtlas
  hcap exceptional normalization
local notation "tag" => stages.supported.gated.arithmeticTag raw.originalAtlas
  exceptional normalization
local notation "indices" => stages.supported.gated.arithmeticIndex raw.originalAtlas
  hcap exceptional normalization
local notation "localWeight" => fun j =>
  (arithmetic.localBranch tag j).indexWeight (arithmetic.localIndex tag j)
local notation "rowExponent" => literalPrimitivePoolRowExponent
  (lengthBound := lengthBound) (columnBound := columnBound)
  (loss := loss) (cutoffExponent := cutoffExponent)
local notation "fiberCap" => (CanonicalLiteralPrimitivePooledScalar.fiberCap rowExponent step : ℝ)
local notation "amplifiedWeight" => amplifiedIndexWeight pool rowExponent columnBound
  (arithmetic.mainCarrier tag) (arithmetic.errorCarrier tag)

open CanonicalLiteralPrimitiveMassConstants

variable (profileDegree heightDegree : ℕ)
variable (widthMax massLoss heightConstant : ℝ)
variable (hwidthMax : 0 ≤ widthMax) (hmassLoss : 0 < massLoss)
variable (heps : 0 < eps) (hepsSmall : eps < step / 3)

local notation "lengthBox" => max lengthBound columnBound
local notation "widthBox" => widthMax + columnBound + (2 * loss + cutoffExponent)
local notation "tilt" => CanonicalLiteralCombinedMassCoefficient.mellinTilt lengthBox massLoss
local notation "chosenContour" => contour K A σ ω ψ cap profileDegree heightDegree
  hi lo hi hlo hhi (zero_le_one.trans hhi) lengthBox massLoss
  (le_max_of_le_left hlengthBound) hmassLoss orders mesh heightConstant widthBox
  (by positivity) unitIndex fixedFirstKernel fixedSecondKernel (by positivity) (by positivity) (by positivity)
local notation "profileConstant" => coefficient K A σ ω ψ cap profileDegree heightDegree
  hi lo hi hlo hhi (zero_le_one.trans hhi) lengthBox massLoss
  (le_max_of_le_left hlengthBound) hmassLoss orders mesh heightConstant widthBox
  (by positivity) unitIndex fixedFirstKernel fixedSecondKernel (by positivity) (by positivity) (by positivity)
local notation "profileConstantPos" => coefficient_pos K A σ ω ψ cap profileDegree heightDegree
  hi lo hi hlo hhi (zero_le_one.trans hhi) lengthBox massLoss
  (le_max_of_le_left hlengthBound) hmassLoss orders mesh heightConstant widthBox
  (by positivity) unitIndex fixedFirstKernel fixedSecondKernel (by positivity) (by positivity) (by positivity)
local notation "numericBound" => coefficient_bound K A σ ω ψ cap profileDegree heightDegree
  hi lo hi hlo hhi (zero_le_one.trans hhi) lengthBox massLoss
  (le_max_of_le_left hlengthBound) hmassLoss orders mesh heightConstant widthBox
  (by positivity) unitIndex fixedFirstKernel fixedSecondKernel (by positivity) (by positivity) (by positivity)
local notation "degree" => CanonicalLiteralPassiveMassCoefficient.degree
  cap profileDegree 0 0 0 heightDegree
local notation "passiveConstant" => PrimitivePassiveFactoryCard.allTagsConstant K cap columnBound
  (step / 3) (massLoss / 8) hcolumnBound (by positivity) (by positivity)
local notation "physicalConstant" => kernelSourceFibreConstant K cap
  (Fintype.card (PUnit.{1} × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))))
  0 0 (columnBound + 7 * (step / 3)) (massLoss / 2) (by positivity) (by positivity)
local notation "harmonicConstant" => pooledHarmonicConstant K A cap columnBound massLoss
  hcolumnBound hmassLoss (step / 3) eps rowExponent columnBound
  (by positivity) heps hepsSmall (by dsimp [literalPrimitivePoolRowExponent]; positivity) hcolumnBound
local notation "harmonicThreshold" => pooledThreshold K A cap columnBound massLoss
  hcolumnBound hmassLoss (step / 3) eps rowExponent columnBound
  (by positivity) heps hepsSmall (by dsimp [literalPrimitivePoolRowExponent]; positivity) hcolumnBound

/-- The single original pool average and its density are paid in the
proved amplified arithmetic mass. All remaining factors are fixed. -/
def literalPrimitivePooledMassConstant : ℝ :=
  profileConstant * fiberCap * (passiveConstant * physicalConstant) * harmonicConstant

/-- This is selected before the actual prime pool and every source. -/
def literalPrimitivePooledMassThreshold : ℝ := harmonicThreshold

local notation "totalConstant" => literalPrimitivePooledMassConstant
  (K := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (μv := μv) (ν := ν)
  (cap := cap) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (loss := loss) (cutoffExponent := cutoffExponent) (hloss := hloss)
  (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
  (mesh := mesh) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi) (orders := orders)
  (profileDegree := profileDegree) (heightDegree := heightDegree)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (widthMax := widthMax) (massLoss := massLoss) (heightConstant := heightConstant)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (hwidthMax := hwidthMax) (hmassLoss := hmassLoss) (eps := eps)
  (heps := heps) (hepsSmall := hepsSmall)
local notation "totalThreshold" => literalPrimitivePooledMassThreshold
  (K := K) (A := A) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (massLoss := massLoss) (hmassLoss := hmassLoss) (eps := eps)
  (heps := heps) (hepsSmall := hepsSmall)

theorem literalPrimitivePooledMassConstant_pos : 0 < totalConstant := by
  have hp := profileConstantPos
  have hf : 0 < fiberCap := by
    have hn : (0 : ℕ) < CanonicalLiteralPrimitivePooledScalar.fiberCap rowExponent step :=
      lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    exact_mod_cast hn
  have hc := PrimitivePassiveFactoryCard.allTagsConstant_pos K cap columnBound
    (step / 3) (massLoss / 8) hcolumnBound (by positivity) (by positivity)
  have hr := kernelSourceFibreConstant_pos K cap
    (Fintype.card (PUnit.{1} × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))))
    0 0 (columnBound + 7 * (step / 3)) (massLoss / 2) (by positivity) (by positivity)
  have hh := pooledHarmonicConstant_pos K A cap columnBound massLoss
    hcolumnBound hmassLoss (step / 3) eps rowExponent columnBound
    (by positivity) heps hepsSmall (by dsimp [literalPrimitivePoolRowExponent]; positivity) hcolumnBound
  exact mul_pos (mul_pos (mul_pos hp hf) (mul_pos hc hr)) hh

theorem literalPrimitivePooledMassThreshold_one_lt : 1 < totalThreshold :=
  pooledThreshold_one_lt K A cap columnBound massLoss
    hcolumnBound hmassLoss (step / 3) eps rowExponent columnBound
    (by positivity) heps hepsSmall (by dsimp [literalPrimitivePoolRowExponent]; positivity) hcolumnBound

variable (hwidth : a.m + a.q ≤ widthMax)
variable (T control : ℝ) (hT : 0 ≤ T) (hcontrol : 1 + T ≤ control)
variable (hprofile : originalBound ≤ control ^ profileDegree)
variable (hheight : analyticHeight ≤ heightConstant * (1 + Real.log Z) * (1 + T) ^ heightDegree)
variable (htilt₁ : δ₁ = tilt) (htilt₂ : δ₂ = tilt) (hcontour : δ = chosenContour)

include hwidth hT hcontrol hprofile hheight htilt₁ htilt₂ hcontour in
/-- The tag power is preserved for the original pool index. Every
other coefficient is bounded from the actual original windows. -/
theorem literalPrimitivePooled_coefficient_product
    (j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization) :
    (massCertificates j).coefficient * (indexCertificates j).cost ≤
      profileConstant * control ^ degree * Z ^ (massLoss + 5 * error / 3 + mesh) *
        Z ^ (movingAt j) := by
  have hw := widthWindow j
  have hn := firstWindows j
  have hbox : rawWidthAt j ≤ widthBox := by linarith
  have h := numericBound Z T (rawWidthAt j) analyticHeight control originalBound error
    internal.m (internal.n₁ + internal.n₂ + (data ξ).geometry.totalLength)
    (idealLogLength Z (firstPhysicalDivisorIdeal (A := A) j.val.2.1.val).val)
    (idealLogLength Z (firstActiveRadical j.val.1.val.1 j.val.1.val.2)) (movingAt j)
    hZ.le hT hbox hheight hcontrol horiginalBound hprofile hn.1
    (hn.2.1.trans (le_max_left _ _))
    (hn.2.2.1.trans (le_max_right _ _)) (hn.2.2.2.trans (le_max_right _ _))
  rw [coefficientIdentity j, costIdentity j]
  simpa only [htilt₁, htilt₂, hcontour] using h

local notation "productBound" => literalPrimitivePooled_coefficient_product
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
  (profileDegree := profileDegree) (heightDegree := heightDegree)
  (widthMax := widthMax) (massLoss := massLoss) (heightConstant := heightConstant)
  (hwidthMax := hwidthMax) (hmassLoss := hmassLoss)
  (hwidth := hwidth) (T := T) (control := control)
  (hT := hT) (hcontrol := hcontrol) (hprofile := hprofile) (hheight := hheight)
  (htilt₁ := htilt₁) (htilt₂ := htilt₂) (hcontour := hcontour)

include hwidth hT hcontrol hprofile hheight htilt₁ htilt₂ hcontour in
/-- The main and all 1/6/7 error sources are summed on their actual
amplified index. The original pool density and prime average occur once. -/
theorem literalPrimitivePooled_global_kernelMass
    (hlarge : totalThreshold ≤ Z)
    (analytic : ∀ j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization,
      (factories j).Input) :
    (∀ b : (completeFamily analytic).active Finset.univ,
      IsFiniteMeasure ((completeFamily analytic).kernel Finset.univ completeMeasure
        (internal.m + internal.q) b)) ∧
    (∑ b : (completeFamily analytic).active Finset.univ,
      ((completeFamily analytic).kernel Finset.univ completeMeasure
        (internal.m + internal.q) b).real Set.univ) ≤
      totalConstant * control ^ degree * Z ^ (9 * massLoss / 4 + eps + 5 * error / 3 + mesh) := by
  have hm := sourceMass analytic
  refine ⟨hm.1, ?_⟩
  let common := profileConstant * control ^ degree * Z ^ (massLoss + 5 * error / 3 + mesh)
  have hcontrol0 : 0 ≤ control := by linarith
  have hcommon : 0 ≤ common := by
    have hp := profileConstantPos.le
    dsimp only [common]
    positivity
  have hM : 0 ≤ rowExponent := by dsimp [literalPrimitivePoolRowExponent]; positivity
  have hamp := amplifiedIndexWeight_nonneg pool rowExponent columnBound
    (arithmetic.mainCarrier tag) (arithmetic.errorCarrier tag) (zero_lt_one.trans hZ).le
    pool.exponent_pos hM hdensity.le
  have hpoint (j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization)
      (b : ((factories j).family (analytic j)).active Finset.univ) :
      stages.supported.gated.parentOuterScalar raw.originalAtlas normalization j.val *
        ((massCertificates j).coefficient *
          (((stages.supported.gated.unscaledParentLeaf raw.originalAtlas exceptional j.val).weight *
              (sourceCertificates j).frozen) *
            ((factories j).family (analytic j)).weight Finset.univ (internal.m + internal.q) b)) ≤
      (common * fiberCap) * amplifiedWeight (indices j) := by
    have hc : 0 ≤ (massCertificates j).coefficient := by
      rw [coefficientIdentity j]
      exact CanonicalLiteralPrimitiveMassCoefficient.kernelCoefficient_nonneg
        K A σ ω ψ cap orders lo hi hlo hhi δ₁ δ₂ δ mesh Z analyticHeight
        (rawWidthAt j) originalBound fixedFirstKernel fixedSecondKernel
        (zero_lt_one.trans hZ) horiginalBound (by positivity) (by positivity)
    have hs : 0 ≤ stages.supported.gated.originalScalarAt raw.originalAtlas j.val := by
      rcases j with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩
      · change 0 ≤ (source.fiber : ℝ) *
          ((4 / ((source.pools DE D).divisorPools.leftData S).density) *
            ((source.pools DE D).divisorPools.leftData S).tagWeight _ * (_ : ℕ)) / 2
        exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg (div_nonneg (by norm_num)
            ((source.pools DE D).divisorPools.leftData S).density_pos.le)
            (((source.pools DE D).divisorPools.leftData S).tagWeight_nonneg _))
            (Nat.cast_nonneg _))) (by norm_num)
      · change 0 ≤ (source.fiber : ℝ) *
          ((4 / ((source.pools DE D).divisorPools.rightData S).density) *
            ((source.pools DE D).divisorPools.rightData S).tagWeight _ * (_ : ℕ)) / 2
        exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg (div_nonneg (by norm_num)
            ((source.pools DE D).divisorPools.rightData S).density_pos.le)
            (((source.pools DE D).divisorPools.rightData S).tagWeight_nonneg _))
            (Nat.cast_nonneg _))) (by norm_num)
    have hp := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (productBound j) hs)
      ((arithmetic.localBranch tag j).indexWeight_nonneg (arithmetic.localIndex tag j))
    have hi := mul_le_mul_of_nonneg_left (outerIndex j (analytic j) b) hc
    calc
      _ = (massCertificates j).coefficient *
        (stages.supported.gated.parentOuterScalar raw.originalAtlas normalization j.val *
          (((stages.supported.gated.unscaledParentLeaf raw.originalAtlas exceptional j.val).weight *
              (sourceCertificates j).frozen) *
            ((factories j).family (analytic j)).weight Finset.univ (internal.m + internal.q) b)) := by ring
      _ ≤ (massCertificates j).coefficient *
          (stages.supported.gated.originalScalarAt raw.originalAtlas j.val *
            ((indexCertificates j).cost * localWeight j)) := hi
      _ = (stages.supported.gated.originalScalarAt raw.originalAtlas j.val *
          ((massCertificates j).coefficient * (indexCertificates j).cost)) * localWeight j := by ring
      _ ≤ (stages.supported.gated.originalScalarAt raw.originalAtlas j.val *
          (common * Z ^ movingAt j)) * localWeight j := hp
      _ = common * (stages.supported.gated.originalScalarAt raw.originalAtlas j.val *
          Z ^ movingAt j * localWeight j) := by ring
      _ ≤ common * (fiberCap * amplifiedWeight (indices j)) :=
        mul_le_mul_of_nonneg_left (scalarBound j) hcommon
      _ = _ := by ring
  have hsum :
      (∑ b : (completeFamily analytic).active Finset.univ, amplifiedWeight (indices b.val.1)) =
      ∑ j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization,
        ∑ _b : ((factories j).family (analytic j)).active Finset.univ,
          amplifiedWeight (indices j) := by
    simpa only [Finset.univ_sigma_univ, Finset.sum_coe_sort] using
      ActualNormalizedPairFamily.sum_sigmaCombine_active
        (fun j => (factories j).family (analytic j)) Finset.univ (fun _ => Finset.univ)
        (fun b => amplifiedWeight (indices b.val.1))
  have harithmetic := stages.arithmeticCarriers_admissible raw.originalAtlas hcap
    normalization exceptional columnBound 1 (by simp) (fun _ _ => one_dvd _) hN
  have hcard := fibreBound massLoss hmassLoss analytic
  have hpassive := (PrimitivePassiveFactoryCard.allTagsConstant_pos K cap columnBound
    (step / 3) (massLoss / 8) hcolumnBound (by positivity) (by positivity)).le
  have hphysical := (kernelSourceFibreConstant_pos K cap
    (Fintype.card (PUnit.{1} × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))))
    0 0 (columnBound + 7 * (step / 3)) (massLoss / 2) (by positivity) (by positivity)).le
  have hcount := sum_weighted_fibres_le
    (fun b : (completeFamily analytic).active Finset.univ => indices b.val.1)
    amplifiedWeight hamp ((passiveConstant * physicalConstant) * Z ^ (massLoss / 4)) hcard
  have hh := pooled_harmonic_sum K A cap columnBound massLoss hcolumnBound hmassLoss
    (step / 3) eps rowExponent columnBound (by positivity) heps hepsSmall hM hcolumnBound
    Z hlarge bad pool (arithmetic.mainCarrier tag) harithmetic.1
    (arithmetic.errorCarrier tag) (fun n _ p _ => harithmetic.2 n p)
  have hindex := hcount.trans (mul_le_mul_of_nonneg_left hh (by positivity))
  have hfixed : 0 ≤ common * fiberCap := mul_nonneg hcommon (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization,
        stages.supported.gated.parentOuterScalar raw.originalAtlas normalization j.val *
          ((massCertificates j).coefficient *
            ∑ b : ((factories j).family (analytic j)).active Finset.univ,
              ((stages.supported.gated.unscaledParentLeaf raw.originalAtlas exceptional j.val).weight *
                (sourceCertificates j).frozen) *
                  ((factories j).family (analytic j)).weight Finset.univ (internal.m + internal.q) b) := hm.2
    _ ≤ ∑ j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization,
        ∑ _b : ((factories j).family (analytic j)).active Finset.univ,
          (common * fiberCap) * amplifiedWeight (indices j) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Finset.mul_sum]
      exact Finset.sum_le_sum (fun b _ => hpoint j b)
    _ = (common * fiberCap) * ∑ b : (completeFamily analytic).active Finset.univ,
        amplifiedWeight (indices b.val.1) := by
      rw [hsum]
      simp only [Finset.mul_sum]
    _ ≤ (common * fiberCap) *
        (((passiveConstant * physicalConstant) * Z ^ (massLoss / 4)) *
          (harmonicConstant * Z ^ (massLoss + eps))) := mul_le_mul_of_nonneg_left hindex hfixed
    _ = _ := by
      dsimp only [common, literalPrimitivePooledMassConstant]
      rw [show 9 * massLoss / 4 + eps + 5 * error / 3 + mesh =
        (massLoss + 5 * error / 3 + mesh) + (massLoss / 4) + (massLoss + eps) by ring,
        Real.rpow_add (zero_lt_one.trans hZ)
          ((massLoss + 5 * error / 3 + mesh) + (massLoss / 4)) (massLoss + eps),
        Real.rpow_add (zero_lt_one.trans hZ)
          (massLoss + 5 * error / 3 + mesh) (massLoss / 4)]
      ring

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledMassConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledMassThreshold_one_lt
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooled_coefficient_product
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooled_global_kernelMass
