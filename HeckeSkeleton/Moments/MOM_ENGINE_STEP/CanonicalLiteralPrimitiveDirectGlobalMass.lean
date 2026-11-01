import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectMassWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveMassConstants
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PrimitiveDirectFactoryFibres

/-!
# Uniform mass of the actual complete direct family

The source, normalization, passive labels, two kernels and chosen
children are the original computed objects.  The numerical coefficient,
physical and passive fibres, and harmonic index sum are all proved from
the original inputs inside this theorem.
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

variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable (cap : ℕ) (loss cutoffExponent : ℝ)
variable (hloss : 0 ≤ loss) (hcutoffExponent : 0 ≤ cutoffExponent)
variable (step error mesh : ℝ) (hstep : 0 < step) (herror : 0 ≤ error) (hmesh : 0 ≤ mesh)
variable (hfit : (data ξ).geometry.fitsMesh mesh)
variable (hsmall : 2 * (2 * loss + cutoffExponent) ≤ step)
variable (hslotsZero : (data ξ).geometry.slotCount = 0)
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

local notation "stages" => Q.literalPrimitiveDirectStages
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (step := step) (hstep := hstep)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

local notation "exceptional" => Q.literalPrimitiveDirectPredicates
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (step := step) (hstep := hstep)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

local notation "normalization" => Q.literalPrimitiveFirstNormalization μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half





local notation "factories" => literalPrimitiveDirectFactory
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)

/-- The original left direct case constructs its own passive family. -/
variable (hδsum : δ₁ + δ₂ ≤ 1 / 2)

local notation "sourceCertificates" => literalPrimitiveDirectSourceIntegral
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)

local notation "completeFamily" => literalPrimitiveDirectFamily
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)

local notation "completeMeasure" => literalPrimitiveDirectMeasure
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)





variable (herrorPos : 0 < error)
variable (hannulusThreshold : OriginalPairAllowanceProduction.annulusThreshold hi error ≤ Z)
variable (hscaleThreshold : hi ^ (2 * cap) ≤ Z ^ error)
variable (hpaidError : 2 * loss + cutoffExponent ≤ error)

local notation "massCertificates" => literalPrimitiveDirectKernelMass
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (hδsum := hδsum)

local notation "indexCertificates" => literalPrimitiveDirectIndexedWeight
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
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

local notation "geometryAt" => literalPrimitiveDirectGeometryAt
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (hstep := hstep)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (hcutoffPower := hcutoffPower)
  (lo := lo) (hi := hi) (hhi := hhi) (orders := orders)
  (originalBound := originalBound) (originalWindow := originalWindow)
  (hrows := hrows) (htime := htime) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)

local notation "rootLengthAt" => literalPrimitiveDirectRootLength
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (hstep := hstep)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (hcutoffPower := hcutoffPower)
  (lo := lo) (hi := hi) (hhi := hhi) (orders := orders)
  (originalBound := originalBound) (originalWindow := originalWindow)
  (hrows := hrows) (htime := htime) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)


local notation "rawWidthAt" => fun j =>
  (geometryAt j).literalRowParameter (2 * loss + cutoffExponent) +
    (geometryAt j).literalSupportParameter (rootLengthAt j)

local notation "coefficientIdentity" => literalPrimitiveDirectKernelMass_coefficient
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (hδsum := hδsum)

local notation "costIdentity" => literalPrimitiveDirectIndexedWeight_cost
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (hδsum := hδsum) (herrorPos := herrorPos)
  (hannulusThreshold := hannulusThreshold) (hscaleThreshold := hscaleThreshold)
  (hpaidError := hpaidError)

local notation "sourceMass" => literalPrimitiveDirect_kernelMass
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (hδsum := hδsum)

local notation "outerIndex" => literalPrimitiveDirect_outer_index
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (hδsum := hδsum) (herrorPos := herrorPos)
  (hannulusThreshold := hannulusThreshold) (hscaleThreshold := hscaleThreshold)
  (hpaidError := hpaidError)

local notation "fibreBound" => literalPrimitiveDirectFamily_index_fibre
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)

local notation "widthWindow" => literalPrimitiveDirect_rawWidth_le
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (hstep := hstep)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (hcutoffPower := hcutoffPower)
  (lo := lo) (hi := hi) (hhi := hhi) (orders := orders)
  (originalBound := originalBound) (originalWindow := originalWindow)
  (hrows := hrows) (htime := htime) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)

local notation "firstWindows" => literalPrimitiveDirect_firstNumericWindows
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (hstep := hstep)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (hcutoffPower := hcutoffPower)
  (lo := lo) (hi := hi) (hhi := hhi) (orders := orders)
  (originalBound := originalBound) (originalWindow := originalWindow)
  (hrows := hrows) (htime := htime) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)

local notation "scalarWindows" => literalPrimitiveDirect_originalScalar_bounds
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (hstep := hstep)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (hcutoffPower := hcutoffPower)
  (lo := lo) (hi := hi) (hhi := hhi) (orders := orders)
  (originalBound := originalBound) (originalWindow := originalWindow)
  (hrows := hrows) (htime := htime) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)

local notation "arithmetic" => (stages).prepared.arithmeticLabels (raw).originalAtlas
  hcap exceptional normalization

open CanonicalLiteralPrimitiveMassConstants

variable (profileDegree heightDegree : ℕ)
variable (lengthBound columnBound widthMax massLoss heightConstant : ℝ)
variable (hlengthBound : 0 ≤ lengthBound) (hcolumnBound : 0 ≤ columnBound)
variable (hwidthMax : 0 ≤ widthMax) (hmassLoss : 0 < massLoss)

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
local notation "passiveConstant" => PrimitivePassiveFactoryCard.directConstant K cap columnBound
  (massLoss / 8) hcolumnBound (by positivity)
local notation "physicalConstant" => kernelSourceFibreConstant K cap
  (Fintype.card (PUnit.{1} × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))))
  0 0 columnBound (massLoss / 2) hcolumnBound (by positivity)
local notation "harmonicConstant" => directHarmonicConstant K cap columnBound massLoss
  hcolumnBound hmassLoss

/-- This expression depends only on the fixed original parameters and
kernel tests; it precedes all source labels and scales. -/
def literalPrimitiveDirectMassConstant : ℝ :=
  profileConstant * (passiveConstant * physicalConstant) * harmonicConstant

local notation "totalConstant" => literalPrimitiveDirectMassConstant
  (K := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (μv := μv) (ν := ν)
  (cap := cap) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (loss := loss) (cutoffExponent := cutoffExponent) (hloss := hloss)
  (hcutoffExponent := hcutoffExponent) (mesh := mesh) (lo := lo) (hi := hi)
  (hlo := hlo) (hhi := hhi) (orders := orders) (profileDegree := profileDegree)
  (heightDegree := heightDegree) (lengthBound := lengthBound) (columnBound := columnBound)
  (widthMax := widthMax) (massLoss := massLoss) (heightConstant := heightConstant)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (hwidthMax := hwidthMax) (hmassLoss := hmassLoss)

theorem literalPrimitiveDirectMassConstant_pos : 0 < totalConstant := by
  have hp := profileConstantPos
  have hc := PrimitivePassiveFactoryCard.directConstant_pos K cap columnBound
    (massLoss / 8) hcolumnBound (by positivity)
  have hf := kernelSourceFibreConstant_pos K cap
    (Fintype.card (PUnit.{1} × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))))
    0 0 columnBound (massLoss / 2) hcolumnBound (by positivity)
  have hh := directHarmonicConstant_pos K cap columnBound massLoss hcolumnBound hmassLoss
  exact mul_pos (mul_pos hp (mul_pos hc hf)) hh

variable (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
variable (hwidth : a.m + a.q ≤ widthMax)
variable (hN : ∀ i ∈ (source).columns,
  (Ideal.absNorm ((source).ideal i).val : ℝ) ≤ Z ^ columnBound)
variable (T control : ℝ) (hT : 0 ≤ T) (hcontrol : 1 + T ≤ control)
variable (hprofile : originalBound ≤ control ^ profileDegree)
variable (hheight : analyticHeight ≤ heightConstant * (1 + Real.log Z) * (1 + T) ^ heightDegree)
variable (htilt₁ : δ₁ = tilt) (htilt₂ : δ₂ = tilt) (hcontour : δ = chosenContour)

include htotal hwidth hN hT hcontrol hprofile hheight htilt₁ htilt₂ hcontour in
/-- The actual two certificate coefficients are uniformly bounded
from the original profile and length windows. -/
theorem literalPrimitiveDirect_coefficient_product
    (j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization) :
    (massCertificates j).coefficient * (indexCertificates j).cost ≤
      profileConstant * control ^ degree * Z ^ (massLoss + 5 * error / 3 + mesh) := by
  have hw := widthWindow columnBound hN j
  have hn := firstWindows lengthBound columnBound htotal hN j
  have hbox : rawWidthAt j ≤ widthBox := by linarith
  have h := numericBound Z T (rawWidthAt j) analyticHeight control originalBound error
    (internal).m ((internal).n₁ + (internal).n₂ + (data ξ).geometry.totalLength)
    (idealLogLength Z (firstPhysicalDivisorIdeal (A := A) j.val.2.1.val).val)
    (idealLogLength Z (firstActiveRadical j.val.1.val.1 j.val.1.val.2)) 0
    hZ.le hT hbox hheight hcontrol horiginalBound hprofile hn.1
    (hn.2.1.trans (le_max_left _ _))
    (hn.2.2.1.trans (le_max_right _ _)) (hn.2.2.2.trans (le_max_right _ _))
  rw [coefficientIdentity j, costIdentity j]
  simpa only [htilt₁, htilt₂, hcontour, Real.rpow_zero, mul_one] using h

local notation "productBound" => literalPrimitiveDirect_coefficient_product
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
  (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (step := step) (error := error) (mesh := mesh) (hstep := hstep)
  (herror := herror) (hmesh := hmesh) (hfit := hfit) (hsmall := hsmall) (hslotsZero := hslotsZero)
  (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
  (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
  (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
  (orders := orders) (originalBound := originalBound) (horiginalBound := horiginalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hprimeOrders := hprimeOrders)
  (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (hδsum := hδsum) (herrorPos := herrorPos)
  (hannulusThreshold := hannulusThreshold) (hscaleThreshold := hscaleThreshold)
  (hpaidError := hpaidError)
  (profileDegree := profileDegree) (heightDegree := heightDegree)
  (lengthBound := lengthBound) (columnBound := columnBound) (widthMax := widthMax)
  (massLoss := massLoss) (heightConstant := heightConstant)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (hwidthMax := hwidthMax) (hmassLoss := hmassLoss)
  (htotal := htotal) (hwidth := hwidth) (hN := hN) (T := T) (control := control)
  (hT := hT) (hcontrol := hcontrol) (hprofile := hprofile) (hheight := hheight)
  (htilt₁ := htilt₁) (htilt₂ := htilt₂) (hcontour := hcontour)

include htotal hwidth hN hT hcontrol hprofile hheight htilt₁ htilt₂ hcontour in
/-- The whole actual direct family has a uniform mass.  Both original
arithmetic divisors and all passive allocations are summed internally. -/
theorem literalPrimitiveDirect_global_kernelMass
    (analytic : ∀ j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization,
      (factories j).Input) :
    (∀ b : (completeFamily analytic).active Finset.univ,
      IsFiniteMeasure ((completeFamily analytic).kernel Finset.univ completeMeasure
        ((internal).m + (internal).q) b)) ∧
    (∑ b : (completeFamily analytic).active Finset.univ,
      ((completeFamily analytic).kernel Finset.univ completeMeasure
        ((internal).m + (internal).q) b).real Set.univ) ≤
      totalConstant * control ^ degree * Z ^ (9 * massLoss / 4 + 5 * error / 3 + mesh) := by
  have hm := sourceMass analytic
  refine ⟨hm.1, ?_⟩
  let common := profileConstant * control ^ degree * Z ^ (massLoss + 5 * error / 3 + mesh)
  have hcontrol0 : 0 ≤ control := by linarith
  have hcommon : 0 ≤ common := by
    have hp := (profileConstantPos).le
    dsimp only [common]
    positivity
  have hpoint (j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization)
      (b : ((factories j).family (analytic j)).active Finset.univ) :
      (stages).prepared.parentOuterScalar (raw).originalAtlas normalization j.val *
        ((massCertificates j).coefficient *
          ((((stages).prepared.unscaledParentLeaf (raw).originalAtlas exceptional j.val).weight *
              (sourceCertificates j).frozen) *
            ((factories j).family (analytic j)).weight Finset.univ ((internal).m + (internal).q) b)) ≤
      common * (arithmetic).carrier.indexWeight ((arithmetic).index j) := by
    have hc : 0 ≤ (massCertificates j).coefficient := by
      rw [coefficientIdentity j]
      exact CanonicalLiteralPrimitiveMassCoefficient.kernelCoefficient_nonneg
        K A σ ω ψ cap orders lo hi hlo hhi δ₁ δ₂ δ mesh Z analyticHeight
        (rawWidthAt j) originalBound fixedFirstKernel fixedSecondKernel
        (zero_lt_one.trans hZ) horiginalBound (by positivity) (by positivity)
    have hs := scalarWindows j
    have hs1 : (stages).prepared.originalScalarAt (raw).originalAtlas j.val ≤ 1 := by linarith [hs.2]
    have hp := mul_le_mul_of_nonneg_left (productBound j) hs.1
    have hp' : (stages).prepared.originalScalarAt (raw).originalAtlas j.val *
        ((massCertificates j).coefficient * (indexCertificates j).cost) ≤ common :=
      hp.trans ((mul_le_mul_of_nonneg_right hs1 hcommon).trans_eq (one_mul common))
    have hi := mul_le_mul_of_nonneg_left (outerIndex j (analytic j) b) hc
    calc
      _ = (massCertificates j).coefficient *
        ((stages).prepared.parentOuterScalar (raw).originalAtlas normalization j.val *
          ((((stages).prepared.unscaledParentLeaf (raw).originalAtlas exceptional j.val).weight *
              (sourceCertificates j).frozen) *
            ((factories j).family (analytic j)).weight Finset.univ ((internal).m + (internal).q) b)) := by ring
      _ ≤ (massCertificates j).coefficient *
          ((stages).prepared.originalScalarAt (raw).originalAtlas j.val *
            ((indexCertificates j).cost * (arithmetic).carrier.indexWeight ((arithmetic).index j))) := hi
      _ = ((stages).prepared.originalScalarAt (raw).originalAtlas j.val *
          ((massCertificates j).coefficient * (indexCertificates j).cost)) *
            (arithmetic).carrier.indexWeight ((arithmetic).index j) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp' ((arithmetic).carrier.indexWeight_nonneg _)
  have hsum :
      (∑ b : (completeFamily analytic).active Finset.univ,
        (arithmetic).carrier.indexWeight ((arithmetic).index b.val.1)) =
      ∑ j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization,
        ∑ _b : ((factories j).family (analytic j)).active Finset.univ,
          (arithmetic).carrier.indexWeight ((arithmetic).index j) := by
    simpa only [Finset.univ_sigma_univ, Finset.sum_coe_sort] using
      ActualNormalizedPairFamily.sum_sigmaCombine_active
        (fun j => (factories j).family (analytic j)) Finset.univ (fun _ => Finset.univ)
        (fun b => (arithmetic).carrier.indexWeight ((arithmetic).index b.val.1))
  have harithmetic := (stages).arithmeticLabels_admissible (raw).originalAtlas hcap
    exceptional normalization columnBound 1 (by simp) (fun _ _ => one_dvd _) hN
  have hcard := fibreBound columnBound massLoss hcolumnBound hmassLoss hN analytic
  have hpassive := (PrimitivePassiveFactoryCard.directConstant_pos K cap columnBound
    (massLoss / 8) hcolumnBound (by positivity)).le
  have hphysical := (kernelSourceFibreConstant_pos K cap
    (Fintype.card (PUnit.{1} × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))))
    0 0 columnBound (massLoss / 2) hcolumnBound (by positivity)).le
  have hh := direct_harmonic_sum K cap columnBound massLoss hcolumnBound hmassLoss Z hZ.le
    (arithmetic).carrier harithmetic
    (fun b : (completeFamily analytic).active Finset.univ => (arithmetic).index b.val.1)
    ((passiveConstant * physicalConstant) * Z ^ (massLoss / 4)) (by positivity) hcard
  calc
    _ ≤ ∑ j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization,
        (stages).prepared.parentOuterScalar (raw).originalAtlas normalization j.val *
          ((massCertificates j).coefficient *
            ∑ b : ((factories j).family (analytic j)).active Finset.univ,
              (((stages).prepared.unscaledParentLeaf (raw).originalAtlas exceptional j.val).weight *
                (sourceCertificates j).frozen) *
                  ((factories j).family (analytic j)).weight Finset.univ ((internal).m + (internal).q) b) := hm.2
    _ ≤ ∑ j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization,
        ∑ _b : ((factories j).family (analytic j)).active Finset.univ,
          common * (arithmetic).carrier.indexWeight ((arithmetic).index j) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Finset.mul_sum]
      exact Finset.sum_le_sum (fun b _ => hpoint j b)
    _ = common * ∑ b : (completeFamily analytic).active Finset.univ,
        (arithmetic).carrier.indexWeight ((arithmetic).index b.val.1) := by
      rw [hsum]
      simp only [Finset.mul_sum]
    _ ≤ common *
        (((passiveConstant * physicalConstant) * Z ^ (massLoss / 4)) *
          harmonicConstant * Z ^ massLoss) := mul_le_mul_of_nonneg_left hh hcommon
    _ = _ := by
      dsimp only [common, literalPrimitiveDirectMassConstant]
      rw [show 9 * massLoss / 4 + 5 * error / 3 + mesh =
        (massLoss + 5 * error / 3 + mesh) + (massLoss / 4) + massLoss by ring,
        Real.rpow_add (zero_lt_one.trans hZ)
          ((massLoss + 5 * error / 3 + mesh) + (massLoss / 4)) massLoss,
        Real.rpow_add (zero_lt_one.trans hZ)
          (massLoss + 5 * error / 3 + mesh) (massLoss / 4)]
      ring

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectMassConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirect_coefficient_product
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirect_global_kernelMass
