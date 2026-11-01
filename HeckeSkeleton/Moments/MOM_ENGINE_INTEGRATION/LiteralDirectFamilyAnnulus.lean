import HeckeSkeleton.Moments.MOM_ENGINE_INTEGRATION.LiteralPassiveFamilyAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectFactory

/-!
# Positive windows on the original direct family

Both actual direct factories expose the original covered passive
constructor. Support therefore passes to their same active children,
then through the original live-key dispatcher and sigma family.
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

namespace LiteralDirectFamilySupport

open EngineStep.CompleteMovingRowRecipe

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

/-- The original left direct case constructs its own passive family. -/
local notation "leftFactory" => literalPrimitiveLeftDirectFactory
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

local notation "rightFactory" => literalPrimitiveRightDirectFactory
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

theorem literalPrimitiveLeftDirectFactory_annulusSupport
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pieces DE D).rightData.columns
      (fun j => (((source).pieces DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (leaf : ((stages DE D).left S χ).supported.gated.CoveredLeafKey
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ))
    (hS : Squarefree S.val)
    (hlive : (((stages DE D).left S χ).supported.gated.fiberCoveredLeaf
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
      ((exceptional DE D).left S χ) ((source).charts DE D).kernel
      ((source).charts DE D).leftPoint leaf).Live) :
    ∀ input : (leftFactory DE D S χ leaf hS hlive).Input,
      FamilyAnnulusSupport ((leftFactory DE D S χ leaf hS hlive).family input)
        Finset.univ lo hi orders := by
  intro input
  unfold EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftDirectFactory
  dsimp only [CurriedNormalizedFamily.family, CurriedNormalizedFamily.ofCurried]
  unfold EngineStep.CompleteMovingRowRecipe.literalLeftDirectPassiveNormalizationFamily
  dsimp only
  apply LiteralPassiveFamilySupport.annulusSupport

theorem literalPrimitiveRightDirectFactory_annulusSupport
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pieces DE D).rightData.columns
      (fun j => (((source).pieces DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (leaf : ((stages DE D).right S χ).supported.gated.CoveredLeafKey
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ))
    (hS : Squarefree S.val)
    (hlive : (((stages DE D).right S χ).supported.gated.fiberCoveredLeaf
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
      ((exceptional DE D).right S χ) ((source).charts DE D).kernel
      (fun i => -((source).charts DE D).rightPoint i) leaf).Live) :
    ∀ input : (rightFactory DE D S χ leaf hS hlive).Input,
      FamilyAnnulusSupport ((rightFactory DE D S χ leaf hS hlive).family input)
        Finset.univ lo hi orders := by
  intro input
  unfold EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightDirectFactory
  dsimp only [CurriedNormalizedFamily.family, CurriedNormalizedFamily.ofCurried]
  unfold EngineStep.CompleteMovingRowRecipe.literalRightDirectPassiveNormalizationFamily
  dsimp only
  apply LiteralPassiveFamilySupport.annulusSupport

theorem literalPrimitiveDirectFactory_annulusSupport
    (j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization) :
    ∀ input : (factories j).Input,
      FamilyAnnulusSupport ((factories j).family input) Finset.univ lo hi orders := by
  have hS := (stages).prepared.live_first_divisor_squarefree
    (raw).originalAtlas exceptional normalization j
  have hparent := (stages).prepared.liveLeaves_spec (raw).originalAtlas exceptional normalization j
  rcases j with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩
  · have hblock := (((stages).prepared DE D).coveredLeaf (raw).originalAtlas (raw).originalAtlas
      ((normalization).left DE D) ((normalization).right DE D)
      ((normalization).left_pos DE D) ((normalization).right_pos DE D)
      (exceptional DE D) ⟨S, χ, .inl leaf⟩).live_of_scale_live _ _ hparent
    have hfiber := (((stages DE D).left S χ).supported.gated.fiberCoveredLeaf
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
      ((exceptional DE D).left S χ) ((source).charts DE D).kernel
      ((source).charts DE D).leftPoint leaf).live_of_scale_live _ _ hblock
    exact literalPrimitiveLeftDirectFactory_annulusSupport
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
      DE D S χ leaf hS hfiber
  · have hblock := (((stages).prepared DE D).coveredLeaf (raw).originalAtlas (raw).originalAtlas
      ((normalization).left DE D) ((normalization).right DE D)
      ((normalization).left_pos DE D) ((normalization).right_pos DE D)
      (exceptional DE D) ⟨S, χ, .inr leaf⟩).live_of_scale_live _ _ hparent
    have hfiber := (((stages DE D).right S χ).supported.gated.fiberCoveredLeaf
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
      ((exceptional DE D).right S χ) ((source).charts DE D).kernel
      (fun i => -((source).charts DE D).rightPoint i) leaf).live_of_scale_live _ _ hblock
    exact literalPrimitiveRightDirectFactory_annulusSupport
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
      DE D S χ leaf hS hfiber

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

local notation "factorySupport" => literalPrimitiveDirectFactory_annulusSupport
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

/-- The original direct sigma family has both tighter supports on
its same public frozen children. -/
theorem literalPrimitiveDirect_family_annulusSupport
    (analytic : ∀ j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization,
      (factories j).Input) :
    FamilyAnnulusSupport (completeFamily analytic) Finset.univ lo hi orders := by
  have h := FamilyAnnulusSupport.sigmaCombine
    (fun j => (factories j).family (analytic j)) Finset.univ (fun _ => Finset.univ)
    (fun j _ => factorySupport j (analytic j))
  simpa only [Finset.univ_sigma_univ] using h

theorem literalPrimitiveLeftDirectFactory_originalSupport
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pieces DE D).rightData.columns
      (fun j => (((source).pieces DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (leaf : ((stages DE D).left S χ).supported.gated.CoveredLeafKey
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ))
    (hS : Squarefree S.val)
    (hlive : (((stages DE D).left S χ).supported.gated.fiberCoveredLeaf
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
      ((exceptional DE D).left S χ) ((source).charts DE D).kernel
      ((source).charts DE D).leftPoint leaf).Live) :
    ∀ input : (leftFactory DE D S χ leaf hS hlive).Input,
      FamilyOriginalSupport ((leftFactory DE D S χ leaf hS hlive).family input)
        lo hi := by
  intro input
  unfold EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftDirectFactory
  dsimp only [CurriedNormalizedFamily.family, CurriedNormalizedFamily.ofCurried]
  unfold EngineStep.CompleteMovingRowRecipe.literalLeftDirectPassiveNormalizationFamily
  dsimp only
  apply LiteralPassiveFamilySupport.originalSupport

theorem literalPrimitiveRightDirectFactory_originalSupport
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pieces DE D).rightData.columns
      (fun j => (((source).pieces DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (leaf : ((stages DE D).right S χ).supported.gated.CoveredLeafKey
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ))
    (hS : Squarefree S.val)
    (hlive : (((stages DE D).right S χ).supported.gated.fiberCoveredLeaf
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
      ((exceptional DE D).right S χ) ((source).charts DE D).kernel
      (fun i => -((source).charts DE D).rightPoint i) leaf).Live) :
    ∀ input : (rightFactory DE D S χ leaf hS hlive).Input,
      FamilyOriginalSupport ((rightFactory DE D S χ leaf hS hlive).family input)
        lo hi := by
  intro input
  unfold EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightDirectFactory
  dsimp only [CurriedNormalizedFamily.family, CurriedNormalizedFamily.ofCurried]
  unfold EngineStep.CompleteMovingRowRecipe.literalRightDirectPassiveNormalizationFamily
  dsimp only
  apply LiteralPassiveFamilySupport.originalSupport

theorem literalPrimitiveDirectFactory_originalSupport
    (j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization) :
    ∀ input : (factories j).Input,
      FamilyOriginalSupport ((factories j).family input) lo hi := by
  have hS := (stages).prepared.live_first_divisor_squarefree
    (raw).originalAtlas exceptional normalization j
  have hparent := (stages).prepared.liveLeaves_spec (raw).originalAtlas exceptional normalization j
  rcases j with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩
  · have hblock := (((stages).prepared DE D).coveredLeaf (raw).originalAtlas (raw).originalAtlas
      ((normalization).left DE D) ((normalization).right DE D)
      ((normalization).left_pos DE D) ((normalization).right_pos DE D)
      (exceptional DE D) ⟨S, χ, .inl leaf⟩).live_of_scale_live _ _ hparent
    have hfiber := (((stages DE D).left S χ).supported.gated.fiberCoveredLeaf
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
      ((exceptional DE D).left S χ) ((source).charts DE D).kernel
      ((source).charts DE D).leftPoint leaf).live_of_scale_live _ _ hblock
    exact literalPrimitiveLeftDirectFactory_originalSupport
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
      DE D S χ leaf hS hfiber
  · have hblock := (((stages).prepared DE D).coveredLeaf (raw).originalAtlas (raw).originalAtlas
      ((normalization).left DE D) ((normalization).right DE D)
      ((normalization).left_pos DE D) ((normalization).right_pos DE D)
      (exceptional DE D) ⟨S, χ, .inr leaf⟩).live_of_scale_live _ _ hparent
    have hfiber := (((stages DE D).right S χ).supported.gated.fiberCoveredLeaf
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
      (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
      ((exceptional DE D).right S χ) ((source).charts DE D).kernel
      (fun i => -((source).charts DE D).rightPoint i) leaf).live_of_scale_live _ _ hblock
    exact literalPrimitiveRightDirectFactory_originalSupport
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
      DE D S χ leaf hS hfiber

local notation "originalCompleteFamily" => literalPrimitiveDirectFamily
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

local notation "factoryOriginal" => literalPrimitiveDirectFactory_originalSupport
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

/-- The original direct sigma family has both tighter supports on
its same public frozen children. -/
theorem literalPrimitiveDirect_family_originalSupport
    (analytic : ∀ j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization,
      (factories j).Input) :
    FamilyOriginalSupport (originalCompleteFamily analytic) lo hi := by
  exact FamilyOriginalSupport.sigmaCombine
    (fun j => (factories j).family (analytic j))
    (fun j => factoryOriginal j (analytic j))

end LiteralDirectFamilySupport
end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.LiteralDirectFamilySupport.literalPrimitiveLeftDirectFactory_annulusSupport
#print axioms HeckeSkeleton.Moments.EngineInduction.LiteralDirectFamilySupport.literalPrimitiveRightDirectFactory_annulusSupport
#print axioms HeckeSkeleton.Moments.EngineInduction.LiteralDirectFamilySupport.literalPrimitiveDirectFactory_annulusSupport
#print axioms HeckeSkeleton.Moments.EngineInduction.LiteralDirectFamilySupport.literalPrimitiveDirect_family_annulusSupport

#print axioms HeckeSkeleton.Moments.EngineInduction.LiteralDirectFamilySupport.literalPrimitiveDirect_family_originalSupport
