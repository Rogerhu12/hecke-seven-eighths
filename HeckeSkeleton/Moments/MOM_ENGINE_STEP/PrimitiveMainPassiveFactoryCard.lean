import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveMainSourceIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PrimitivePassiveFactoryCard

/-!
# The genuine primitive factory label count

The unchanged source factory exposes its actual independent passive
labels. Original occurrence embeddings supply their slot cap, and the
original common-support membership supplies the first ideal's norm.
No analytic input or finished cardinality estimate is assumed.
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

local notation "leftFactory" => literalPrimitiveLeftMainFactory
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

local notation "rightFactory" => literalPrimitiveRightMainFactory
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

/-- The count is for this factory's stored label type, before any
individual analytic certificate is supplied. -/
theorem literalPrimitiveLeftMainFactory_card
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pools DE D).rightData.columns
      (fun j => (((source).pools DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (leaf : (((stages DE D).left S χ).main).supported.gated.CoveredLeafKey ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).main) ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).main))
    (hS : Squarefree S.val)
    (hlive : ((((stages DE D).left S χ).main).supported.gated.fiberCoveredLeaf ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).main) ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).main)
      ((exceptional DE D).left S χ).main ((source).charts DE D).kernel ((source).charts DE D).leftPoint leaf).Live)
    (ε : ℝ) (hε : 0 < ε) :
    (Fintype.card (leftFactory DE D S χ leaf hS hlive).Label : ℝ) ≤
      PrimitivePassiveFactoryCard.directConstant K cap columnBound ε hcolumnBound hε * Z ^ ε := by
  let v := leaf.1
  let originalL := literalLeftMainAtoms
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
      ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
      (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
      ((source).pools DE D) S χ (((source).block DE).literalLeftFixed D.val)
      (((source).block DE).literalLeftFixed_generates C D.val) δ₂ v.2.2.1
  let originalRecipeL := literalLeftMainRecipe
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
      ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
      (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
      ((source).pools DE D) S χ (((source).block DE).literalLeftFixed D.val)
      (((source).block DE).literalLeftFixed_generates C D.val) δ₂ v.2.2.1
  let originalR := literalLeftMainAtoms
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
      ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
      (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
      ((source).pools DE D) S χ (((source).block DE).literalLeftFixed D.val)
      (((source).block DE).literalLeftFixed_generates C D.val) δ₂ v.2.2.2.1
  let originalRecipeR := literalLeftMainRecipe
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
      ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
      (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
      ((source).pools DE D) S χ (((source).block DE).literalLeftFixed D.val)
      (((source).block DE).literalLeftFixed_generates C D.val) δ₂ v.2.2.2.1
  let recipeL := v.literalLeftRecipe (originalL.redistributeNormFactors δ₁ δ₂)
    (originalRecipeL.redistributeNormFactors δ₁ δ₂)
  let recipeR := v.literalRightRecipe (originalR.redistributeNormFactors δ₁ δ₂)
    (originalRecipeR.redistributeNormFactors δ₁ δ₂)
  have hD := (actual_common_pair_properties (source).columns (source).columns
    (fun i => ((source).ideal i).val) (fun i => ((source).ideal i).val) DE).1
  have hDN := (actual_common_pair_norm (source).columns (source).columns
    (fun i => ((source).ideal i).val) (fun i => ((source).ideal i).val) (Z ^ columnBound)
    (fun i _ => ((source).ideal i).property.1) (fun i _ => ((source).ideal i).property.1)
    hN hN DE).1
  exact PrimitivePassiveFactoryCard.direct_bound cap columnBound ε hcolumnBound hε
    Z hZ DE.val.1 hD hDN recipeL.slots recipeR.slots hcap

/-- The count is for this factory's stored label type, before any
individual analytic certificate is supplied. -/
theorem literalPrimitiveRightMainFactory_card
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pools DE D).rightData.columns
      (fun j => (((source).pools DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (leaf : (((stages DE D).right S χ).main).supported.gated.CoveredLeafKey ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).main) ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).main))
    (hS : Squarefree S.val)
    (hlive : ((((stages DE D).right S χ).main).supported.gated.fiberCoveredLeaf ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).main) ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).main)
      ((exceptional DE D).right S χ).main ((source).charts DE D).kernel (fun i => -((source).charts DE D).rightPoint i) leaf).Live)
    (ε : ℝ) (hε : 0 < ε) :
    (Fintype.card (rightFactory DE D S χ leaf hS hlive).Label : ℝ) ≤
      PrimitivePassiveFactoryCard.directConstant K cap columnBound ε hcolumnBound hε * Z ^ ε := by
  let v := leaf.1
  let originalL := literalRightMainAtoms
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
      ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
      (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
      ((source).pools DE D) S χ (((source).block DE).literalRightFixed D.val)
      (((source).block DE).literalRightFixed_generates C D.val) δ₂ v.2.2.1
  let originalRecipeL := literalRightMainRecipe
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
      ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
      (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
      ((source).pools DE D) S χ (((source).block DE).literalRightFixed D.val)
      (((source).block DE).literalRightFixed_generates C D.val) δ₂ v.2.2.1
  let originalR := literalRightMainAtoms
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
      ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
      (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
      ((source).pools DE D) S χ (((source).block DE).literalRightFixed D.val)
      (((source).block DE).literalRightFixed_generates C D.val) δ₂ v.2.2.2.1
  let originalRecipeR := literalRightMainRecipe
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
      ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
      (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
      ((source).pools DE D) S χ (((source).block DE).literalRightFixed D.val)
      (((source).block DE).literalRightFixed_generates C D.val) δ₂ v.2.2.2.1
  let recipeL := v.literalLeftRecipe (originalL.redistributeNormFactors δ₁ δ₂)
    (originalRecipeL.redistributeNormFactors δ₁ δ₂)
  let recipeR := v.literalRightRecipe (originalR.redistributeNormFactors δ₁ δ₂)
    (originalRecipeR.redistributeNormFactors δ₁ δ₂)
  have hD := (actual_common_pair_properties (source).columns (source).columns
    (fun i => ((source).ideal i).val) (fun i => ((source).ideal i).val) DE).1
  have hDN := (actual_common_pair_norm (source).columns (source).columns
    (fun i => ((source).ideal i).val) (fun i => ((source).ideal i).val) (Z ^ columnBound)
    (fun i _ => ((source).ideal i).property.1) (fun i _ => ((source).ideal i).property.1)
    hN hN DE).1
  exact PrimitivePassiveFactoryCard.direct_bound cap columnBound ε hcolumnBound hε
    Z hZ DE.val.1 hD hDN recipeL.slots recipeR.slots hcap

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftMainFactory_card
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightMainFactory_card
