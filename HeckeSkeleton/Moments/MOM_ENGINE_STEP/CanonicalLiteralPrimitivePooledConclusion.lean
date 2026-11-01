import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledParentBound
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledOutput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledGlobalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveEngineConclusion
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualFirstSourceTerminalNonneg

/-!
# The actual amplified family gives the engine conclusion

Every family, measure and child in this internal assembly is the actual
primitive producer's existing object. The original first-width identity
transports only the scalar kernel denominator. Geometry, moving inputs,
individual integrability, the parent inequality and the complete global
mass estimate are constructed by their proved actual-source theorems.
The remaining comparisons are numerical terminal and fixed-constant
budgets, supplied by the final uniform parameter choice.
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

local notation "completeFamily" => literalPrimitivePooledFamily
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

local notation "completeMeasure" => literalPrimitivePooledMeasure
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

local notation "degree" => CanonicalLiteralPassiveMassCoefficient.degree
  cap profileDegree 0 0 0 heightDegree

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

variable (hwidth : a.m + a.q ≤ widthMax)
variable (T control : ℝ) (hT : 0 ≤ T) (hcontrol : 1 + T ≤ control)
variable (hprofile : originalBound ≤ control ^ profileDegree)
variable (hheight : analyticHeight ≤ heightConstant * (1 + Real.log Z) * (1 + T) ^ heightDegree)
variable (htilt₁ : δ₁ = tilt) (htilt₂ : δ₂ = tilt) (hcontour : δ = chosenContour)

local notation "outputGeometry" => literalPrimitivePooled_family_outputGeometry
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


local notation "movingChildren" => literalPrimitivePooled_family_moving_admissible
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


local notation "integrableChildren" => literalPrimitivePooled_family_children_integrable
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


local notation "parentBound" => literalPrimitivePooled_parent_le_kernel
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


local notation "globalMass" => literalPrimitivePooled_global_kernelMass
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
  (heps := heps) (hepsSmall := hepsSmall)

variable {sTail sZero : Finset (ℕ × ℕ)} {terminalSlots : ℕ}
variable {Lmax Nsave decay εzero Cerror Czero : ℝ}
variable {ε terminalExponent finalConstant finalControl : ℝ}

/-- Complete actual-source assembly. No output geometry, finished
kernel mass, child admissibility or source integral is an input. -/
def literalPrimitivePooledConclusion
    (hlarge : totalThreshold ≤ Z)
    (terminal : stages.DualTerminalCalibration sTail sZero terminalSlots Lmax Nsave decay)
    (hCerror : 0 ≤ Cerror) (hCzero : 0 ≤ Czero)
    (hstage : ∀ {j : Type*} (p : FirstGaussPoolData C pool j)
      (c : j → ℂ) (x : j → ℝ)
      (stage : ActualPoolStages (E := ℝ)
        (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
        μv hDiff p c (rowBallFiniteFamily K A.Sf 1))
      (hs : stage.DualSourceConditions)
      (cal : stage.DualTerminalCalibration sTail sZero terminalSlots Lmax Nsave decay)
      (z : ℝ),
      p.energy (FirstGaussPoolData.twistedCoefficient c x z) ≤
        cal.rawPhaseCost x z εzero Cerror Czero)
    (analytic : ∀ j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization,
      (factories j).Input)
    (firstZero firstTail exceptionalCost : ℝ)
    (hfirstZero : 0 ≤ firstZero) (hfirstTail : 0 ≤ firstTail)
    (hexceptionalCost : 0 ≤ exceptionalCost)
    (hfirst : pairedStageEnergy centered (data ξ) a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
      firstZero + firstTail + firstSource.rawRowCost hDiff / Z ^ (a.m + a.q))
    (hexceptional : stages.supported.gated.exceptionalBudget raw.originalAtlas exceptional normalization /
      Z ^ (a.m + a.q) ≤ exceptionalCost)
    (hterminals : firstZero +
      stages.dualSecondZeroBudget terminal normalization εzero Czero / Z ^ (a.m + a.q) +
        exceptionalCost +
        (firstTail + stages.dualSecondTailBudget terminal normalization Cerror / Z ^ (a.m + a.q)) ≤
      finalConstant * finalControl * Z ^ terminalExponent)
    (hmassComparison : totalConstant * control ^ degree * Z ^ (9 * massLoss / 4 + eps + 5 * error / 3 + mesh) ≤
      finalConstant * finalControl * Z ^ ε) :
    PairedEngineConclusion (Ω := WithLp 2 (ℝ × ℝ)) centered (data ξ) a
      Z t Y₁ Y₂ step ε terminalExponent finalConstant finalControl
        (MovingEngineChildAdmissible A P R
          (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (data ξ)
          Set.univ (Set.Icc (0 : ℝ) hi) orders Z) := by
  have hm := globalMass hlarge analytic
  have hwidthEq : internal.m + internal.q = a.m + a.q :=
    Q.fullSupportParameters_width a Z
  rw [hwidthEq] at hm
  have hden : 0 ≤ Z ^ (a.m + a.q) :=
    Real.rpow_nonneg (zero_le_one.trans hZ.le) _
  have hsecondZero : 0 ≤ stages.dualSecondZeroBudget terminal normalization εzero Czero /
      Z ^ (a.m + a.q) :=
    div_nonneg (ActualFirstSource.SecondStages.dualSecondZeroBudget_nonneg
      (R := stages) terminal normalization εzero Czero hCzero) hden
  have hsecondTail : 0 ≤ stages.dualSecondTailBudget terminal normalization Cerror /
      Z ^ (a.m + a.q) :=
    div_nonneg (ActualFirstSource.SecondStages.dualSecondTailBudget_nonneg
      (R := stages) terminal normalization Cerror hCerror) hden
  have hp := parentBound terminal hCerror hCzero hstage analytic
    firstZero firstTail exceptionalCost hfirst hexceptional
  exact PairedEngineConclusion.ofLiteralPrimitiveFamily
    (completeFamily analytic) completeMeasure
    (outputGeometry analytic) (movingChildren analytic)
    (integrableChildren analytic (a.m + a.q)) (zero_lt_one.trans hZ)
    firstZero (stages.dualSecondZeroBudget terminal normalization εzero Czero / Z ^ (a.m + a.q))
    exceptionalCost
    (firstTail + stages.dualSecondTailBudget terminal normalization Cerror / Z ^ (a.m + a.q))
    hfirstZero hsecondZero hexceptionalCost (add_nonneg hfirstTail hsecondTail) hterminals
    (by simpa only [ActualNormalizedPairFamily.childPair_eq_frozen] using hp)
    ⟨hm.1, hm.2.trans hmassComparison⟩

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledConclusion
