import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPooledExceptionalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledColumns

/-!
# Exceptional estimates for the original primitive pooled sources

The same primitive first source fixes its original common labels, pool,
row windows and residual columns. All geometric inputs to the literal
exceptional estimates below are proved from these original objects.
No post-transform source window, selected side or terminal estimate is
an input. The finite original volume primitive is selected at the fixed
compact support and fixed width box before any actual leaf.
-/

set_option autoImplicit false
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
open HeckePort.Moments.MobiusRegroup HeckePort.IdealMobiusDivisorSum

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
variable (step : ℝ) (hstep : 0 < step)
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
variable (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive ψ (data ξ).theta
  (Set.Icc lo hi))
variable (ε widthMax : ℝ) (hε : 0 < ε) (hwidthMax : 0 ≤ widthMax)
local notation "maskExponent" => CanonicalLiteralExceptionalPhysicalBox.maskExponent
  widthMax loss cutoffExponent
local notation "hmaskExponent" => CanonicalLiteralExceptionalPhysicalBox.maskExponent_nonneg
  hwidthMax hloss hcutoffExponent
local notation "orders" => CanonicalLiteralExceptionalUnifiedChoice.orders
  (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExponent hε hmaskExponent
local notation "heightOrder" => CanonicalLiteralExceptionalUnifiedChoice.heightOrder
  (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExponent hε hmaskExponent
variable (originalBound : ℝ) (hamplitude : 1 ≤ originalBound)
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
variable (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta)
variable (hplaces : CanonicalLiteralExceptionalArithmetic.thetaBadPrimes (data ξ).theta ⊆ A.Sf)
variable (hlower : hi⁻¹ ≤ lo) (hδsum : δ₁ + δ₂ ≤ 1 / 2)
variable (slotLoss finalLoss : ℝ) (hslotLossNonneg : 0 ≤ slotLoss) (hfinalLoss : 0 ≤ finalLoss)
variable (hslotLoss : hi ≤ Z ^ (2 * slotLoss))
variable (hslots : (cap : ℝ) * slotLoss ≤ finalLoss / 16)
variable (hsupport : 2 * loss + cutoffExponent ≤ finalLoss / 16)
variable (hvolume : ε ≤ finalLoss / 16)
variable (hwidth : a.m + a.q ≤ widthMax)
variable (hthreshold : max 2 (Ideal.absNorm A.cS : ℝ) ≤ Z)

variable (lengthBound columnBound : ℝ)
variable (hlengthBound : 0 ≤ lengthBound) (hcolumnBound : 0 ≤ columnBound)
variable (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
variable (hfirstBox : columnBound + 2 * (step / 3) ≤ widthMax)
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

local notation "Γ₀" => sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "hΓ₀" => actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "fixedCoefficient" => CanonicalLiteralExceptionalSourceBudget.coefficient
  (A := A) (σ := σ) (η := η) (hS := hS) primitive ε widthMax loss cutoffExponent
    hε hwidthMax hloss hcutoffExponent δ₁ δ₂ hi cap
local notation "degree" => CanonicalLiteralExceptionalSourceBudget.profileDegree cap +
  CanonicalLiteralExceptionalAtomBudget.commonDegree cap
local notation "supportError" => 2 * loss + cutoffExponent
local notation "hsupportError" => (by positivity : 0 ≤ 2 * loss + cutoffExponent)
local notation "domainInternal" => domain.withSupportLength (Q.fullSupportLength Z)

/-- The right prepared source negates the original first chart location.
The literal right dictionary therefore retains the positive logarithm. -/
theorem literalPrimitivePooled_rightPoint_neg
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset) :
    (fun i => -((source).charts DE D).rightPoint i) =
      (fun i => Real.log (A.exteriorNorm (((source).block DE).rightResidual i))) := by
  funext i
  change -(-Real.log (A.exteriorNorm (((source).block DE).rightResidual i))) = _
  exact neg_neg _

section LeftMain

variable (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
variable (S : divisorPool ((source).pools DE D).rightData.columns
  (fun j => (((source).pools DE D).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)
local notation "first" => OriginalNominalGeometry.canonicalMain
  (a := internal) (Z := Z) (step := step) (((source).block DE).literalLeftCoordinates D.val)
  supportError (zero_lt_one.trans hZ) hsupportError
local notation "rowWindow" => (((source).pools DE D).divisorPools.leftData S).literalMainRows
  internal (((source).block DE).literalLeftCoordinates D.val) supportError hsupportError
  hstep (leftRows DE D S)
local notation "stage" => ((stages DE D).left S χ).main
local notation "cover" => (((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).main
local notation "point" => ((source).charts DE D).leftPoint
local notation "movingCost" => step / 3
local notation "firstFixed" => ((source).block DE).literalLeftFixed D.val
local notation "hfirst" => ((source).block DE).literalLeftFixed_generates C D.val
local notation "phases" => CanonicalLiteralActualCharacters.unamplifiedPhases
  firstFixed (CanonicalLiteralFirstPhase.leftElement C ((source).block DE).primes
    ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst
local notation "predicate" => (stage).supported.gated.literalHybridPredicates
  cover cover P R phases Q.moving Q.correction (data ξ).theta
variable (leaf : (stage).supported.gated.CoveredLeafKey cover cover)
variable (hsquarefree : Squarefree S.val)
variable (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover predicate
  ((source).charts DE D).kernel point leaf).Live)
local notation "v" => leaf.1
local notation "j" => leaf.2
local notation "bareLive" => ((v).leaf predicate ((source).charts DE D).kernel point j).live_of_scale_live _ _ hlive
local notation "construction" => literalLeftMainExceptionalExtraction
    (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := (source).block DE) (C := C)
    (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ) (hDiff := hDiff)
    (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (retainedScale := (first).retainedScale) (g := (first).enlargement) (hscale := (first).retainedScale_pos)
    (domain := domainInternal) («v» := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
    («firstFixed» := firstFixed) («hfirst» := hfirst) («j» := j) (hS := hsquarefree)
    (hlive := bareLive)
local notation "oldLeftAtoms" => literalLeftMainAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ firstFixed hfirst δ₂ v.2.2.1
local notation "oldRightAtoms" => literalLeftMainAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ firstFixed hfirst δ₂ v.2.2.2.1
local notation "leftScalar" => literalLeftMainScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ v.2.2.1 * ((oldLeftAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => literalLeftMainScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ v.2.2.2.1 * ((oldRightAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rawRows" => (v).chart.actualRows ∅ cutoff₂ hcutoff₂ (v).rowLabel
local notation "characters" => (rawRows).literalFiniteCharacters C P R phases Q.moving Q.correction
  ((v).chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ (v).rowLabel)
  ((v).chart.originalSector P ∅ cutoff₂ hcutoff₂ (v).rowLabel) (data ξ).theta
local notation "outer" => (construction).val.stripOuter leftScalar rightScalar
  (construction).property.2.1 (construction).property.2.2
local notation "allowance" => firstLeftAllowance Z
  ((first).skeleton.A + ((first).skeleton.q + (first).skeleton.R + (first).skeleton.E))
  (first).ideals.first.val (first).ideals.opposite.val
local notation "radical" => (Ideal.absNorm (commonRadical
  (primePowerProduct (v).block.primes (v).block.leftMultiplicity).val
  (primePowerProduct (v).block.primes (v).block.rightMultiplicity).val) : ℝ)

include originalWindow hrows htime hprime hamplitude hlo hhi hcap hY₁ hY₂ hlower hδsum href
  hslotLossNonneg hfinalLoss
  hslotLoss hslots hone hplaces hsupport hcutoffPower₂ hsquarefree hlive hwidth hthreshold hvolume hfirstBox in
/-- The actual centered left main source uses its original
primitive row and column windows, including the original full support. -/
theorem literalPrimitiveLeftMainExceptional_pointwise
    (hcentered : centered = true) (hpadding : 0 ≤ padding)
    (thetaPair : (data ξ).theta × (data ξ).theta) (z : ℝ × ℝ) :
    ((outer).thetaClassLeaf characters thetaPair).exceptionalIntegrand z / allowance ≤
      (hi ^ cap * orbitalFieldFactor K * ((Γ₀).index : ℝ) * fixedCoefficient) *
        originalBound ^ degree *
        (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ heightOrder *
        Z ^ (padding + 3 * step + finalLoss / 2 + movingCost) / radical *
        Z ^ (-idealLogLength Z j.1.val) := by
  have hactive : ∀ i ∈ ((((source).pools DE D).divisorPools.leftData S).mainSource (((source).pools DE D).leftDivisorCoefficient S χ)).columns,
      ((((source).pools DE D).divisorPools.leftData S).mainSource (((source).pools DE D).leftDivisorCoefficient S χ)).coefficient i ≠ 0 →
      A.exteriorNorm (((((source).pools DE D).divisorPools.leftData S).mainSource (((source).pools DE D).leftDivisorCoefficient S χ)).ideal i) ≤
        Z ^ ((first).skeleton.A - (first).skeleton.c - (first).skeleton.w + loss) := by
    intro i hcol hci
    change A.exteriorNorm (((((source).pools DE D).divisorPools.leftData S).mainSource (((source).pools DE D).leftDivisorCoefficient S χ)).ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z -
        idealLogLength Z (((source).block DE).literalLeftCoordinates D.val).first.val - 0 + loss)
    rw [((source).block DE).literalLeftCoordinates_first, sub_zero]
    exact literalPrimitiveLeftMain_active_norm
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
      (pool := pool) (hdensity := hdensity) DE D S χ i hcol hci
  have hcutoffPaid : CanonicalLiteralExceptionalGeometry.paidCutoff loss cutoffExponent 0 / 6 ≤
      finalLoss / 16 := by
    unfold CanonicalLiteralExceptionalGeometry.paidCutoff
    linarith
  have hwidthInternal : (internal).m + (internal).q ≤ widthMax := by
    simpa only [Q.fullSupportParameters_width] using hwidth
  have hDE : DE.val ∈ commonSupportPool (raw).exteriorColumns (raw).exteriorColumns
      (fun i => ((raw).columnExterior i).val) (fun i => ((raw).columnExterior i).val) := DE.property
  have hcolumns : ∀ i ∈ (raw).exteriorColumns,
      A.exteriorNorm ((raw).columnExterior i) ≤ Z ^ widthMax := by
    intro i hi
    exact (hN i hi).trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [hstep.le]))
  exact literalLeftMainExceptional_pointwise
    (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := (source).block DE) (C := C)
    (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ) (hDiff := hDiff)
    (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (step := step) («supportError» := supportError) («hsupportError» := hsupportError)
    (lo := lo) (hi := hi) (hlo := hlo) (primitive := primitive)
    (ε := ε) (widthMax := widthMax) (columnLoss := loss) (cutoffExponent := cutoffExponent)
    (hε := hε) (hwidthMax := hwidthMax) (hcolumnLoss := hloss) (hcutoffExponent := hcutoffExponent)
    (originalBound := originalBound) (annulus := hi) (hamplitude := hamplitude) (hannulus := hhi)
    (reference := reference) (href := by
      simpa only [Q.literalPrimitiveFirstSource_pairedRows] using href)
    (originalWindow := originalWindow) (hreference := hrows reference href) (htime := htime)
    (hprime := hprime) (hupper := le_rfl) (hlower := hlower) (hδsum := hδsum)
    (domain := domainInternal) («v» := v) (F := ((source).charts DE D).kernel) («j» := j)
    (hS := hsquarefree) (hfiber := hlive) (thetaPair := thetaPair)
    (cap := cap) (hcap := hcap) (slotLoss := slotLoss) (loss := finalLoss)
    (hslotLossNonneg := hslotLossNonneg) (hloss := hfinalLoss) (hslotLoss := hslotLoss)
    (hslots := hslots) (hstep := hstep.le) (hq := Q.fullSupportParameters_q_nonneg a Z hZ)
    (hone := hone) (hplaces := hplaces) (hsupport := hsupport)
    (hcutoffPaid := hcutoffPaid) (hcutoffPower := hcutoffPower₂) (hactiveColumns := hactive)
    (hwidth := hwidthInternal) (hthreshold := hthreshold) (hvolume := hvolume)
    (hDE := hDE) (horiginalColumns := hcolumns)
    (holdOriginal := literalPrimitiveFirstSource_oldSupport (Q := Q) (a := a) (Z := Z) (hZ := hZ))
    hcentered hpadding z

include originalWindow hrows htime hprime hamplitude hlo hhi hcap hY₁ hY₂ hlower hδsum href
  hslotLossNonneg hfinalLoss
  hslotLoss hslots hone hplaces hsupport hcutoffPower₂ hsquarefree hlive in
/-- The actual ordinary left main source uses its original
primitive row and column windows, including the original full support. -/
theorem literalPrimitiveLeftMainOrdinaryExceptional_pointwise
    (hcentered : centered = false)
    (thetaPair : (data ξ).theta × (data ξ).theta) (z : ℝ × ℝ) :
    ((outer).thetaClassLeaf characters thetaPair).exceptionalIntegrand z / allowance ≤
      (hi ^ cap * orbitalFieldFactor K * ((Γ₀).index : ℝ) * fixedCoefficient) *
        originalBound ^ degree *
        (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ heightOrder *
        Z ^ (3 * step + finalLoss / 2 + movingCost) / radical *
        Z ^ (-idealLogLength Z j.1.val) := by
  have hactive : ∀ i ∈ ((((source).pools DE D).divisorPools.leftData S).mainSource (((source).pools DE D).leftDivisorCoefficient S χ)).columns,
      ((((source).pools DE D).divisorPools.leftData S).mainSource (((source).pools DE D).leftDivisorCoefficient S χ)).coefficient i ≠ 0 →
      A.exteriorNorm (((((source).pools DE D).divisorPools.leftData S).mainSource (((source).pools DE D).leftDivisorCoefficient S χ)).ideal i) ≤
        Z ^ ((first).skeleton.A - (first).skeleton.c - (first).skeleton.w + loss) := by
    intro i hcol hci
    change A.exteriorNorm (((((source).pools DE D).divisorPools.leftData S).mainSource (((source).pools DE D).leftDivisorCoefficient S χ)).ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z -
        idealLogLength Z (((source).block DE).literalLeftCoordinates D.val).first.val - 0 + loss)
    rw [((source).block DE).literalLeftCoordinates_first, sub_zero]
    exact literalPrimitiveLeftMain_active_norm
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
      (pool := pool) (hdensity := hdensity) DE D S χ i hcol hci
  have hcutoffPaid : CanonicalLiteralExceptionalGeometry.paidCutoff loss cutoffExponent 0 / 6 ≤
      finalLoss / 16 := by
    unfold CanonicalLiteralExceptionalGeometry.paidCutoff
    linarith
  exact literalLeftMainOrdinaryExceptional_pointwise
    (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := (source).block DE) (C := C)
    (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ) (hDiff := hDiff)
    (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (step := step) («supportError» := supportError) («hsupportError» := hsupportError)
    (lo := lo) (hi := hi) (hlo := hlo) (primitive := primitive)
    (ε := ε) (widthMax := widthMax) (columnLoss := loss) (cutoffExponent := cutoffExponent)
    (hε := hε) (hwidthMax := hwidthMax) (hcolumnLoss := hloss) (hcutoffExponent := hcutoffExponent)
    (originalBound := originalBound) (annulus := hi) (hamplitude := hamplitude) (hannulus := hhi)
    (reference := reference) (href := by
      simpa only [Q.literalPrimitiveFirstSource_pairedRows] using href)
    (originalWindow := originalWindow) (hreference := hrows reference href) (htime := htime)
    (hprime := hprime) (hupper := le_rfl) (hlower := hlower) (hδsum := hδsum)
    (domain := domainInternal) («v» := v) (F := ((source).charts DE D).kernel) («j» := j)
    (hS := hsquarefree) (hfiber := hlive) (thetaPair := thetaPair)
    (cap := cap) (hcap := hcap) (slotLoss := slotLoss) (loss := finalLoss)
    (hslotLossNonneg := hslotLossNonneg) (hloss := hfinalLoss) (hslotLoss := hslotLoss)
    (hslots := hslots) (hstep := hstep.le) (hq := Q.fullSupportParameters_q_nonneg a Z hZ)
    (hone := hone) (hplaces := hplaces) (hsupport := hsupport)
    (hcutoffPaid := hcutoffPaid) (hcutoffPower := hcutoffPower₂) (hactiveColumns := hactive)
    hcentered z

end LeftMain

section LeftPool

variable (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
variable (S : divisorPool ((source).pools DE D).rightData.columns
  (fun j => (((source).pools DE D).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)
variable (valuation : AmplifierValuation) (prime : pool.primes)
local notation "first" => OriginalNominalGeometry.canonicalPoolError
  (a := internal) pool valuation prime (((source).block DE).literalLeftCoordinates D.val)
  supportError hsupportError
local notation "rowWindow" => (((source).pools DE D).divisorPools.leftData S).literalPoolRows
  internal (((source).block DE).literalLeftCoordinates D.val) supportError hsupportError
  hstep (leftRows DE D S) valuation prime
local notation "stage" => (((source).pools DE D).divisorPools.leftData S).literalValuationStage
  (hΓ := hΓ₀) (μv := μv) (hDiff := hDiff) (ν := ν)
  (((source).pools DE D).leftDivisorCoefficient S χ) P internal
  (((source).block DE).literalLeftCoordinates D.val) supportError hsupportError
  hstep (leftRows DE D S) δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ valuation prime
local notation "cover" => (((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual prime valuation.multiplicity
local notation "point" => (fun i => ((source).charts DE D).leftPoint i.val)
local notation "movingCost" => (amplifierMovingExponent valuation.multiplicity : ℝ) *
  idealLogLength Z prime.val.val.asIdeal
local notation "firstFixed" => ((source).block DE).literalLeftFixed D.val
local notation "hfirst" => ((source).block DE).literalLeftFixed_generates C D.val
local notation "phases" => CanonicalLiteralActualCharacters.amplifiedPhases C
  firstFixed (CanonicalLiteralFirstPhase.leftElement C ((source).block DE).primes
    ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst prime.val valuation.multiplicity
local notation "predicate" => (stage).supported.gated.literalHybridPredicates
  cover cover P R phases Q.moving Q.correction (data ξ).theta
variable (leaf : (stage).supported.gated.CoveredLeafKey cover cover)
variable (hsquarefree : Squarefree S.val)
variable (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover predicate
  ((source).charts DE D).kernel point leaf).Live)
local notation "v" => leaf.1
local notation "j" => leaf.2
local notation "bareLive" => ((v).leaf predicate ((source).charts DE D).kernel point j).live_of_scale_live _ _ hlive
local notation "construction" => literalLeftPoolExceptionalExtraction
    (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := (source).block DE) (C := C)
    (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ) (hDiff := hDiff)
    (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (retainedScale := (first).retainedScale) (g := (first).enlargement) (hscale := (first).retainedScale_pos)
    (domain := domainInternal) («v» := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
    («firstFixed» := firstFixed) («hfirst» := hfirst) («j» := j) (hS := hsquarefree)
    (q := prime) (n := valuation.multiplicity) (hlive := hlive)
local notation "oldLeftAtoms" => literalLeftPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ firstFixed hfirst δ₂ prime valuation.multiplicity v.2.2.1
local notation "oldRightAtoms" => literalLeftPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ firstFixed hfirst δ₂ prime valuation.multiplicity v.2.2.2.1
local notation "leftScalar" => literalLeftPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ prime valuation.multiplicity v.2.2.1 * ((oldLeftAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => literalLeftPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ prime valuation.multiplicity v.2.2.2.1 * ((oldRightAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rawRows" => (v).chart.actualRows ∅ cutoff₂ hcutoff₂ (v).rowLabel
local notation "characters" => (rawRows).literalFiniteCharacters C P R phases Q.moving Q.correction
  ((v).chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ (v).rowLabel)
  ((v).chart.originalSector P ∅ cutoff₂ hcutoff₂ (v).rowLabel) (data ξ).theta
local notation "outer" => (construction).val.stripOuter leftScalar rightScalar
  (construction).property.2.1 (construction).property.2.2
local notation "allowance" => firstLeftAllowance Z
  ((first).skeleton.A + ((first).skeleton.q + (first).skeleton.R + (first).skeleton.E))
  (first).ideals.first.val (first).ideals.opposite.val
local notation "radical" => (Ideal.absNorm (commonRadical
  (primePowerProduct (v).block.primes (v).block.leftMultiplicity).val
  (primePowerProduct (v).block.primes (v).block.rightMultiplicity).val) : ℝ)

include originalWindow hrows htime hprime hamplitude hlo hhi hcap hY₁ hY₂ hlower hδsum href
  hslotLossNonneg hfinalLoss
  hslotLoss hslots hone hplaces hsupport hcutoffPower₂ hsquarefree hlive hwidth hthreshold hvolume hfirstBox in
/-- The actual centered left valuation source uses its original
primitive row and column windows, including the original full support. -/
theorem literalPrimitiveLeftPoolExceptional_pointwise
    (hcentered : centered = true) (hpadding : 0 ≤ padding)
    (thetaPair : (data ξ).theta × (data ξ).theta) (z : ℝ × ℝ) :
    ((outer).thetaClassLeaf characters thetaPair).exceptionalIntegrand z / allowance ≤
      (hi ^ cap * orbitalFieldFactor K * ((Γ₀).index : ℝ) * fixedCoefficient) *
        originalBound ^ degree *
        (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ heightOrder *
        Z ^ (padding + 3 * step + finalLoss / 2 + movingCost) / radical *
        Z ^ (-idealLogLength Z j.1.val) := by
  have hactive : ∀ i ∈ ((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ)).columns,
      ((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ)).coefficient i ≠ 0 →
      A.exteriorNorm (((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ)).ideal i) ≤
        Z ^ ((first).skeleton.A - (first).skeleton.c - (first).skeleton.w + loss) := by
    intro i hcol hci
    change A.exteriorNorm (((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ)).ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z -
        idealLogLength Z (((source).block DE).literalLeftCoordinates D.val).first.val -
        (valuation.multiplicity : ℝ) * idealLogLength Z prime.val.val.asIdeal + loss)
    rw [((source).block DE).literalLeftCoordinates_first]
    have hremoved := idealLogLength_pow Z prime.val.val.asIdeal valuation.multiplicity
    rw [← hremoved]
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
  have hcutoffPaid : CanonicalLiteralExceptionalGeometry.paidCutoff loss cutoffExponent 0 / 6 ≤
      finalLoss / 16 := by
    unfold CanonicalLiteralExceptionalGeometry.paidCutoff
    linarith
  have hwidthInternal : (internal).m + (internal).q ≤ widthMax := by
    simpa only [Q.fullSupportParameters_width] using hwidth
  have hDE : DE.val ∈ commonSupportPool (raw).exteriorColumns (raw).exteriorColumns
      (fun i => ((raw).columnExterior i).val) (fun i => ((raw).columnExterior i).val) := DE.property
  exact literalLeftPoolExceptional_pointwise
    (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := (source).block DE) (C := C)
    (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ) (hDiff := hDiff)
    (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (step := step) («supportError» := supportError) («hsupportError» := hsupportError)
    (lo := lo) (hi := hi) (hlo := hlo) (primitive := primitive)
    (ε := ε) (widthMax := widthMax) (columnLoss := loss) (cutoffExponent := cutoffExponent)
    (hε := hε) (hwidthMax := hwidthMax) (hcolumnLoss := hloss) (hcutoffExponent := hcutoffExponent)
    (originalBound := originalBound) (annulus := hi) (hamplitude := hamplitude) (hannulus := hhi)
    (reference := reference) (href := by
      simpa only [Q.literalPrimitiveFirstSource_pairedRows] using href)
    (originalWindow := originalWindow) (hreference := hrows reference href) (htime := htime)
    (hprime := hprime) (hupper := le_rfl) (hlower := hlower) (hδsum := hδsum)
    (domain := domainInternal) («v» := v) (F := ((source).charts DE D).kernel) («j» := j)
    (hS := hsquarefree) (hfiber := hlive) (thetaPair := thetaPair)
    (cap := cap) (hcap := hcap) (slotLoss := slotLoss) (loss := finalLoss)
    (hslotLossNonneg := hslotLossNonneg) (hloss := hfinalLoss) (hslotLoss := hslotLoss)
    (hslots := hslots) (hstep := hstep.le) (hq := Q.fullSupportParameters_q_nonneg a Z hZ)
    (hone := hone) (hplaces := hplaces) (hsupport := hsupport)
    (hcutoffPaid := hcutoffPaid) (hcutoffPower := hcutoffPower₂) (hactiveColumns := hactive)
    (e := valuation) (q := prime)
    (hwidth := hwidthInternal) (hthreshold := hthreshold) (hvolume := hvolume)
    (hDE := hDE) (horiginalColumns := hN)
    (holdOriginal := literalPrimitiveFirstSource_oldSupport (Q := Q) (a := a) (Z := Z) (hZ := hZ))
    (firstColumnBound := columnBound) (hfirstBox := hfirstBox)
    hcentered hpadding z

include originalWindow hrows htime hprime hamplitude hlo hhi hcap hY₁ hY₂ hlower hδsum href
  hslotLossNonneg hfinalLoss
  hslotLoss hslots hone hplaces hsupport hcutoffPower₂ hsquarefree hlive in
/-- The actual ordinary left valuation source uses its original
primitive row and column windows, including the original full support. -/
theorem literalPrimitiveLeftPoolOrdinaryExceptional_pointwise
    (hcentered : centered = false)
    (thetaPair : (data ξ).theta × (data ξ).theta) (z : ℝ × ℝ) :
    ((outer).thetaClassLeaf characters thetaPair).exceptionalIntegrand z / allowance ≤
      (hi ^ cap * orbitalFieldFactor K * ((Γ₀).index : ℝ) * fixedCoefficient) *
        originalBound ^ degree *
        (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ heightOrder *
        Z ^ (3 * step + finalLoss / 2 + movingCost) / radical *
        Z ^ (-idealLogLength Z j.1.val) := by
  have hactive : ∀ i ∈ ((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ)).columns,
      ((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ)).coefficient i ≠ 0 →
      A.exteriorNorm (((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ)).ideal i) ≤
        Z ^ ((first).skeleton.A - (first).skeleton.c - (first).skeleton.w + loss) := by
    intro i hcol hci
    change A.exteriorNorm (((((source).pools DE D).divisorPools.leftData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).leftDivisorCoefficient S χ)).ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z -
        idealLogLength Z (((source).block DE).literalLeftCoordinates D.val).first.val -
        (valuation.multiplicity : ℝ) * idealLogLength Z prime.val.val.asIdeal + loss)
    rw [((source).block DE).literalLeftCoordinates_first]
    have hremoved := idealLogLength_pow Z prime.val.val.asIdeal valuation.multiplicity
    rw [← hremoved]
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
  have hcutoffPaid : CanonicalLiteralExceptionalGeometry.paidCutoff loss cutoffExponent 0 / 6 ≤
      finalLoss / 16 := by
    unfold CanonicalLiteralExceptionalGeometry.paidCutoff
    linarith
  exact literalLeftPoolOrdinaryExceptional_pointwise
    (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := (source).block DE) (C := C)
    (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ) (hDiff := hDiff)
    (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (step := step) («supportError» := supportError) («hsupportError» := hsupportError)
    (lo := lo) (hi := hi) (hlo := hlo) (primitive := primitive)
    (ε := ε) (widthMax := widthMax) (columnLoss := loss) (cutoffExponent := cutoffExponent)
    (hε := hε) (hwidthMax := hwidthMax) (hcolumnLoss := hloss) (hcutoffExponent := hcutoffExponent)
    (originalBound := originalBound) (annulus := hi) (hamplitude := hamplitude) (hannulus := hhi)
    (reference := reference) (href := by
      simpa only [Q.literalPrimitiveFirstSource_pairedRows] using href)
    (originalWindow := originalWindow) (hreference := hrows reference href) (htime := htime)
    (hprime := hprime) (hupper := le_rfl) (hlower := hlower) (hδsum := hδsum)
    (domain := domainInternal) («v» := v) (F := ((source).charts DE D).kernel) («j» := j)
    (hS := hsquarefree) (hfiber := hlive) (thetaPair := thetaPair)
    (cap := cap) (hcap := hcap) (slotLoss := slotLoss) (loss := finalLoss)
    (hslotLossNonneg := hslotLossNonneg) (hloss := hfinalLoss) (hslotLoss := hslotLoss)
    (hslots := hslots) (hstep := hstep.le) (hq := Q.fullSupportParameters_q_nonneg a Z hZ)
    (hone := hone) (hplaces := hplaces) (hsupport := hsupport)
    (hcutoffPaid := hcutoffPaid) (hcutoffPower := hcutoffPower₂) (hactiveColumns := hactive)
    (e := valuation) (q := prime)
    hcentered z

end LeftPool

section RightMain

variable (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
variable (S : divisorPool ((source).pools DE D).rightData.columns
  (fun j => (((source).pools DE D).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)
local notation "first" => OriginalNominalGeometry.canonicalMain
  (a := internal) (Z := Z) (step := step) (((source).block DE).literalRightCoordinates D.val)
  supportError (zero_lt_one.trans hZ) hsupportError
local notation "rowWindow" => (((source).pools DE D).divisorPools.rightData S).literalMainRows
  internal (((source).block DE).literalRightCoordinates D.val) supportError hsupportError
  hstep (rightRows DE D S)
local notation "stage" => ((stages DE D).right S χ).main
local notation "cover" => (((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).main
local notation "point" =>
  (fun i => Real.log (A.exteriorNorm (((source).block DE).rightResidual i)))
local notation "movingCost" => step / 3
local notation "firstFixed" => ((source).block DE).literalRightFixed D.val
local notation "hfirst" => ((source).block DE).literalRightFixed_generates C D.val
local notation "phases" => CanonicalLiteralActualCharacters.unamplifiedPhases
  firstFixed (CanonicalLiteralFirstPhase.rightElement C ((source).block DE).primes
    ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst
local notation "predicate" => (stage).supported.gated.literalHybridPredicates
  cover cover P R phases Q.moving Q.correction (data ξ).theta
variable (leaf : (stage).supported.gated.CoveredLeafKey cover cover)
variable (hsquarefree : Squarefree S.val)
variable (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover predicate
  ((source).charts DE D).kernel point leaf).Live)
local notation "v" => leaf.1
local notation "j" => leaf.2
local notation "bareLive" => ((v).leaf predicate ((source).charts DE D).kernel point j).live_of_scale_live _ _ hlive
local notation "construction" => literalRightMainExceptionalExtraction
    (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := (source).block DE) (C := C)
    (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ) (hDiff := hDiff)
    (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (retainedScale := (first).retainedScale) (g := (first).enlargement) (hscale := (first).retainedScale_pos)
    (domain := domainInternal) («v» := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
    («firstFixed» := firstFixed) («hfirst» := hfirst) («j» := j) (hS := hsquarefree)
    (hlive := bareLive)
local notation "oldLeftAtoms" => literalRightMainAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ firstFixed hfirst δ₂ v.2.2.1
local notation "oldRightAtoms" => literalRightMainAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ firstFixed hfirst δ₂ v.2.2.2.1
local notation "leftScalar" => literalRightMainScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ v.2.2.1 * ((oldLeftAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => literalRightMainScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ v.2.2.2.1 * ((oldRightAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rawRows" => (v).chart.actualRows ∅ cutoff₂ hcutoff₂ (v).rowLabel
local notation "characters" => (rawRows).literalFiniteCharacters C P R phases Q.moving Q.correction
  ((v).chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ (v).rowLabel)
  ((v).chart.originalSector P ∅ cutoff₂ hcutoff₂ (v).rowLabel) (data ξ).theta
local notation "outer" => (construction).val.stripOuter leftScalar rightScalar
  (construction).property.2.1 (construction).property.2.2
local notation "allowance" => firstLeftAllowance Z
  ((first).skeleton.A + ((first).skeleton.q + (first).skeleton.R + (first).skeleton.E))
  (first).ideals.first.val (first).ideals.opposite.val
local notation "radical" => (Ideal.absNorm (commonRadical
  (primePowerProduct (v).block.primes (v).block.leftMultiplicity).val
  (primePowerProduct (v).block.primes (v).block.rightMultiplicity).val) : ℝ)

include originalWindow hrows htime hprime hamplitude hlo hhi hcap hY₁ hY₂ hlower hδsum href
  hslotLossNonneg hfinalLoss
  hslotLoss hslots hone hplaces hsupport hcutoffPower₂ hsquarefree hlive hwidth hthreshold hvolume hfirstBox in
/-- The actual centered right main source uses its original
primitive row and column windows, including the original full support. -/
theorem literalPrimitiveRightMainExceptional_pointwise
    (hcentered : centered = true) (hpadding : 0 ≤ padding)
    (thetaPair : (data ξ).theta × (data ξ).theta) (z : ℝ × ℝ) :
    ((outer).thetaClassLeaf characters thetaPair).exceptionalIntegrand z / allowance ≤
      (hi ^ cap * orbitalFieldFactor K * ((Γ₀).index : ℝ) * fixedCoefficient) *
        originalBound ^ degree *
        (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ heightOrder *
        Z ^ (padding + 3 * step + finalLoss / 2 + movingCost) / radical *
        Z ^ (-idealLogLength Z j.1.val) := by
  have hactive : ∀ i ∈ ((((source).pools DE D).divisorPools.rightData S).mainSource (((source).pools DE D).rightDivisorCoefficient S χ)).columns,
      ((((source).pools DE D).divisorPools.rightData S).mainSource (((source).pools DE D).rightDivisorCoefficient S χ)).coefficient i ≠ 0 →
      A.exteriorNorm (((((source).pools DE D).divisorPools.rightData S).mainSource (((source).pools DE D).rightDivisorCoefficient S χ)).ideal i) ≤
        Z ^ ((first).skeleton.A - (first).skeleton.c - (first).skeleton.w + loss) := by
    intro i hcol hci
    change A.exteriorNorm (((((source).pools DE D).divisorPools.rightData S).mainSource (((source).pools DE D).rightDivisorCoefficient S χ)).ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z -
        idealLogLength Z (((source).block DE).literalRightCoordinates D.val).first.val - 0 + loss)
    rw [((source).block DE).literalRightCoordinates_first, sub_zero]
    exact literalPrimitiveRightMain_active_norm
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
      (pool := pool) (hdensity := hdensity) DE D S χ i hcol hci
  have hcutoffPaid : CanonicalLiteralExceptionalGeometry.paidCutoff loss cutoffExponent 0 / 6 ≤
      finalLoss / 16 := by
    unfold CanonicalLiteralExceptionalGeometry.paidCutoff
    linarith
  have hwidthInternal : (internal).m + (internal).q ≤ widthMax := by
    simpa only [Q.fullSupportParameters_width] using hwidth
  have hDE : DE.val ∈ commonSupportPool (raw).exteriorColumns (raw).exteriorColumns
      (fun i => ((raw).columnExterior i).val) (fun i => ((raw).columnExterior i).val) := DE.property
  have hcolumns : ∀ i ∈ (raw).exteriorColumns,
      A.exteriorNorm ((raw).columnExterior i) ≤ Z ^ widthMax := by
    intro i hi
    exact (hN i hi).trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [hstep.le]))
  exact literalRightMainExceptional_pointwise
    (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := (source).block DE) (C := C)
    (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ) (hDiff := hDiff)
    (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (step := step) («supportError» := supportError) («hsupportError» := hsupportError)
    (lo := lo) (hi := hi) (hlo := hlo) (primitive := primitive)
    (ε := ε) (widthMax := widthMax) (columnLoss := loss) (cutoffExponent := cutoffExponent)
    (hε := hε) (hwidthMax := hwidthMax) (hcolumnLoss := hloss) (hcutoffExponent := hcutoffExponent)
    (originalBound := originalBound) (annulus := hi) (hamplitude := hamplitude) (hannulus := hhi)
    (reference := reference) (href := by
      simpa only [Q.literalPrimitiveFirstSource_pairedRows] using href)
    (originalWindow := originalWindow) (hreference := hrows reference href) (htime := htime)
    (hprime := hprime) (hupper := le_rfl) (hlower := hlower) (hδsum := hδsum)
    (domain := domainInternal) («v» := v) (F := ((source).charts DE D).kernel) («j» := j)
    (hS := hsquarefree) (hfiber := hlive) (thetaPair := thetaPair)
    (cap := cap) (hcap := hcap) (slotLoss := slotLoss) (loss := finalLoss)
    (hslotLossNonneg := hslotLossNonneg) (hloss := hfinalLoss) (hslotLoss := hslotLoss)
    (hslots := hslots) (hstep := hstep.le) (hq := Q.fullSupportParameters_q_nonneg a Z hZ)
    (hone := hone) (hplaces := hplaces) (hsupport := hsupport)
    (hcutoffPaid := hcutoffPaid) (hcutoffPower := hcutoffPower₂) (hactiveColumns := hactive)
    (hwidth := hwidthInternal) (hthreshold := hthreshold) (hvolume := hvolume)
    (hDE := hDE) (horiginalColumns := hcolumns)
    (holdOriginal := literalPrimitiveFirstSource_oldSupport (Q := Q) (a := a) (Z := Z) (hZ := hZ))
    hcentered hpadding z

include originalWindow hrows htime hprime hamplitude hlo hhi hcap hY₁ hY₂ hlower hδsum href
  hslotLossNonneg hfinalLoss
  hslotLoss hslots hone hplaces hsupport hcutoffPower₂ hsquarefree hlive in
/-- The actual ordinary right main source uses its original
primitive row and column windows, including the original full support. -/
theorem literalPrimitiveRightMainOrdinaryExceptional_pointwise
    (hcentered : centered = false)
    (thetaPair : (data ξ).theta × (data ξ).theta) (z : ℝ × ℝ) :
    ((outer).thetaClassLeaf characters thetaPair).exceptionalIntegrand z / allowance ≤
      (hi ^ cap * orbitalFieldFactor K * ((Γ₀).index : ℝ) * fixedCoefficient) *
        originalBound ^ degree *
        (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ heightOrder *
        Z ^ (3 * step + finalLoss / 2 + movingCost) / radical *
        Z ^ (-idealLogLength Z j.1.val) := by
  have hactive : ∀ i ∈ ((((source).pools DE D).divisorPools.rightData S).mainSource (((source).pools DE D).rightDivisorCoefficient S χ)).columns,
      ((((source).pools DE D).divisorPools.rightData S).mainSource (((source).pools DE D).rightDivisorCoefficient S χ)).coefficient i ≠ 0 →
      A.exteriorNorm (((((source).pools DE D).divisorPools.rightData S).mainSource (((source).pools DE D).rightDivisorCoefficient S χ)).ideal i) ≤
        Z ^ ((first).skeleton.A - (first).skeleton.c - (first).skeleton.w + loss) := by
    intro i hcol hci
    change A.exteriorNorm (((((source).pools DE D).divisorPools.rightData S).mainSource (((source).pools DE D).rightDivisorCoefficient S χ)).ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z -
        idealLogLength Z (((source).block DE).literalRightCoordinates D.val).first.val - 0 + loss)
    rw [((source).block DE).literalRightCoordinates_first, sub_zero]
    exact literalPrimitiveRightMain_active_norm
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
      (pool := pool) (hdensity := hdensity) DE D S χ i hcol hci
  have hcutoffPaid : CanonicalLiteralExceptionalGeometry.paidCutoff loss cutoffExponent 0 / 6 ≤
      finalLoss / 16 := by
    unfold CanonicalLiteralExceptionalGeometry.paidCutoff
    linarith
  exact literalRightMainOrdinaryExceptional_pointwise
    (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := (source).block DE) (C := C)
    (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ) (hDiff := hDiff)
    (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (step := step) («supportError» := supportError) («hsupportError» := hsupportError)
    (lo := lo) (hi := hi) (hlo := hlo) (primitive := primitive)
    (ε := ε) (widthMax := widthMax) (columnLoss := loss) (cutoffExponent := cutoffExponent)
    (hε := hε) (hwidthMax := hwidthMax) (hcolumnLoss := hloss) (hcutoffExponent := hcutoffExponent)
    (originalBound := originalBound) (annulus := hi) (hamplitude := hamplitude) (hannulus := hhi)
    (reference := reference) (href := by
      simpa only [Q.literalPrimitiveFirstSource_pairedRows] using href)
    (originalWindow := originalWindow) (hreference := hrows reference href) (htime := htime)
    (hprime := hprime) (hupper := le_rfl) (hlower := hlower) (hδsum := hδsum)
    (domain := domainInternal) («v» := v) (F := ((source).charts DE D).kernel) («j» := j)
    (hS := hsquarefree) (hfiber := hlive) (thetaPair := thetaPair)
    (cap := cap) (hcap := hcap) (slotLoss := slotLoss) (loss := finalLoss)
    (hslotLossNonneg := hslotLossNonneg) (hloss := hfinalLoss) (hslotLoss := hslotLoss)
    (hslots := hslots) (hstep := hstep.le) (hq := Q.fullSupportParameters_q_nonneg a Z hZ)
    (hone := hone) (hplaces := hplaces) (hsupport := hsupport)
    (hcutoffPaid := hcutoffPaid) (hcutoffPower := hcutoffPower₂) (hactiveColumns := hactive)
    hcentered z

end RightMain

section RightPool

variable (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
variable (S : divisorPool ((source).pools DE D).rightData.columns
  (fun j => (((source).pools DE D).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)
variable (valuation : AmplifierValuation) (prime : pool.primes)
local notation "first" => OriginalNominalGeometry.canonicalPoolError
  (a := internal) pool valuation prime (((source).block DE).literalRightCoordinates D.val)
  supportError hsupportError
local notation "rowWindow" => (((source).pools DE D).divisorPools.rightData S).literalPoolRows
  internal (((source).block DE).literalRightCoordinates D.val) supportError hsupportError
  hstep (rightRows DE D S) valuation prime
local notation "stage" => (((source).pools DE D).divisorPools.rightData S).literalValuationStage
  (hΓ := hΓ₀) (μv := μv) (hDiff := hDiff) (ν := ν)
  (((source).pools DE D).rightDivisorCoefficient S χ) P internal
  (((source).block DE).literalRightCoordinates D.val) supportError hsupportError
  hstep (rightRows DE D S) δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ valuation prime
local notation "cover" => (((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual prime valuation.multiplicity
local notation "point" =>
  (fun i => Real.log (A.exteriorNorm (((source).block DE).rightResidual i.val)))
local notation "movingCost" => (amplifierMovingExponent valuation.multiplicity : ℝ) *
  idealLogLength Z prime.val.val.asIdeal
local notation "firstFixed" => ((source).block DE).literalRightFixed D.val
local notation "hfirst" => ((source).block DE).literalRightFixed_generates C D.val
local notation "phases" => CanonicalLiteralActualCharacters.amplifiedPhases C
  firstFixed (CanonicalLiteralFirstPhase.rightElement C ((source).block DE).primes
    ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst prime.val valuation.multiplicity
local notation "predicate" => (stage).supported.gated.literalHybridPredicates
  cover cover P R phases Q.moving Q.correction (data ξ).theta
variable (leaf : (stage).supported.gated.CoveredLeafKey cover cover)
variable (hsquarefree : Squarefree S.val)
variable (hlive : ((stage).supported.gated.fiberCoveredLeaf cover cover predicate
  ((source).charts DE D).kernel point leaf).Live)
local notation "v" => leaf.1
local notation "j" => leaf.2
local notation "bareLive" => ((v).leaf predicate ((source).charts DE D).kernel point j).live_of_scale_live _ _ hlive
local notation "construction" => literalRightPoolExceptionalExtraction
    (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := (source).block DE) (C := C)
    (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ) (hDiff := hDiff)
    (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (retainedScale := (first).retainedScale) (g := (first).enlargement) (hscale := (first).retainedScale_pos)
    (domain := domainInternal) («v» := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
    («firstFixed» := firstFixed) («hfirst» := hfirst) («j» := j) (hS := hsquarefree)
    (q := prime) (n := valuation.multiplicity) (hlive := hlive)
local notation "oldLeftAtoms" => literalRightPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ firstFixed hfirst δ₂ prime valuation.multiplicity v.2.2.1
local notation "oldRightAtoms" => literalRightPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ firstFixed hfirst δ₂ prime valuation.multiplicity v.2.2.2.1
local notation "leftScalar" => literalRightPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ prime valuation.multiplicity v.2.2.1 * ((oldLeftAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => literalRightPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
  Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
  (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
  (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
  ((source).pools DE D) S χ prime valuation.multiplicity v.2.2.2.1 * ((oldRightAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rawRows" => (v).chart.actualRows ∅ cutoff₂ hcutoff₂ (v).rowLabel
local notation "characters" => (rawRows).literalFiniteCharacters C P R phases Q.moving Q.correction
  ((v).chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ (v).rowLabel)
  ((v).chart.originalSector P ∅ cutoff₂ hcutoff₂ (v).rowLabel) (data ξ).theta
local notation "outer" => (construction).val.stripOuter leftScalar rightScalar
  (construction).property.2.1 (construction).property.2.2
local notation "allowance" => firstLeftAllowance Z
  ((first).skeleton.A + ((first).skeleton.q + (first).skeleton.R + (first).skeleton.E))
  (first).ideals.first.val (first).ideals.opposite.val
local notation "radical" => (Ideal.absNorm (commonRadical
  (primePowerProduct (v).block.primes (v).block.leftMultiplicity).val
  (primePowerProduct (v).block.primes (v).block.rightMultiplicity).val) : ℝ)

include originalWindow hrows htime hprime hamplitude hlo hhi hcap hY₁ hY₂ hlower hδsum href
  hslotLossNonneg hfinalLoss
  hslotLoss hslots hone hplaces hsupport hcutoffPower₂ hsquarefree hlive hwidth hthreshold hvolume hfirstBox in
/-- The actual centered right valuation source uses its original
primitive row and column windows, including the original full support. -/
theorem literalPrimitiveRightPoolExceptional_pointwise
    (hcentered : centered = true) (hpadding : 0 ≤ padding)
    (thetaPair : (data ξ).theta × (data ξ).theta) (z : ℝ × ℝ) :
    ((outer).thetaClassLeaf characters thetaPair).exceptionalIntegrand z / allowance ≤
      (hi ^ cap * orbitalFieldFactor K * ((Γ₀).index : ℝ) * fixedCoefficient) *
        originalBound ^ degree *
        (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ heightOrder *
        Z ^ (padding + 3 * step + finalLoss / 2 + movingCost) / radical *
        Z ^ (-idealLogLength Z j.1.val) := by
  have hactive : ∀ i ∈ ((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ)).columns,
      ((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ)).coefficient i ≠ 0 →
      A.exteriorNorm (((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ)).ideal i) ≤
        Z ^ ((first).skeleton.A - (first).skeleton.c - (first).skeleton.w + loss) := by
    intro i hcol hci
    change A.exteriorNorm (((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ)).ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z -
        idealLogLength Z (((source).block DE).literalRightCoordinates D.val).first.val -
        (valuation.multiplicity : ℝ) * idealLogLength Z prime.val.val.asIdeal + loss)
    rw [((source).block DE).literalRightCoordinates_first]
    have hremoved := idealLogLength_pow Z prime.val.val.asIdeal valuation.multiplicity
    rw [← hremoved]
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
  have hcutoffPaid : CanonicalLiteralExceptionalGeometry.paidCutoff loss cutoffExponent 0 / 6 ≤
      finalLoss / 16 := by
    unfold CanonicalLiteralExceptionalGeometry.paidCutoff
    linarith
  have hwidthInternal : (internal).m + (internal).q ≤ widthMax := by
    simpa only [Q.fullSupportParameters_width] using hwidth
  have hDE : DE.val ∈ commonSupportPool (raw).exteriorColumns (raw).exteriorColumns
      (fun i => ((raw).columnExterior i).val) (fun i => ((raw).columnExterior i).val) := DE.property
  exact literalRightPoolExceptional_pointwise
    (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := (source).block DE) (C := C)
    (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ) (hDiff := hDiff)
    (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (step := step) («supportError» := supportError) («hsupportError» := hsupportError)
    (lo := lo) (hi := hi) (hlo := hlo) (primitive := primitive)
    (ε := ε) (widthMax := widthMax) (columnLoss := loss) (cutoffExponent := cutoffExponent)
    (hε := hε) (hwidthMax := hwidthMax) (hcolumnLoss := hloss) (hcutoffExponent := hcutoffExponent)
    (originalBound := originalBound) (annulus := hi) (hamplitude := hamplitude) (hannulus := hhi)
    (reference := reference) (href := by
      simpa only [Q.literalPrimitiveFirstSource_pairedRows] using href)
    (originalWindow := originalWindow) (hreference := hrows reference href) (htime := htime)
    (hprime := hprime) (hupper := le_rfl) (hlower := hlower) (hδsum := hδsum)
    (domain := domainInternal) («v» := v) (F := ((source).charts DE D).kernel) («j» := j)
    (hS := hsquarefree) (hfiber := hlive) (thetaPair := thetaPair)
    (cap := cap) (hcap := hcap) (slotLoss := slotLoss) (loss := finalLoss)
    (hslotLossNonneg := hslotLossNonneg) (hloss := hfinalLoss) (hslotLoss := hslotLoss)
    (hslots := hslots) (hstep := hstep.le) (hq := Q.fullSupportParameters_q_nonneg a Z hZ)
    (hone := hone) (hplaces := hplaces) (hsupport := hsupport)
    (hcutoffPaid := hcutoffPaid) (hcutoffPower := hcutoffPower₂) (hactiveColumns := hactive)
    (e := valuation) (q := prime)
    (hwidth := hwidthInternal) (hthreshold := hthreshold) (hvolume := hvolume)
    (hDE := hDE) (horiginalColumns := hN)
    (holdOriginal := literalPrimitiveFirstSource_oldSupport (Q := Q) (a := a) (Z := Z) (hZ := hZ))
    (firstColumnBound := columnBound) (hfirstBox := hfirstBox)
    hcentered hpadding z

include originalWindow hrows htime hprime hamplitude hlo hhi hcap hY₁ hY₂ hlower hδsum href
  hslotLossNonneg hfinalLoss
  hslotLoss hslots hone hplaces hsupport hcutoffPower₂ hsquarefree hlive in
/-- The actual ordinary right valuation source uses its original
primitive row and column windows, including the original full support. -/
theorem literalPrimitiveRightPoolOrdinaryExceptional_pointwise
    (hcentered : centered = false)
    (thetaPair : (data ξ).theta × (data ξ).theta) (z : ℝ × ℝ) :
    ((outer).thetaClassLeaf characters thetaPair).exceptionalIntegrand z / allowance ≤
      (hi ^ cap * orbitalFieldFactor K * ((Γ₀).index : ℝ) * fixedCoefficient) *
        originalBound ^ degree *
        (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ heightOrder *
        Z ^ (3 * step + finalLoss / 2 + movingCost) / radical *
        Z ^ (-idealLogLength Z j.1.val) := by
  have hactive : ∀ i ∈ ((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ)).columns,
      ((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ)).coefficient i ≠ 0 →
      A.exteriorNorm (((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ)).ideal i) ≤
        Z ^ ((first).skeleton.A - (first).skeleton.c - (first).skeleton.w + loss) := by
    intro i hcol hci
    change A.exteriorNorm (((((source).pools DE D).divisorPools.rightData S).residualSource prime.val valuation.multiplicity (((source).pools DE D).rightDivisorCoefficient S χ)).ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z -
        idealLogLength Z (((source).block DE).literalRightCoordinates D.val).first.val -
        (valuation.multiplicity : ℝ) * idealLogLength Z prime.val.val.asIdeal + loss)
    rw [((source).block DE).literalRightCoordinates_first]
    have hremoved := idealLogLength_pow Z prime.val.val.asIdeal valuation.multiplicity
    rw [← hremoved]
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
  have hcutoffPaid : CanonicalLiteralExceptionalGeometry.paidCutoff loss cutoffExponent 0 / 6 ≤
      finalLoss / 16 := by
    unfold CanonicalLiteralExceptionalGeometry.paidCutoff
    linarith
  exact literalRightPoolOrdinaryExceptional_pointwise
    (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := (source).block DE) (C := C)
    (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pools DE D) (S := S) (χ := χ) (hDiff := hDiff)
    (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
    (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
    (dyad := fun _ _ i => Fin.elim0 i)
    (step := step) («supportError» := supportError) («hsupportError» := hsupportError)
    (lo := lo) (hi := hi) (hlo := hlo) (primitive := primitive)
    (ε := ε) (widthMax := widthMax) (columnLoss := loss) (cutoffExponent := cutoffExponent)
    (hε := hε) (hwidthMax := hwidthMax) (hcolumnLoss := hloss) (hcutoffExponent := hcutoffExponent)
    (originalBound := originalBound) (annulus := hi) (hamplitude := hamplitude) (hannulus := hhi)
    (reference := reference) (href := by
      simpa only [Q.literalPrimitiveFirstSource_pairedRows] using href)
    (originalWindow := originalWindow) (hreference := hrows reference href) (htime := htime)
    (hprime := hprime) (hupper := le_rfl) (hlower := hlower) (hδsum := hδsum)
    (domain := domainInternal) («v» := v) (F := ((source).charts DE D).kernel) («j» := j)
    (hS := hsquarefree) (hfiber := hlive) (thetaPair := thetaPair)
    (cap := cap) (hcap := hcap) (slotLoss := slotLoss) (loss := finalLoss)
    (hslotLossNonneg := hslotLossNonneg) (hloss := hfinalLoss) (hslotLoss := hslotLoss)
    (hslots := hslots) (hstep := hstep.le) (hq := Q.fullSupportParameters_q_nonneg a Z hZ)
    (hone := hone) (hplaces := hplaces) (hsupport := hsupport)
    (hcutoffPaid := hcutoffPaid) (hcutoffPower := hcutoffPower₂) (hactiveColumns := hactive)
    (e := valuation) (q := prime)
    hcentered z

end RightPool

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooled_rightPoint_neg
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftMainExceptional_pointwise

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftMainOrdinaryExceptional_pointwise

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftPoolExceptional_pointwise

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftPoolOrdinaryExceptional_pointwise

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightMainExceptional_pointwise

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightMainOrdinaryExceptional_pointwise

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightPoolExceptional_pointwise

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightPoolOrdinaryExceptional_pointwise
