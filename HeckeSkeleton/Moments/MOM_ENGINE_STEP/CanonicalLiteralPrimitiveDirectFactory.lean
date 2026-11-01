import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectColumns
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectPassiveNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRowProfileBound
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CurriedNormalizedFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DependentNormalizedFamily

/-!
# The actual direct live-key dispatcher

The original moving recipe determines its first source, original atlas,
second stages, finite exceptional predicates and first normalizations.
Each live original left or right key supplies its own first phase,
second common pattern, physical row-profile bound and sharp columns.
The corresponding literal passive factory then constructs its finite
normalized family. Only the individual analytic certificates remain
curried; there is no supplied normalized family or source estimate.
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

/-- The original left direct case constructs its own passive family. -/
def literalPrimitiveLeftDirectFactory
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
    CurriedNormalizedFamily A σ (WithLp 2 (ℝ × ℝ)) ω ψ Z := by
  let baseGeometry := Q.literalPrimitiveLeftDirectGeometry
      (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
      (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
      (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
      (loss := loss) (cutoffExponent := cutoffExponent) (step := step)
      (hloss := hloss) (hcutoffExponent := hcutoffExponent) DE D
  let rowWindow := Q.literalPrimitiveLeftDirectRows
      (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
      (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
      (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
      (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
      (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
      (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
      (hcutoffPower := hcutoffPower) (step := step) (hstep := hstep)
      (hloss := hloss) (hcutoffExponent := hcutoffExponent) DE D
  let v := leaf.1
  let predicate := (exceptional DE D).left S χ
  let geometry := baseGeometry.atSecondPattern v.block.primes
    v.block.leftMultiplicity v.block.rightMultiplicity v.block.left_positive v.block.right_positive
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
  have hbare : (v.leaf predicate ((source).charts DE D).kernel ((source).charts DE D).leftPoint leaf.2).Live :=
    (v.leaf predicate ((source).charts DE D).kernel ((source).charts DE D).leftPoint leaf.2).live_of_scale_live _ _ hlive
  have hprofile := ActualGaussStage.canonicalSector_fiberLeaf_rowProfile_one
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (μv := μv) (hDiff := hDiff) (ν := ν)
    P δ₂ hδ₂ hδ₂half
    (((source).pieces DE D).leftData.directSource
      (((source).pieces DE D).leftDivisorCoefficient S χ))
    baseGeometry.retainedScale Z baseGeometry.enlargement
    baseGeometry.retainedScale_pos (zero_lt_one.trans hZ) cutoff₂ hcutoff₂ rowWindow
    0 0 (fun _ _ => (PUnit.unit : PUnit.{1})) (fun _ _ i => Fin.elim0 i)
    (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
    (((source).pieces DE D).leftSourceCover (raw).originalAtlas S χ)
    predicate ((source).charts DE D).kernel ((source).charts DE D).leftPoint leaf hlive
  have hfirstIdeal : geometry.ideals.first.val = DE.val.1 :=
    ((source).block DE).literalLeftCoordinates_first D.val
  have hoppositeIdeal : geometry.ideals.opposite.val = DE.val.2 :=
    ((source).block DE).literalLeftCoordinates_opposite D.val
  have hactive : ∀ i ∈ ((source).pieces DE D).leftData.columns,
      ((source).pieces DE D).leftDivisorCoefficient S χ i ≠ 0 →
      A.exteriorNorm (((source).pieces DE D).leftData.ideal i) ≤
        Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + loss) := by
    intro i hcol hci
    change A.exteriorNorm (((source).pieces DE D).leftData.ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z -
        idealLogLength Z geometry.ideals.first.val - 0 + loss)
    rw [hfirstIdeal, sub_zero]
    exact literalPrimitiveDirectLeft_active_norm
      (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
      (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
      (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
      (cap := cap) (annulus := hi) (loss := loss) (hannulus := hhi) (hcap := hcap)
      (hannulusZ := hannulusZ) (domain := domain) (profiles := originalWindow)
      (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2) DE D S χ i hcol hci
  exact CurriedNormalizedFamily.ofCurried (literalLeftDirectPassiveNormalizationFamily
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂)
    (b := (source).block DE) (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1)
    (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pieces DE D) (S := S) (χ := χ)
    (hDiff := hDiff) (hroot := hroot) (hemb := hemb)
    (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (retainedScale := baseGeometry.retainedScale) (g := baseGeometry.enlargement)
    (hscale := baseGeometry.retainedScale_pos) (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
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
    (v := v) (exceptional := predicate) (F := ((source).charts DE D).kernel)
    (firstFixed := ((source).block DE).literalLeftFixed D.val) (hfirst := ((source).block DE).literalLeftFixed_generates C D.val) (j := leaf.2)
    (hS := hS) (hlive := hbare) (profileBound := 1) (hprofileBound := by norm_num)
    (hprofile := hprofile) (geometry := geometry) (hretained := rfl) (henlargement := rfl)
    (hsecond := rfl) (hopposite := rfl) (hunit := rfl) (hnonunit := rfl)
    (direct := fun _ => hslotsZero) (columnLoss := loss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hloss) (hcutoffExponent := hcutoffExponent)
    (hsmall := hsmall) (hcutoffPower := hcutoffPower₂) (hactiveColumns := hactive)
    (oldSupport := literalPrimitiveFirstSource_oldSupport (Q := Q) (a := a) (Z := Z) (hZ := hZ))
    (firstIdeal := hfirstIdeal) (oppositeIdeal := hoppositeIdeal)
    (physicalDivisor := rfl) (branchTag := rfl) (hexceptional := rfl))

/-- The original right direct case constructs its own passive family. -/
def literalPrimitiveRightDirectFactory
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
    CurriedNormalizedFamily A σ (WithLp 2 (ℝ × ℝ)) ω ψ Z := by
  let baseGeometry := Q.literalPrimitiveRightDirectGeometry
      (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
      (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
      (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
      (loss := loss) (cutoffExponent := cutoffExponent) (step := step)
      (hloss := hloss) (hcutoffExponent := hcutoffExponent) DE D
  let rowWindow := Q.literalPrimitiveRightDirectRows
      (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
      (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
      (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
      (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
      (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
      (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
      (hcutoffPower := hcutoffPower) (step := step) (hstep := hstep)
      (hloss := hloss) (hcutoffExponent := hcutoffExponent) DE D
  let v := leaf.1
  let predicate := (exceptional DE D).right S χ
  let geometry := baseGeometry.atSecondPattern v.block.primes
    v.block.leftMultiplicity v.block.rightMultiplicity v.block.left_positive v.block.right_positive
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
  have hbare : (v.leaf predicate ((source).charts DE D).kernel (fun i => -((source).charts DE D).rightPoint i) leaf.2).Live :=
    (v.leaf predicate ((source).charts DE D).kernel (fun i => -((source).charts DE D).rightPoint i) leaf.2).live_of_scale_live _ _ hlive
  have hprofile := ActualGaussStage.canonicalSector_fiberLeaf_rowProfile_one
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (μv := μv) (hDiff := hDiff) (ν := ν)
    P δ₂ hδ₂ hδ₂half
    (((source).pieces DE D).rightData.directSource
      (((source).pieces DE D).rightDivisorCoefficient S χ))
    baseGeometry.retainedScale Z baseGeometry.enlargement
    baseGeometry.retainedScale_pos (zero_lt_one.trans hZ) cutoff₂ hcutoff₂ rowWindow
    0 0 (fun _ _ => (PUnit.unit : PUnit.{1})) (fun _ _ i => Fin.elim0 i)
    (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
    (((source).pieces DE D).rightSourceCover (raw).originalAtlas S χ)
    predicate ((source).charts DE D).kernel (fun i => -((source).charts DE D).rightPoint i) leaf hlive
  have hfirstIdeal : geometry.ideals.first.val = DE.val.2 :=
    ((source).block DE).literalRightCoordinates_first D.val
  have hoppositeIdeal : geometry.ideals.opposite.val = DE.val.1 :=
    ((source).block DE).literalRightCoordinates_opposite D.val
  have hactive : ∀ i ∈ ((source).pieces DE D).rightData.columns,
      ((source).pieces DE D).rightDivisorCoefficient S χ i ≠ 0 →
      A.exteriorNorm (((source).pieces DE D).rightData.ideal i) ≤
        Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + loss) := by
    intro i hcol hci
    change A.exteriorNorm (((source).pieces DE D).rightData.ideal i) ≤
      Z ^ ((internal).n₁ + (internal).n₂ + (internal).z -
        idealLogLength Z geometry.ideals.first.val - 0 + loss)
    rw [hfirstIdeal, sub_zero]
    exact literalPrimitiveDirectRight_active_norm
      (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
      (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
      (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
      (cap := cap) (annulus := hi) (loss := loss) (hannulus := hhi) (hcap := hcap)
      (hannulusZ := hannulusZ) (domain := domain) (profiles := originalWindow)
      (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2) DE D S χ i hcol hci
  exact CurriedNormalizedFamily.ofCurried (literalRightDirectPassiveNormalizationFamily
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
    (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂)
    (b := (source).block DE) (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1)
    (finiteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
    (radius := (source).radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
    (p := (source).pieces DE D) (S := S) (χ := χ)
    (hDiff := hDiff) (hroot := hroot) (hemb := hemb)
    (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (retainedScale := baseGeometry.retainedScale) (g := baseGeometry.enlargement)
    (hscale := baseGeometry.retainedScale_pos) (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
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
    (v := v) (exceptional := predicate) (F := ((source).charts DE D).kernel)
    (firstFixed := ((source).block DE).literalRightFixed D.val) (hfirst := ((source).block DE).literalRightFixed_generates C D.val) (j := leaf.2)
    (hS := hS) (hlive := hbare) (profileBound := 1) (hprofileBound := by norm_num)
    (hprofile := hprofile) (geometry := geometry) (hretained := rfl) (henlargement := rfl)
    (hsecond := rfl) (hopposite := rfl) (hunit := rfl) (hnonunit := rfl)
    (direct := fun _ => hslotsZero) (columnLoss := loss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hloss) (hcutoffExponent := hcutoffExponent)
    (hsmall := hsmall) (hcutoffPower := hcutoffPower₂) (hactiveColumns := hactive)
    (oldSupport := literalPrimitiveFirstSource_oldSupport (Q := Q) (a := a) (Z := Z) (hZ := hZ))
    (firstIdeal := hfirstIdeal) (oppositeIdeal := hoppositeIdeal)
    (physicalDivisor := rfl) (branchTag := rfl) (hexceptional := rfl))


/-- Dispatch on the genuine parent live key. Squarefreeness and
physical nonemptiness come from this key's existing positive factors. -/
def literalPrimitiveDirectFactory
    (j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization) :
    CurriedNormalizedFamily A σ (WithLp 2 (ℝ × ℝ)) ω ψ Z := by
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
    exact literalPrimitiveLeftDirectFactory
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
    exact literalPrimitiveRightDirectFactory
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

/-- The original direct live carrier is the outer index. The inner
index is exactly the passive pair label of that original case. -/
def literalPrimitiveDirectFamily
    (analytic : ∀ j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization,
      (factories j).Input) :
    ActualNormalizedPairFamily A σ (WithLp 2 (ℝ × ℝ))
      (Σ j : (stages).prepared.liveLeaves (raw).originalAtlas exceptional normalization,
        (factories j).Label) ω ψ Z :=
  ActualNormalizedPairFamily.sigmaCombine (fun j => (factories j).family (analytic j))

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftDirectFactory
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightDirectFactory

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectFactory
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectFamily
