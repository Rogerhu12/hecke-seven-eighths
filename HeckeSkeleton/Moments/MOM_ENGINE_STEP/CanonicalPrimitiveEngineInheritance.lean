import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveUniformEngine
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledInverseSlots
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PairedEngineAdmissibilityTransport

/-!
# The existing primitive engine preserves inverse slot membership

The pooled output reads the inverse property from its original selected
children, through exactly its existing finite reindexing and comparison
scale transport. The uniform dispatcher retains its original reference
row and selected pool. Empty and zero-slot cases are discharged on those
same outputs. Only admissibility is strengthened; the numerical engine,
its branches, children, kernels and terminal values are left intact.
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

namespace PairedEngineConclusion

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ step ε terminalExponent C control : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}
variable (out : PairedEngineConclusion (Ω := Ω) centered d a
  Z t Y₁ Y₂ step ε terminalExponent C control admissible)

/-- A property of the already selected data, with no closure requirement
on the original finite set of characters. -/
def SlotInverseMembership : Prop :=
  ∀ (b : Fin out.branches) (z : Ω),
    (∀ i, ((out.leftData b z).slotCoefficient i)⁻¹ ∈ (out.leftData b z).theta) ∧
    (∀ i, ((out.rightData b z).slotCoefficient i)⁻¹ ∈ (out.rightData b z).theta)

/-- Internal proof transport on the same conclusion. Actual producers
below construct the property from the original parent, not as input. -/
def withInheritedSlots (h : out.SlotInverseMembership) :
    PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ step ε terminalExponent C control
      (fun child parameters => admissible child parameters ∧
        ∀ i, (child.slotCoefficient i)⁻¹ ∈ child.theta) :=
  out.withAdmissible _
    (fun b z => ⟨out.left_admissible b z, (h b z).1⟩)
    (fun b z => ⟨out.right_admissible b z, (h b z).2⟩)

variable (h : out.SlotInverseMembership)

@[simp] theorem withInheritedSlots_branches :
    (out.withInheritedSlots h).branches = out.branches := rfl

@[simp] theorem withInheritedSlots_leftData :
    (out.withInheritedSlots h).leftData = out.leftData := rfl

@[simp] theorem withInheritedSlots_rightData :
    (out.withInheritedSlots h).rightData = out.rightData := rfl

@[simp] theorem withInheritedSlots_leftParameters :
    (out.withInheritedSlots h).leftParameters = out.leftParameters := rfl

@[simp] theorem withInheritedSlots_rightParameters :
    (out.withInheritedSlots h).rightParameters = out.rightParameters := rfl

@[simp] theorem withInheritedSlots_kernel :
    (out.withInheritedSlots h).kernel = out.kernel := rfl

@[simp] theorem withInheritedSlots_terminals :
    (out.withInheritedSlots h).firstZero = out.firstZero ∧
      (out.withInheritedSlots h).secondZero = out.secondZero ∧
      (out.withInheritedSlots h).exceptional = out.exceptional ∧
      (out.withInheritedSlots h).tail = out.tail := ⟨rfl, rfl, rfl, rfl⟩

/-- The empty parent uses the existing empty branch carrier. -/
theorem slotInverseMembership_of_zero_branches (hzero : out.branches = 0) :
    out.SlotInverseMembership := by
  intro b z
  exact Fin.elim0 (Fin.cast hzero b)

/-- This handles the actual direct case using only its existing slot
count conclusion; no slot character is introduced in this case. -/
theorem slotInverseMembership_of_zero_slots (hzero : d.geometry.slotCount = 0) :
    out.SlotInverseMembership := by
  intro b z
  exact ⟨out.left_slot_inverse_of_zero_slots hzero b z,
    out.right_slot_inverse_of_zero_slots hzero b z⟩

end PairedEngineConclusion

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

namespace CompleteMovingRowRecipe

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
variable (hfit : (data ξ).geometry.fitsMesh b.loss)
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
local notation "hY₁" => scaleWindows.1
local notation "hY₂" => scaleWindows.2.1
local notation "hleftPower" => scaleWindows.2.2.1
local notation "hrightPower" => scaleWindows.2.2.2.1
local notation "hY₁le" => scaleWindows.2.2.2.2.1
local notation "hY₂le" => scaleWindows.2.2.2.2.2.1
local notation "htotal" => scaleWindows.2.2.2.2.2.2.1
local notation "hcolumn" => scaleWindows.2.2.2.2.2.2.2
local notation "hannulusZ" =>
  (b.threshold_windows Z (b.fullThreshold_spec.2.1.trans hlarge)).1
local notation "hlowerThreshold" =>
  (b.threshold_windows Z (b.fullThreshold_spec.2.1.trans hlarge)).2.1
local notation "chosenContour" => CanonicalPrimitiveEngineMassChoices.contour
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b orders heightC
local notation "hcontourPos" => CanonicalPrimitiveEngineMassChoices.contour_pos
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b orders heightC
local notation "hcontourQuarter" => CanonicalPrimitiveEngineMassChoices.contour_le_quarter
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b orders heightC
local notation "control" => CanonicalPrimitiveEngineControl.value amplitude t
local notation "internal" => Q.fullSupportParameters a Z
local notation "raw" => ((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ)
  internal Z t).raw canonicalLeft canonicalRight
local notation "firstSource" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t canonicalLeft canonicalRight hZ hbudget centered
  (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one hZ.le) b.tilt b.tilt_pos b.tilt_le_half


local notation "hN" => Q.literalPrimitiveFirstSource_column_norm μv ν C hroot hemb W ξ
  a Z t canonicalLeft canonicalRight hZ hbudget centered
  (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one hZ.le) b.tilt b.tilt_pos b.tilt_le_half
  b.cap b.hi b.loss b.lengthBound b.lengthBound b.columnBound b.hi_ge_one hcap hannulusZ
  hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le window₂ hrows htime (fun _ h => h.2) hcolumn

variable (Drecipe : ComparisonPoissonCoefficientData K A)
variable (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
variable {bad : Finset (HeightOneSpectrum (𝓞 K))}
variable (pool : PowerScaleExteriorPool A bad Z (b.step / 3) b.loss)
variable (hdensity : 0 < pool.rowDensity b.rowBound b.columnBound)
variable (hmassLarge : CanonicalPrimitiveEngineMassChoices.pooledThreshold (A := A) b ≤ Z)

local notation "source" => Q.literalPrimitivePooledSource
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one hZ.le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z hZ.le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)

local notation "stages" => Q.literalPrimitivePooledStages
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one hZ.le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z hZ.le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)
  (hstep := b.step_pos) (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z hZ.le))

local notation "exceptional" => Q.literalPrimitivePooledPredicates
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one hZ.le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z hZ.le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)
  (hstep := b.step_pos) (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z hZ.le))

local notation "normalization" => Q.literalPrimitivePooledNormalization
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one hZ.le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z hZ.le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)

local notation "computedInput" => literalPrimitivePooledInput
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one hZ.le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := b.loss) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := b.loss_pos.le) (hfit := hfit) (hsmall := b.width_margin)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z hZ.le))
  (hcutoffPower := (b.firstCutoff_le Z hZ.le)) (hcutoffPower₂ := (b.secondCutoff_le Z hZ.le))
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

local notation "pooledFamily" => literalPrimitivePooledFamily
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one hZ.le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := b.loss) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := b.loss_pos.le) (hfit := hfit) (hsmall := b.width_margin)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z hZ.le))
  (hcutoffPower := (b.firstCutoff_le Z hZ.le)) (hcutoffPower₂ := (b.secondCutoff_le Z hZ.le))
  (reference := reference) (href := href) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (originalBound := amplitude) (horiginalBound := (zero_le_one.trans hamplitude))
  (originalWindow := window₂) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (hprimeOrders := hprimeOrders)
  (δ := chosenContour) (analyticHeight := (heightC * (1 + Real.log Z))) (hδ := hcontourPos) (hδhi := hcontourQuarter)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity) computedInput

local notation "familyInverse" => literalPrimitivePooled_family_slot_inverse_mem_theta
  (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one hZ.le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half) (hY₁ := hY₁) (hY₂ := hY₂)
  (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
  (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (step := b.step) (error := b.error) (mesh := b.loss) (hstep := b.step_pos)
  (herror := b.error_pos.le) (hmesh := b.loss_pos.le) (hfit := hfit) (hsmall := b.width_margin)
  (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z hZ.le))
  (hcutoffPower := (b.firstCutoff_le Z hZ.le)) (hcutoffPower₂ := (b.secondCutoff_le Z hZ.le))
  (reference := reference) (href := href) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (originalBound := amplitude) (horiginalBound := (zero_le_one.trans hamplitude))
  (originalWindow := window₂) (hrows := hrows) (htime := htime) (hprime := hprime)
  (hcap := hcap) (hannulusZ := hannulusZ) (domain := canonicalDomain) (hprimeOrders := hprimeOrders)
  (δ := chosenContour) (analyticHeight := (heightC * (1 + Real.log Z))) (hδ := hcontourPos) (hδhi := hcontourQuarter)
  (hone := hone) (hbackground := hbackground) (hslot := hslot)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
  (hinverse := hslotInverse) computedInput

local notation "secondConstant" =>
  CanonicalPrimitiveSecondTerminalUniform.Csecond μv ν C hDiff b second
local notation "massConstant" => CanonicalPrimitiveEngineMassChoices.constant
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b orders heightC
local notation "exceptionalCost" =>
  stages.supported.gated.exceptionalBudget raw.originalAtlas exceptional normalization / Z ^ (a.m + a.q)

variable (finalConstant exceptionalConstant terminalExponent exceptionalExponent : ℝ)
variable (finalDegree exceptionalDegree : ℕ)
variable (hfinalConstant : 0 ≤ finalConstant) (hexceptionalConstant : 0 ≤ exceptionalConstant)
variable (hfirstDegree : firstDualOriginalProfileDegree b.cap 1 ≤ finalDegree)
variable (hsecondDegree : 2 * (b.cap + 2) ≤ finalDegree)
variable (hexceptionalDegree : exceptionalDegree ≤ finalDegree)
variable (hmassDegree : CanonicalPrimitiveEngineMassChoices.degree b ≤ finalDegree)
variable (hterminalExponent : b.paddingMax + 3 * b.step + b.ε ≤ terminalExponent)
variable (hexceptionalExponent : exceptionalExponent ≤ terminalExponent)
variable (hterminalConstant : 2 * first.Cfirst + 2 * secondConstant + exceptionalConstant ≤ finalConstant)
variable (hmassConstant : massConstant ≤ finalConstant)

variable (hexceptional : exceptionalCost ≤
  exceptionalConstant * control ^ exceptionalDegree * Z ^ exceptionalExponent)

local notation "engine" => Q.literalPrimitivePooledEngine
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
  (hprimeOrders := hprimeOrders) (first := first) (second := second)
  (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
  (hcap := hcap) (hlarge := hlarge) (hfit := hfit)
  (reference := reference) (href := href) (amplitude := amplitude) (hamplitude := hamplitude)
  (profiles := profiles) (hrows := hrows) (htime := htime) (hprime := hprime)
  (heightC := heightC) (analyticWindow := analyticWindow) (boundary := boundary)
  (hone := hone) (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
  (Drecipe := Drecipe) (hD := hD) (pool := pool) (hdensity := hdensity)
  (hmassLarge := hmassLarge)
  (finalConstant := finalConstant) (exceptionalConstant := exceptionalConstant)
  (terminalExponent := terminalExponent) (exceptionalExponent := exceptionalExponent)
  (finalDegree := finalDegree) (exceptionalDegree := exceptionalDegree)
  (hfinalConstant := hfinalConstant) (hexceptionalConstant := hexceptionalConstant)
  (hfirstDegree := hfirstDegree) (hsecondDegree := hsecondDegree)
  (hexceptionalDegree := hexceptionalDegree) (hmassDegree := hmassDegree)
  (hterminalExponent := hterminalExponent) (hexceptionalExponent := hexceptionalExponent)
  (hterminalConstant := hterminalConstant) (hmassConstant := hmassConstant)
  (hexceptional := hexceptional)

/-- The fixed pooled engine retains precisely the inverse memberships
proved for its actual passive children, after its original `Fin`
reindexing and the unchanged comparison-scale transport. -/
theorem literalPrimitivePooledEngine_slot_inverse_mem_theta :
    engine.SlotInverseMembership := by
  change ∀ (i : Fin (Fintype.card (pooledFamily.active Finset.univ)))
      (z : WithLp 2 (ℝ × ℝ)),
    (∀ j, ((pooledFamily.leftData Finset.univ
      ((Fintype.equivFin (pooledFamily.active Finset.univ)).symm i) z).slotCoefficient j)⁻¹ ∈
        (pooledFamily.leftData Finset.univ
          ((Fintype.equivFin (pooledFamily.active Finset.univ)).symm i) z).theta) ∧
    (∀ j, ((pooledFamily.rightData Finset.univ
      ((Fintype.equivFin (pooledFamily.active Finset.univ)).symm i) z).slotCoefficient j)⁻¹ ∈
        (pooledFamily.rightData Finset.univ
          ((Fintype.equivFin (pooledFamily.active Finset.univ)).symm i) z).theta)
  exact fun i z => familyInverse
    ((Fintype.equivFin (pooledFamily.active Finset.univ)).symm i) z

local notation "engineInverse" => Q.literalPrimitivePooledEngine_slot_inverse_mem_theta
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
  (hprimeOrders := hprimeOrders) (first := first) (second := second)
  (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
  (hcap := hcap) (hlarge := hlarge) (hfit := hfit)
  (reference := reference) (href := href) (amplitude := amplitude) (hamplitude := hamplitude)
  (profiles := profiles) (hrows := hrows) (htime := htime) (hprime := hprime)
  (heightC := heightC) (analyticWindow := analyticWindow) (boundary := boundary)
  (hone := hone) (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
  (Drecipe := Drecipe) (hD := hD) (pool := pool) (hdensity := hdensity)
  (hmassLarge := hmassLarge)
  (finalConstant := finalConstant) (exceptionalConstant := exceptionalConstant)
  (terminalExponent := terminalExponent) (exceptionalExponent := exceptionalExponent)
  (finalDegree := finalDegree) (exceptionalDegree := exceptionalDegree)
  (hfinalConstant := hfinalConstant) (hexceptionalConstant := hexceptionalConstant)
  (hfirstDegree := hfirstDegree) (hsecondDegree := hsecondDegree)
  (hexceptionalDegree := hexceptionalDegree) (hmassDegree := hmassDegree)
  (hterminalExponent := hterminalExponent) (hexceptionalExponent := hexceptionalExponent)
  (hterminalConstant := hterminalConstant) (hmassConstant := hmassConstant)
  (hexceptional := hexceptional)

/-- The original pooled engine with its inherited slot condition made
available to the next engine step. All numerical fields are copied. -/
def literalPrimitivePooledEngineWithInheritedSlots :=
  engine.withInheritedSlots engineInverse

end CompleteMovingRowRecipe

end HeckeSkeleton.Moments.EngineStep

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments CommonSupportMass HeckeGeneral.Bridge
open CanonicalPrimitiveEngineChoices

variable {K : Type} [Field K] [NumberField K]

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ω ψ : HeckeCharacter K}
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

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (b : Box) (orders : Finset (ℕ × ℕ))
variable (first : CanonicalPrimitiveFirstTerminalConstants.Fixed μv ν C hDiff b orders)
variable (second : CanonicalPrimitiveSecondTerminalConstants.Fixed
  (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  μv hDiff C (rowBallFiniteFamily K A.Sf 1) b)
variable (heightC exceptionalConstant : ℝ)

local notation "secondConstant" =>
  CanonicalPrimitiveSecondTerminalUniform.Csecond μv ν C hDiff b second
local notation "massConstant" => CanonicalPrimitiveEngineMassChoices.constant
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b orders heightC

local notation "finalConstant" => constant
  (A := A) (σ := σ) (ω := ω) (ψ := ψ)
  μv ν C hDiff b orders first second heightC exceptionalConstant

variable (exceptionalDegree : ℕ) (Zexceptional : ℝ)
variable (hexceptionalConstant : 0 ≤ exceptionalConstant)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (Drecipe : ComparisonPoissonCoefficientData K A)
variable (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {Index : Type*} {data : Index → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)
variable (W : NormProfileRecipe data) (ξ : Index)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable (hbudget : Q.FullJointBudget Z (a.m + a.q))
variable (hwidth : a.m + a.q ≤ b.widthMax) (hpadding : padding ≤ b.paddingMax)
variable (hcap : (data ξ).geometry.slotCount ≤ b.cap)
variable (hlarge : threshold A b Zexceptional ≤ Z)
variable (hfit : (data ξ).geometry.fitsMesh b.loss)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
variable (amplitude : ℝ) (hamplitude : 1 ≤ amplitude)
variable (profiles : RawProfileWindow rowDomain heightDomain (Set.Icc b.lo b.hi)
  (OriginalProfileAtomBounds.profileOrders orders ∪
    CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
  (data ξ) amplitude)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (htime : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable (analyticWindow : CanonicalOriginalPrimeAnalyticProvider.Window
  (A := A) (P := P) (R := R) (data ξ).theta b.rawNormBound heightC)
variable (boundary : a.κ < 1 → FiniteOrderBoundary (K := K) ((a.κ + 1) / 2))
variable (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta)
variable (hbackground : (data ξ).plainBackground⁻¹ ∈ (data ξ).theta ∨
  ¬ FiniteOrder (data ξ).plainBackground)
variable (hslot : ∀ i, (data ξ).slotCoefficient i ∈ (data ξ).theta)
variable (hslotInverse : ∀ i, ((data ξ).slotCoefficient i)⁻¹ ∈ (data ξ).theta)

local notation "thresholds" => threshold_spec A b Zexceptional Z hlarge
local notation "hfull" => thresholds.1
local notation "control" => CanonicalPrimitiveEngineControl.value amplitude t
local notation "finalDegree" => CanonicalPrimitiveEngineFinalBudget.degree b exceptionalDegree
local notation "terminalExponent" => CanonicalPrimitiveEngineFinalBudget.terminalExponent b

local notation "directCost" => Q.literalPrimitiveDirectEngineExceptionalCost
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
  (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hcap := hcap) (hlarge := hfull)
  (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (htime := htime)

local notation "poolCost" => fun
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : reference ∈ pairedRows (data ξ) a Z)
    (selection : CanonicalPrimitiveEnginePool.Selection A b Z) =>
  Q.literalPrimitivePooledEngineExceptionalCost
    (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
    (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
    (hcap := hcap) (hlarge := hfull) (reference := reference) (href := href)
    (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (htime := htime)
    (pool := selection.pool) (hdensity := selection.density_pos)


variable (hdirect : Zexceptional ≤ Z → (data ξ).geometry.slotCount = 0 →
  directCost ≤ exceptionalConstant * control ^ exceptionalDegree * Z ^ terminalExponent)
variable (hpool : Zexceptional ≤ Z →
  ∀ (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : reference ∈ pairedRows (data ξ) a Z)
    (selection : CanonicalPrimitiveEnginePool.Selection A b Z),
  poolCost reference href selection ≤
    exceptionalConstant * control ^ exceptionalDegree * Z ^ terminalExponent)

local notation "produced" => produce
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
  (first := first) (second := second) (heightC := heightC)
  (exceptionalConstant := exceptionalConstant) (exceptionalDegree := exceptionalDegree)
  (Zexceptional := Zexceptional) (hexceptionalConstant := hexceptionalConstant)
  (hprimeOrders := hprimeOrders) (Drecipe := Drecipe) (hD := hD)
  (Q := Q) (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
  (hcap := hcap) (hlarge := hlarge) (hfit := hfit)
  (amplitude := amplitude) (hamplitude := hamplitude) (profiles := profiles)
  (hrows := hrows) (htime := htime) (hprime := hprime)
  (analyticWindow := analyticWindow) (boundary := boundary) (hone := hone)
  (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
  hdirect hpool

/-- All branches of the existing uniform producer inherit the inverse
condition. Its reference row, selected pool and finite enumeration are
those of `produce` itself. -/
theorem produce_slot_inverse_mem_theta : produced.SlotInverseMembership := by
  by_cases hzero : (data ξ).geometry.slotCount = 0
  · exact produced.slotInverseMembership_of_zero_slots hzero
  by_cases hempty : pairedRows (data ξ) a Z = ∅
  · apply produced.slotInverseMembership_of_zero_branches
    simp only [produce, dif_pos hempty, PairedEngineConclusion.ofEmptyParent_branches]
  have hnonempty : (pairedRows (data ξ) a Z).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hempty
  let reference := hnonempty.choose
  have href : reference ∈ pairedRows (data ξ) a Z := hnonempty.choose_spec
  let selection := CanonicalPrimitiveEnginePool.selected A b Z thresholds.2.1
  have hsecond : 0 ≤ secondConstant :=
    (CanonicalPrimitiveSecondTerminalUniform.Csecond_pos μv ν C hDiff b second).le
  have hmass : 0 ≤ massConstant :=
    (CanonicalPrimitiveEngineMassChoices.constant_pos
      (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b orders heightC).le
  have hfinal : 0 ≤ finalConstant :=
    (constant_pos (A := A) (σ := σ) (ω := ω) (ψ := ψ)
      μv ν C hDiff b orders first second heightC exceptionalConstant hexceptionalConstant).le
  have h := Q.literalPrimitivePooledEngine_slot_inverse_mem_theta
    (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
    (hprimeOrders := hprimeOrders) (first := first) (second := second)
    (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
    (hcap := hcap) (hlarge := hfull) (hfit := hfit)
    (reference := reference) (href := href) (amplitude := amplitude) (hamplitude := hamplitude)
    (profiles := profiles) (hrows := hrows) (htime := htime) (hprime := hprime)
    (heightC := heightC) (analyticWindow := analyticWindow) (boundary := boundary)
    (hone := hone) (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
    (Drecipe := Drecipe) (hD := hD) (pool := selection.pool) (hdensity := selection.density_pos)
    (hmassLarge := thresholds.2.2.1)
    (finalConstant := finalConstant) (exceptionalConstant := exceptionalConstant)
    (terminalExponent := terminalExponent) (exceptionalExponent := terminalExponent)
    (finalDegree := finalDegree) (exceptionalDegree := exceptionalDegree)
    (hfinalConstant := hfinal) (hexceptionalConstant := hexceptionalConstant)
    (hfirstDegree := CanonicalPrimitiveEngineFinalBudget.first_degree_le b exceptionalDegree)
    (hsecondDegree := CanonicalPrimitiveEngineFinalBudget.second_degree_le b exceptionalDegree)
    (hexceptionalDegree := CanonicalPrimitiveEngineFinalBudget.exceptional_degree_le b exceptionalDegree)
    (hmassDegree := CanonicalPrimitiveEngineFinalBudget.mass_degree_le b exceptionalDegree)
    (hterminalExponent := le_rfl) (hexceptionalExponent := le_rfl)
    (hterminalConstant := CanonicalPrimitiveEngineFinalBudget.terminals_le hmass)
    (hmassConstant := CanonicalPrimitiveEngineFinalBudget.mass_le
      first.Cfirst_pos.le hsecond hexceptionalConstant)
    (hexceptional := hpool thresholds.2.2.2 reference href selection)
  simpa only [produce, dif_neg hempty, dif_neg hzero] using h

local notation "producedInverse" => produce_slot_inverse_mem_theta
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
  (first := first) (second := second) (heightC := heightC)
  (exceptionalConstant := exceptionalConstant) (exceptionalDegree := exceptionalDegree)
  (Zexceptional := Zexceptional) (hexceptionalConstant := hexceptionalConstant)
  (hprimeOrders := hprimeOrders) (Drecipe := Drecipe) (hD := hD)
  (Q := Q) (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
  (hcap := hcap) (hlarge := hlarge) (hfit := hfit)
  (amplitude := amplitude) (hamplitude := hamplitude) (profiles := profiles)
  (hrows := hrows) (htime := htime) (hprime := hprime)
  (analyticWindow := analyticWindow) (boundary := boundary) (hone := hone)
  (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
  hdirect hpool

/-- A uniform result ready for another engine step, with the original
selected data and all original numerical estimates kept verbatim. -/
def produceWithInheritedSlots :
    PairedEngineConclusion (Ω := WithLp 2 (ℝ × ℝ)) centered (data ξ) a Z t Y₁ Y₂
      b.step b.ε terminalExponent finalConstant (control ^ finalDegree)
      (fun child parameters =>
        MovingEngineChildAdmissible A P R
          (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (data ξ)
          Set.univ (Set.Icc (0 : ℝ) b.hi) orders Z child parameters ∧
        ∀ i, (child.slotCoefficient i)⁻¹ ∈ child.theta) :=
  produced.withInheritedSlots producedInverse

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine

#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.withInheritedSlots
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledEngine_slot_inverse_mem_theta
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledEngineWithInheritedSlots
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine.produce_slot_inverse_mem_theta
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine.produceWithInheritedSlots
