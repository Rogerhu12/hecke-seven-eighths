import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledFactory
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveInverseSlots

/-!
# Inherited inverse slot characters in the original pooled output

Each of the four actual factories is inspected on its existing
calibrations. Their slot fields are the original parent characters at
the literal allocation indices. The already chosen capacity child
retains those fields at its actual selected indices. No new family,
child, character closure or raw-data certificate is introduced.

The main cases and every one, six and seven valuation are then read
through the same original live-key dispatcher and the same sigma family.
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

/-- Transport a proved raw field property through the actual selected
child. The four public factory proofs below construct both raw premises
by projection from the original literal data. -/
private theorem actual_family_inverse_slots
    {ω ψ : HeckeCharacter K} {V Λ : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
    (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)
    (hleft : ∀ (b : Λ) (z : V)
      (i : Fin ((family.leftCalibration b).data z).geometry.slotCount),
      (((family.leftCalibration b).data z).slotCoefficient i)⁻¹ ∈
        ((family.leftCalibration b).data z).theta)
    (hright : ∀ (b : Λ) (z : V)
      (i : Fin ((family.rightCalibration b).data z).geometry.slotCount),
      (((family.rightCalibration b).data z).slotCoefficient i)⁻¹ ∈
        ((family.rightCalibration b).data z).theta)
    (b : family.active labels) (z : V) :
    (∀ i, ((family.leftData labels b z).slotCoefficient i)⁻¹ ∈
      (family.leftData labels b z).theta) ∧
    (∀ i, ((family.rightData labels b z).slotCoefficient i)⁻¹ ∈
      (family.rightData labels b z).theta) := by
  constructor
  · intro i
    change (((family.leftChild labels b).frozenData z).slotCoefficient i)⁻¹ ∈
      ((family.leftChild labels b).frozenData z).theta
    rw [(family.leftChild labels b).frozen_slotCoefficient_eq z i,
      (family.leftChild labels b).frozen_theta_eq z]
    exact hleft b.val z _
  · intro i
    change (((family.rightChild labels b).frozenData z).slotCoefficient i)⁻¹ ∈
      ((family.rightChild labels b).frozenData z).theta
    rw [(family.rightChild labels b).frozen_slotCoefficient_eq z i,
      (family.rightChild labels b).frozen_theta_eq z]
    exact hright b.val z _

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

local notation "leftMainFactory" => literalPrimitiveLeftMainFactory
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

local notation "leftPoolFactory" => literalPrimitiveLeftPoolFactory
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

local notation "rightMainFactory" => literalPrimitiveRightMainFactory
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

local notation "rightPoolFactory" => literalPrimitiveRightPoolFactory
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

variable (hinverse : ∀ i, ((data ξ).slotCoefficient i)⁻¹ ∈ (data ξ).theta)

include hinverse

/-- Both children of this same actual main factory inherit the original slot inverses. -/
theorem literalPrimitiveLeftMainFactory_slot_inverse_mem_theta
    (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset)
    (S : divisorPool (source.pools DE D).rightData.columns
      (fun j => ((source.pools DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (leaf : (((stages DE D).left S χ).main).supported.gated.CoveredLeafKey (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).main) (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).main))
    (hS : Squarefree S.val)
    (hlive : ((((stages DE D).left S χ).main).supported.gated.fiberCoveredLeaf (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).main) (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).main)
      ((exceptional DE D).left S χ).main (source.charts DE D).kernel (source.charts DE D).leftPoint leaf).Live) :
    ∀ (input : (leftMainFactory DE D S χ leaf hS hlive).Input)
      (b : ((leftMainFactory DE D S χ leaf hS hlive).family input).active Finset.univ) (z : WithLp 2 (ℝ × ℝ)),
      (∀ i, ((((leftMainFactory DE D S χ leaf hS hlive).family input).leftData Finset.univ b z).slotCoefficient i)⁻¹ ∈
        (((leftMainFactory DE D S χ leaf hS hlive).family input).leftData Finset.univ b z).theta) ∧
      (∀ i, ((((leftMainFactory DE D S χ leaf hS hlive).family input).rightData Finset.univ b z).slotCoefficient i)⁻¹ ∈
        (((leftMainFactory DE D S χ leaf hS hlive).family input).rightData Finset.univ b z).theta) := by
  intro input b z
  exact actual_family_inverse_slots ((leftMainFactory DE D S χ leaf hS hlive).family input) Finset.univ
    (by
      intro label mode i
      change ((data ξ).slotCoefficient _)⁻¹ ∈ (data ξ).theta
      exact hinverse _)
    (by
      intro label mode i
      change ((data ξ).slotCoefficient _)⁻¹ ∈ (data ξ).theta
      exact hinverse _) b z

/-- Both children of this same actual main factory inherit the original slot inverses. -/
theorem literalPrimitiveRightMainFactory_slot_inverse_mem_theta
    (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset)
    (S : divisorPool (source.pools DE D).rightData.columns
      (fun j => ((source.pools DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (leaf : (((stages DE D).right S χ).main).supported.gated.CoveredLeafKey (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).main) (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).main))
    (hS : Squarefree S.val)
    (hlive : ((((stages DE D).right S χ).main).supported.gated.fiberCoveredLeaf (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).main) (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).main)
      ((exceptional DE D).right S χ).main (source.charts DE D).kernel (fun i => -(source.charts DE D).rightPoint i) leaf).Live) :
    ∀ (input : (rightMainFactory DE D S χ leaf hS hlive).Input)
      (b : ((rightMainFactory DE D S χ leaf hS hlive).family input).active Finset.univ) (z : WithLp 2 (ℝ × ℝ)),
      (∀ i, ((((rightMainFactory DE D S χ leaf hS hlive).family input).leftData Finset.univ b z).slotCoefficient i)⁻¹ ∈
        (((rightMainFactory DE D S χ leaf hS hlive).family input).leftData Finset.univ b z).theta) ∧
      (∀ i, ((((rightMainFactory DE D S χ leaf hS hlive).family input).rightData Finset.univ b z).slotCoefficient i)⁻¹ ∈
        (((rightMainFactory DE D S χ leaf hS hlive).family input).rightData Finset.univ b z).theta) := by
  intro input b z
  exact actual_family_inverse_slots ((rightMainFactory DE D S χ leaf hS hlive).family input) Finset.univ
    (by
      intro label mode i
      change ((data ξ).slotCoefficient _)⁻¹ ∈ (data ξ).theta
      exact hinverse _)
    (by
      intro label mode i
      change ((data ξ).slotCoefficient _)⁻¹ ∈ (data ξ).theta
      exact hinverse _) b z

section LeftValuation

variable (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset)
variable (S : divisorPool (source.pools DE D).rightData.columns
  (fun j => ((source.pools DE D).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle) (valuation : AmplifierValuation) (prime : pool.primes)

local notation "baseGeometry" => OriginalNominalGeometry.canonicalPoolError
  (a := internal) pool valuation prime ((source.block DE).literalLeftCoordinates D.val)
  (2 * loss + cutoffExponent) (by positivity : 0 ≤ 2 * loss + cutoffExponent)
local notation "rowWindow" => ((source.pools DE D).divisorPools.leftData S).literalPoolRows internal
  ((source.block DE).literalLeftCoordinates D.val) (2 * loss + cutoffExponent)
  (by positivity) hstep (leftRows DE D S) valuation prime
local notation "poolStage" => ((source.pools DE D).divisorPools.leftData S).literalValuationStage
  (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  (μv := μv) (hDiff := hDiff) (ν := ν)
  ((source.pools DE D).leftDivisorCoefficient S χ) P internal ((source.block DE).literalLeftCoordinates D.val)
  (2 * loss + cutoffExponent) (by positivity) hstep (leftRows DE D S)
  δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ valuation prime
local notation "cover" => (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).residual prime valuation.multiplicity)
local notation "predicate" => poolStage.supported.gated.literalHybridPredicates cover cover P R
  (CanonicalLiteralActualCharacters.amplifiedPhases C
    ((source.block DE).literalLeftFixed D.val)
    (CanonicalLiteralFirstPhase.leftElement C (source.block DE).primes
      (source.block DE).leftMultiplicity (source.block DE).rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
    ((source.block DE).literalLeftFixed_generates C D.val) prime.val valuation.multiplicity)
  Q.moving Q.correction (data ξ).theta

/-- The original valuation and prime are retained in both selected children. -/
theorem literalPrimitiveLeftPoolFactory_slot_inverse_mem_theta
    (leaf : poolStage.supported.gated.CoveredLeafKey cover cover)
    (hS : Squarefree S.val)
    (hlive : (poolStage.supported.gated.fiberCoveredLeaf cover cover predicate
      (source.charts DE D).kernel (fun i => (source.charts DE D).leftPoint i.val) leaf).Live) :
    ∀ (input : (leftPoolFactory DE D S χ valuation prime leaf hS hlive).Input)
      (b : ((leftPoolFactory DE D S χ valuation prime leaf hS hlive).family input).active Finset.univ) (z : WithLp 2 (ℝ × ℝ)),
      (∀ i, ((((leftPoolFactory DE D S χ valuation prime leaf hS hlive).family input).leftData Finset.univ b z).slotCoefficient i)⁻¹ ∈
        (((leftPoolFactory DE D S χ valuation prime leaf hS hlive).family input).leftData Finset.univ b z).theta) ∧
      (∀ i, ((((leftPoolFactory DE D S χ valuation prime leaf hS hlive).family input).rightData Finset.univ b z).slotCoefficient i)⁻¹ ∈
        (((leftPoolFactory DE D S χ valuation prime leaf hS hlive).family input).rightData Finset.univ b z).theta) := by
  intro input b z
  exact actual_family_inverse_slots ((leftPoolFactory DE D S χ valuation prime leaf hS hlive).family input) Finset.univ
    (by
      intro label mode i
      change ((data ξ).slotCoefficient _)⁻¹ ∈ (data ξ).theta
      exact hinverse _)
    (by
      intro label mode i
      change ((data ξ).slotCoefficient _)⁻¹ ∈ (data ξ).theta
      exact hinverse _) b z

end LeftValuation

section RightValuation

variable (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset)
variable (S : divisorPool (source.pools DE D).rightData.columns
  (fun j => ((source.pools DE D).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle) (valuation : AmplifierValuation) (prime : pool.primes)

local notation "baseGeometry" => OriginalNominalGeometry.canonicalPoolError
  (a := internal) pool valuation prime ((source.block DE).literalRightCoordinates D.val)
  (2 * loss + cutoffExponent) (by positivity : 0 ≤ 2 * loss + cutoffExponent)
local notation "rowWindow" => ((source.pools DE D).divisorPools.rightData S).literalPoolRows internal
  ((source.block DE).literalRightCoordinates D.val) (2 * loss + cutoffExponent)
  (by positivity) hstep (rightRows DE D S) valuation prime
local notation "poolStage" => ((source.pools DE D).divisorPools.rightData S).literalValuationStage
  (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  (μv := μv) (hDiff := hDiff) (ν := ν)
  ((source.pools DE D).rightDivisorCoefficient S χ) P internal ((source.block DE).literalRightCoordinates D.val)
  (2 * loss + cutoffExponent) (by positivity) hstep (rightRows DE D S)
  δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ valuation prime
local notation "cover" => (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).residual prime valuation.multiplicity)
local notation "predicate" => poolStage.supported.gated.literalHybridPredicates cover cover P R
  (CanonicalLiteralActualCharacters.amplifiedPhases C
    ((source.block DE).literalRightFixed D.val)
    (CanonicalLiteralFirstPhase.rightElement C (source.block DE).primes
      (source.block DE).leftMultiplicity (source.block DE).rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val)
    ((source.block DE).literalRightFixed_generates C D.val) prime.val valuation.multiplicity)
  Q.moving Q.correction (data ξ).theta

/-- The original valuation and prime are retained in both selected children. -/
theorem literalPrimitiveRightPoolFactory_slot_inverse_mem_theta
    (leaf : poolStage.supported.gated.CoveredLeafKey cover cover)
    (hS : Squarefree S.val)
    (hlive : (poolStage.supported.gated.fiberCoveredLeaf cover cover predicate
      (source.charts DE D).kernel (fun i => -(source.charts DE D).rightPoint i.val) leaf).Live) :
    ∀ (input : (rightPoolFactory DE D S χ valuation prime leaf hS hlive).Input)
      (b : ((rightPoolFactory DE D S χ valuation prime leaf hS hlive).family input).active Finset.univ) (z : WithLp 2 (ℝ × ℝ)),
      (∀ i, ((((rightPoolFactory DE D S χ valuation prime leaf hS hlive).family input).leftData Finset.univ b z).slotCoefficient i)⁻¹ ∈
        (((rightPoolFactory DE D S χ valuation prime leaf hS hlive).family input).leftData Finset.univ b z).theta) ∧
      (∀ i, ((((rightPoolFactory DE D S χ valuation prime leaf hS hlive).family input).rightData Finset.univ b z).slotCoefficient i)⁻¹ ∈
        (((rightPoolFactory DE D S χ valuation prime leaf hS hlive).family input).rightData Finset.univ b z).theta) := by
  intro input b z
  exact actual_family_inverse_slots ((rightPoolFactory DE D S χ valuation prime leaf hS hlive).family input) Finset.univ
    (by
      intro label mode i
      change ((data ξ).slotCoefficient _)⁻¹ ∈ (data ξ).theta
      exact hinverse _)
    (by
      intro label mode i
      change ((data ξ).slotCoefficient _)⁻¹ ∈ (data ξ).theta
      exact hinverse _) b z

end RightValuation

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

local notation "leftMainInverse" => literalPrimitiveLeftMainFactory_slot_inverse_mem_theta
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
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity) (hinverse := hinverse)

local notation "leftPoolInverse" => literalPrimitiveLeftPoolFactory_slot_inverse_mem_theta
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
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity) (hinverse := hinverse)

local notation "rightMainInverse" => literalPrimitiveRightMainFactory_slot_inverse_mem_theta
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
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity) (hinverse := hinverse)

local notation "rightPoolInverse" => literalPrimitiveRightPoolFactory_slot_inverse_mem_theta
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
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity) (hinverse := hinverse)

theorem literalPrimitivePooledFactory_slot_inverse_mem_theta
    (j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization) :
    ∀ (input : (factories j).Input)
      (b : ((factories j).family input).active Finset.univ) (z : WithLp 2 (ℝ × ℝ)),
      (∀ i, ((((factories j).family input).leftData Finset.univ b z).slotCoefficient i)⁻¹ ∈
        (((factories j).family input).leftData Finset.univ b z).theta) ∧
      (∀ i, ((((factories j).family input).rightData Finset.univ b z).slotCoefficient i)⁻¹ ∈
        (((factories j).family input).rightData Finset.univ b z).theta) := by
  have hS := stages.supported.gated.live_first_divisor_squarefree
    raw.originalAtlas exceptional normalization j
  have hparent := stages.supported.gated.liveLeaves_spec raw.originalAtlas exceptional normalization j
  rcases j with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩
  · have hblock := ((stages.supported.gated DE D).coveredLeaf raw.originalAtlas raw.originalAtlas
      (normalization.left DE D) (normalization.right DE D)
      (normalization.left_pos DE D) (normalization.right_pos DE D)
      (exceptional DE D) ⟨S, χ, .inl leaf⟩).live_of_scale_live _ _ hparent
    have hpool := (((stages DE D).left S χ).supported.gated.coveredLeaf ((source.pools DE D).leftSourceCovers raw.originalAtlas S χ)
      ((exceptional DE D).left S χ) (source.charts DE D).kernel (source.charts DE D).leftPoint leaf).live_of_scale_live _ _ hblock
    rcases leaf with leaf | (⟨prime, leaf⟩ | (⟨prime, leaf⟩ | ⟨prime, leaf⟩))
    · have hfiber := ((((stages DE D).left S χ).main).supported.gated.fiberCoveredLeaf
        (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).main) (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).main) (((exceptional DE D).left S χ).main)
        (source.charts DE D).kernel (source.charts DE D).leftPoint leaf).live_of_scale_live _ _ hpool
      exact leftMainInverse DE D S χ leaf hS hfiber
    · have hfiber := ((((stages DE D).left S χ).one prime).supported.gated.fiberCoveredLeaf
        (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).residual prime 1) (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).residual prime 1) (((exceptional DE D).left S χ).one prime)
        (source.charts DE D).kernel (fun i => (source.charts DE D).leftPoint i.val) leaf).live_of_scale_live _ _ hpool
      exact leftPoolInverse DE D S χ .one prime leaf hS hfiber
    · have hfiber := ((((stages DE D).left S χ).six prime).supported.gated.fiberCoveredLeaf
        (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).residual prime 6) (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).residual prime 6) (((exceptional DE D).left S χ).six prime)
        (source.charts DE D).kernel (fun i => (source.charts DE D).leftPoint i.val) leaf).live_of_scale_live _ _ hpool
      exact leftPoolInverse DE D S χ .six prime leaf hS hfiber
    · have hfiber := ((((stages DE D).left S χ).seven prime).supported.gated.fiberCoveredLeaf
        (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).residual prime 7) (((source.pools DE D).leftSourceCovers raw.originalAtlas S χ).residual prime 7) (((exceptional DE D).left S χ).seven prime)
        (source.charts DE D).kernel (fun i => (source.charts DE D).leftPoint i.val) leaf).live_of_scale_live _ _ hpool
      exact leftPoolInverse DE D S χ .seven prime leaf hS hfiber
  · have hblock := ((stages.supported.gated DE D).coveredLeaf raw.originalAtlas raw.originalAtlas
      (normalization.left DE D) (normalization.right DE D)
      (normalization.left_pos DE D) (normalization.right_pos DE D)
      (exceptional DE D) ⟨S, χ, .inr leaf⟩).live_of_scale_live _ _ hparent
    have hpool := (((stages DE D).right S χ).supported.gated.coveredLeaf ((source.pools DE D).rightSourceCovers raw.originalAtlas S χ)
      ((exceptional DE D).right S χ) (source.charts DE D).kernel (fun i => -(source.charts DE D).rightPoint i) leaf).live_of_scale_live _ _ hblock
    rcases leaf with leaf | (⟨prime, leaf⟩ | (⟨prime, leaf⟩ | ⟨prime, leaf⟩))
    · have hfiber := ((((stages DE D).right S χ).main).supported.gated.fiberCoveredLeaf
        (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).main) (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).main) (((exceptional DE D).right S χ).main)
        (source.charts DE D).kernel (fun i => -(source.charts DE D).rightPoint i) leaf).live_of_scale_live _ _ hpool
      exact rightMainInverse DE D S χ leaf hS hfiber
    · have hfiber := ((((stages DE D).right S χ).one prime).supported.gated.fiberCoveredLeaf
        (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).residual prime 1) (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).residual prime 1) (((exceptional DE D).right S χ).one prime)
        (source.charts DE D).kernel (fun i => -(source.charts DE D).rightPoint i.val) leaf).live_of_scale_live _ _ hpool
      exact rightPoolInverse DE D S χ .one prime leaf hS hfiber
    · have hfiber := ((((stages DE D).right S χ).six prime).supported.gated.fiberCoveredLeaf
        (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).residual prime 6) (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).residual prime 6) (((exceptional DE D).right S χ).six prime)
        (source.charts DE D).kernel (fun i => -(source.charts DE D).rightPoint i.val) leaf).live_of_scale_live _ _ hpool
      exact rightPoolInverse DE D S χ .six prime leaf hS hfiber
    · have hfiber := ((((stages DE D).right S χ).seven prime).supported.gated.fiberCoveredLeaf
        (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).residual prime 7) (((source.pools DE D).rightSourceCovers raw.originalAtlas S χ).residual prime 7) (((exceptional DE D).right S χ).seven prime)
        (source.charts DE D).kernel (fun i => -(source.charts DE D).rightPoint i.val) leaf).live_of_scale_live _ _ hpool
      exact rightPoolInverse DE D S χ .seven prime leaf hS hfiber

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

local notation "factoryInverse" => literalPrimitivePooledFactory_slot_inverse_mem_theta
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
  (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity) (hinverse := hinverse)

/-- The final amplified family has precisely the same outer live key,
inner passive label and chosen children as the original producer. -/
theorem literalPrimitivePooled_family_slot_inverse_mem_theta
    (analytic : ∀ j : stages.supported.gated.liveLeaves raw.originalAtlas exceptional normalization,
      (factories j).Input) :
    ∀ (b : (completeFamily analytic).active Finset.univ) (z : WithLp 2 (ℝ × ℝ)),
      (∀ i, (((completeFamily analytic).leftData Finset.univ b z).slotCoefficient i)⁻¹ ∈
        ((completeFamily analytic).leftData Finset.univ b z).theta) ∧
      (∀ i, (((completeFamily analytic).rightData Finset.univ b z).slotCoefficient i)⁻¹ ∈
        ((completeFamily analytic).rightData Finset.univ b z).theta) := by
  have hleft := ActualNormalizedPairFamily.sigmaCombine_left_slot_inverse_mem_theta
    (fun j => (factories j).family (analytic j)) Finset.univ (fun _ => Finset.univ)
    (fun j _ b z i => (factoryInverse j (analytic j) b z).1 i)
  have hright := ActualNormalizedPairFamily.sigmaCombine_right_slot_inverse_mem_theta
    (fun j => (factories j).family (analytic j)) Finset.univ (fun _ => Finset.univ)
    (fun j _ b z i => (factoryInverse j (analytic j) b z).2 i)
  simpa only [Finset.univ_sigma_univ] using
    (fun b z => And.intro (hleft b z) (hright b z))

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftMainFactory_slot_inverse_mem_theta
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightMainFactory_slot_inverse_mem_theta
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftPoolFactory_slot_inverse_mem_theta
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightPoolFactory_slot_inverse_mem_theta
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledFactory_slot_inverse_mem_theta
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooled_family_slot_inverse_mem_theta
