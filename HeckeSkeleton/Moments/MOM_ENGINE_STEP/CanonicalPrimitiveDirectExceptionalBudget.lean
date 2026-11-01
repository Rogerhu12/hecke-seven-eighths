import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveDirectEngine
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveExceptionalChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineSetup
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectExceptionalIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalExactIndex

/-!
# The complete direct exceptional budget from the original inputs

This independent integration candidate uses the exact direct source and its
original live-key arithmetic carrier. The raw profile representatives are
restricted only in their finite seminorm orders. The existing integral proof
constructs every actual exceptional rectangle and both Fourier integrals.
The original scalar, row classifier and exact inner divisor then supply the
fixed arithmetic estimate selected before the moving source.

The internal annulus lower bound is supplied by the public `annularBox`.
There is no input exceptional leaf bound or normalized family mass bound.
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
open CanonicalPrimitiveEngineChoices

private theorem exceptional_sourceOrders_mono
    {s t : Finset (ℕ × ℕ)} (h : s ⊆ t) :
    CanonicalLogProfiles.sourceOrders s ⊆ CanonicalLogProfiles.sourceOrders t := by
  intro p hp
  change p ∈ Finset.Iic (s.sup Prod.fst, s.sup Prod.snd) at hp
  change p ∈ Finset.Iic (t.sup Prod.fst, t.sup Prod.snd)
  have hp' := Finset.mem_Iic.mp hp
  exact Finset.mem_Iic.mpr
    ⟨hp'.1.trans (Finset.sup_mono h), hp'.2.trans (Finset.sup_mono h)⟩

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

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (b : Box) (orders : Finset (ℕ × ℕ))
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
variable (hcap : (data ξ).geometry.slotCount ≤ b.cap)
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
variable (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta)
variable (hplaces : CanonicalLiteralExceptionalArithmetic.thetaBadPrimes (data ξ).theta ⊆ A.Sf)
variable (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive
  ψ (data ξ).theta (Set.Icc b.lo b.hi))
variable (hlower : b.hi⁻¹ ≤ b.lo)
variable (hvolumeOrders : CanonicalPrimitiveExceptionalChoices.orders
  (A := A) (σ := σ) (η := η) (hS := hS) b primitive ⊆ orders)
variable (hlarge : CanonicalPrimitiveExceptionalChoices.threshold μv ν C hDiff b primitive ≤ Z)

local notation "Γ₀" => sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "hΓ₀" => actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "thresholds" => CanonicalPrimitiveExceptionalChoices.threshold_windows
  μv ν C hDiff b primitive Z hlarge
local notation "hfull" => thresholds.1
local notation "hZ" => domain.scale
local notation "fixedWindows" => CanonicalPrimitiveEngineOriginalWindows.fixed_windows b hfull
local notation "canonicalLeft" => canonicalComparisonScale centered (Z ^ a.n₁) Y₁
local notation "canonicalRight" => canonicalComparisonScale centered (Z ^ a.n₂) Y₂
local notation "paidDomain" =>
  (CanonicalPrimitiveEngineSetup.boundedDomain b domain hpadding).canonicalComparisonScales
local notation "scaleWindows" =>
  CanonicalPrimitiveEngineOriginalWindows.scale_windows b domain hwidth hpadding
local notation "window₂" => profiles.restrictOrders Finset.subset_union_right
local notation "volumeWindow" => (window₂).restrictOrders
  (exceptional_sourceOrders_mono (exceptional_sourceOrders_mono hvolumeOrders))
local notation "internal" => Q.fullSupportParameters a Z
local notation "raw" => ((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ)
  internal Z t).raw canonicalLeft canonicalRight
local notation "source" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t canonicalLeft canonicalRight hZ hbudget centered
  (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one (hZ).le) b.tilt b.tilt_pos b.tilt_le_half

local notation "stages" => Q.literalPrimitiveDirectStages
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
  («hZ» := hZ) (hbudget := hbudget) (centered := centered)
  (cutoff := b.firstBox.cutoff Z) (hcutoff := b.firstBox.cutoff_ge_one (hZ).le)
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := (fixedWindows).upper_annulus)
  (domain := paidDomain) (profiles := volumeWindow) (hrows := hrows) (ht := htime)
  (hwindow := fun _ h => h.2) (hcutoffPower := b.firstCutoff_le Z (hZ).le)
  (step := b.step) (hstep := b.step_pos) (hloss := b.loss_pos.le)
  (hcutoffExponent := b.loss_pos.le) (hDiff := hDiff)
  (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := b.secondCutoff Z) (hcutoff₂ := b.secondCutoff_ge_one Z (hZ).le)
local notation "exceptional" => Q.literalPrimitiveDirectPredicates
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
  («hZ» := hZ) (hbudget := hbudget) (centered := centered)
  (cutoff := b.firstBox.cutoff Z) (hcutoff := b.firstBox.cutoff_ge_one (hZ).le)
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := (fixedWindows).upper_annulus)
  (domain := paidDomain) (profiles := volumeWindow) (hrows := hrows) (ht := htime)
  (hwindow := fun _ h => h.2) (hcutoffPower := b.firstCutoff_le Z (hZ).le)
  (step := b.step) (hstep := b.step_pos) (hloss := b.loss_pos.le)
  (hcutoffExponent := b.loss_pos.le) (hDiff := hDiff)
  (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := b.secondCutoff Z) (hcutoff₂ := b.secondCutoff_ge_one Z (hZ).le)
local notation "normalization" => Q.literalPrimitiveFirstNormalization μv ν C hroot hemb W ξ
  a Z t canonicalLeft canonicalRight hZ hbudget centered
  (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one (hZ).le) b.tilt b.tilt_pos b.tilt_le_half
local notation "parents" => (stages).prepared
local notation "keys" => (parents).liveLeaves (raw).originalAtlas exceptional normalization
local notation "labels" => (parents).arithmeticLabels (raw).originalAtlas hcap exceptional normalization
local notation "control" => CanonicalPrimitiveEngineControl.value amplitude t
local notation "degree" => CanonicalPrimitiveExceptionalChoices.degree b
local notation "integralC" => CanonicalPrimitiveExceptionalChoices.integralCoefficient
  (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive
local notation "leafC" => CanonicalPrimitiveExceptionalChoices.leafCoefficient
  (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive
local notation "loss" => (if centered then b.paddingMax else 0) + 3 * b.step + b.ε / 2 +
  CanonicalPrimitiveExceptionalChoices.firstTiltError b
local notation "cost" => Q.literalPrimitiveDirectEngineExceptionalCost
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
  (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hcap := hcap) (hlarge := hfull)
  (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (htime := htime)

include hwidth hpadding hamplitude href hprime hone hplaces hlower hvolumeOrders in
/-- The complete original direct exceptional term has the fixed engine
constant and degree. All leaf, scalar, fibre and arithmetic inputs are
constructed from the displayed original data. -/
theorem literalPrimitiveDirectEngineExceptionalCost_le :
    cost ≤ CanonicalPrimitiveExceptionalChoices.constant μv ν C hDiff b primitive *
      control ^ degree * Z ^ (b.paddingMax + 3 * b.step + b.ε) := by
  have hP : 0 ≤ amplitude := zero_le_one.trans hamplitude
  have hcontrol : 1 ≤ control := CanonicalPrimitiveEngineControl.one_le amplitude t hamplitude
  have hN : ∀ i ∈ (source).columns,
      (Ideal.absNorm ((source).ideal i).val : ℝ) ≤ Z ^ b.columnBound :=
    Q.literalPrimitiveFirstSource_column_norm
      (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
      («hZ» := hZ) (hbudget := hbudget) (centered := centered)
      (cutoff := b.firstBox.cutoff Z) (hcutoff := b.firstBox.cutoff_ge_one (hZ).le)
      (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
      (cap := b.cap) (annulus := b.hi) («loss» := b.loss)
      (leftExponent := b.lengthBound) (rightExponent := b.lengthBound)
      (normBound := b.columnBound) (hannulus := b.hi_ge_one) (hcap := hcap)
      (hannulusZ := (fixedWindows).upper_annulus)
      (hY₁ := scaleWindows.1) (hY₂ := scaleWindows.2.1)
      (hleftPower := scaleWindows.2.2.1) (hrightPower := scaleWindows.2.2.2.1)
      (hY₁le := scaleWindows.2.2.2.2.1) (hY₂le := scaleWindows.2.2.2.2.2.1)
      (profiles := profiles) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
      (hcolumn := scaleWindows.2.2.2.2.2.2.2)
  let rows := Q.literalPrimitivePreparedDirectStagesOriginalFibreRows
    (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
    (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
    («hZ» := hZ) (hbudget := hbudget) (centered := centered)
    (cutoff := b.firstBox.cutoff Z) (hcutoff := b.firstBox.cutoff_ge_one (hZ).le)
    (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
    (cap := b.cap) (annulus := b.hi) («loss» := b.loss) (cutoffExponent := b.loss)
    (hannulus := b.hi_ge_one) (hcap := hcap) (hannulusZ := (fixedWindows).upper_annulus)
    (domain := paidDomain) (profiles := volumeWindow) (hrows := hrows) (ht := htime)
    (hwindow := fun _ h => h.2) (hcutoffPower := b.firstCutoff_le Z (hZ).le)
    (step := b.step) (hstep := b.step_pos) (hloss := b.loss_pos.le)
    (hcutoffExponent := b.loss_pos.le) (hDiff := hDiff)
    (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
    (cutoff₂ := b.secondCutoff Z) (hcutoff₂ := b.secondCutoff_ge_one Z (hZ).le)
    b.columnBound b.columnBound_nonneg hN
  let lower : keys → ℝ := fun i => idealLogLength Z ((parents).innerDivisor (raw).originalAtlas i.val)
  have hdivisor (i : keys) : (parents).innerDivisor (raw).originalAtlas i.val ≠ 0 :=
    ((stages).prepared_live_inner_divisor_squarefree (raw).originalAtlas exceptional normalization i).ne_zero
  have hwindow (i : keys) :
      (Ideal.absNorm ((parents).innerDivisor (raw).originalAtlas i.val) : ℝ) ≤ Z ^ (lower i + 0) := by
    dsimp only [lower]
    rw [add_zero]
    exact (rpow_idealLogLength Z hZ _ (hdivisor i)).ge
  have hindex (i : keys) :
      (labels).carrier.exceptionalDyadWeight Z (lower i) ((labels).index i) =
        (labels).carrier.indexWeight ((labels).index i) := by
    have hi := (parents).originalIndex_innerDivisor (raw).originalAtlas hcap exceptional normalization i
    have hn : ((labels).index i).2.2.2.1.val ≠ 0 := by
      change ((parents).originalIndex (raw).originalAtlas hcap exceptional normalization i).2.2.2.1.val ≠ 0
      rw [hi]
      exact hdivisor i
    change (labels).carrier.exceptionalDyadWeight Z
      (idealLogLength Z ((parents).innerDivisor (raw).originalAtlas i.val))
      ((parents).originalIndex (raw).originalAtlas hcap exceptional normalization i) = _
    rw [← hi]
    exact (labels).carrier.exceptionalDyadWeight_at_divisor Z hZ _ hn
  have hden : Z ^ ((internal).m + (internal).q) = Z ^ (a.m + a.q) :=
    congrArg (fun e : ℝ => Z ^ e) (Q.fullSupportParameters_width a Z)
  have hleafC : 0 ≤ leafC := CanonicalPrimitiveExceptionalChoices.leafCoefficient_nonneg
    (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive
  have hI : 0 ≤ integralC := CanonicalPrimitiveExceptionalChoices.integralCoefficient_nonneg
    (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive
  have hpoint (i : keys) :
      ((parents).parentLeaf (raw).originalAtlas exceptional normalization i.val).exceptionalCost /
          Z ^ ((internal).m + (internal).q) ≤
        leafC * control ^ degree * Z ^ loss *
          (labels).carrier.exceptionalDyadWeight Z (lower i) ((labels).index i) := by
    have hfirstBox : b.columnBound ≤ CanonicalPrimitiveExceptionalChoices.sourceWidth b := by
      have hs := CanonicalPrimitiveExceptionalChoices.firstSupportWidth_le b
      linarith [b.step_pos]
    have hp := Q.literalPrimitiveDirectExceptional_integral
      (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
      («hZ» := hZ) (hbudget := hbudget) (centered := centered)
      (cutoff := b.firstBox.cutoff Z) (hcutoff := b.firstBox.cutoff_ge_one (hZ).le)
      (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
      (hY₁ := scaleWindows.1) (hY₂ := scaleWindows.2.1)
      (cap := b.cap) («loss» := b.loss) (cutoffExponent := b.loss)
      (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
      (step := b.step) (hstep := b.step_pos) (hDiff := hDiff)
      (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
      (cutoff₂ := b.secondCutoff Z) (hcutoff₂ := b.secondCutoff_ge_one Z (hZ).le)
      (hcutoffPower := b.firstCutoff_le Z (hZ).le) (hcutoffPower₂ := b.secondCutoff_le Z (hZ).le)
      (reference := reference) (href := href) (lo := b.lo) (hi := b.hi)
      (hlo := b.lo_pos) (hhi := b.hi_ge_one) (primitive := primitive)
      (ε := CanonicalPrimitiveExceptionalChoices.volumeLoss b)
      (widthMax := CanonicalPrimitiveExceptionalChoices.sourceWidth b)
      (hε := CanonicalPrimitiveExceptionalChoices.volumeLoss_pos b)
      (hwidthMax := CanonicalPrimitiveExceptionalChoices.sourceWidth_nonneg b)
      (originalBound := amplitude) (hamplitude := hamplitude) (originalWindow := volumeWindow)
      (hrows := hrows) (htime := htime) (hprime := hprime)
      (hcap := hcap) (hannulusZ := (fixedWindows).upper_annulus) (domain := paidDomain)
      (hone := hone) (hplaces := hplaces) (hlower := hlower)
      (hδsum := CanonicalPrimitiveEngineOriginalWindows.tilt_sum_le_half b)
      (slotLoss := b.loss) (finalLoss := b.ε) (hslotLossNonneg := b.loss_pos.le)
      (hfinalLoss := b.ε_pos.le) (hslotLoss := (fixedWindows).single_annulus)
      (hslots := by linarith [b.cap_mul_loss_le_ε, b.ε_pos])
      (hsupport := by linarith [b.loss_le_ε, b.ε_pos])
      (hvolume := by
        unfold CanonicalPrimitiveExceptionalChoices.volumeLoss
        linarith [b.ε_pos])
      (hwidth := hwidth.trans (CanonicalPrimitiveExceptionalChoices.parentWidth_le b))
      (hthreshold := thresholds.2.1) (normBound := b.columnBound)
      (lengthBound := b.lengthBound) (hlengthBound := b.lengthBound_nonneg)
      (htotal := scaleWindows.2.2.2.2.2.2.1) (hfirstBox := hfirstBox) (hN := hN)
      (hpadding := fun _ => b.padding_nonneg) i
    have hp' :
        ((parents).parentLeaf (raw).originalAtlas exceptional normalization i.val).exceptionalCost /
          Z ^ (a.m + a.q) ≤ (parents).originalScalarAt (raw).originalAtlas i.val *
            (integralC * amplitude ^ degree * Z ^ loss *
              (labels).carrier.indexWeight ((labels).index i)) := by
      simpa only [CanonicalPrimitiveExceptionalChoices.degree_eq] using hp
    have hs := Q.literalPrimitiveDirect_originalScalar_bounds
      (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
      («hZ» := hZ) (hbudget := hbudget) (centered := centered)
      (cutoff := b.firstBox.cutoff Z) (hcutoff := b.firstBox.cutoff_ge_one (hZ).le)
      (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
      (cap := b.cap) («loss» := b.loss) (cutoffExponent := b.loss)
      (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
      (step := b.step) (hstep := b.step_pos) (hDiff := hDiff)
      (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
      (cutoff₂ := b.secondCutoff Z) (hcutoff₂ := b.secondCutoff_ge_one Z (hZ).le)
      (hcutoffPower := b.firstCutoff_le Z (hZ).le)
      (lo := b.lo) (hi := b.hi) (hhi := b.hi_ge_one)
      (orders := CanonicalPrimitiveExceptionalChoices.orders
        (A := A) (σ := σ) (η := η) (hS := hS) b primitive)
      (originalBound := amplitude) (originalWindow := volumeWindow)
      (hrows := hrows) (htime := htime) (hcap := hcap)
      (hannulusZ := (fixedWindows).upper_annulus) (domain := paidDomain) i
    have hsCap : (parents).originalScalarAt (raw).originalAtlas i.val ≤
        CanonicalPrimitiveExceptionalChoices.fiberCap b := by
      linarith [hs.2, CanonicalPrimitiveExceptionalChoices.fiberCap_one b]
    have hi : 0 ≤ (labels).carrier.indexWeight ((labels).index i) := (labels).carrier.indexWeight_nonneg _
    have hpow := pow_le_pow_left₀ hP
      (CanonicalPrimitiveEngineControl.amplitude_le amplitude t hamplitude) degree
    calc
      _ = ((parents).parentLeaf (raw).originalAtlas exceptional normalization i.val).exceptionalCost /
          Z ^ (a.m + a.q) := congrArg
        (fun r : ℝ => ((parents).parentLeaf (raw).originalAtlas exceptional normalization i.val).exceptionalCost / r) hden
      _ ≤ (parents).originalScalarAt (raw).originalAtlas i.val *
          (integralC * amplitude ^ degree * Z ^ loss * (labels).carrier.indexWeight ((labels).index i)) := hp'
      _ ≤ CanonicalPrimitiveExceptionalChoices.fiberCap b *
          (integralC * amplitude ^ degree * Z ^ loss * (labels).carrier.indexWeight ((labels).index i)) :=
        mul_le_mul_of_nonneg_right hsCap
          (mul_nonneg (mul_nonneg (mul_nonneg hI (pow_nonneg hP _))
            (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hi)
      _ = leafC * amplitude ^ degree * Z ^ loss * (labels).carrier.indexWeight ((labels).index i) := by
        unfold CanonicalPrimitiveExceptionalChoices.leafCoefficient
        ring
      _ ≤ leafC * control ^ degree * Z ^ loss * (labels).carrier.indexWeight ((labels).index i) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hleafC)
            (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hi
      _ = _ := congrArg (fun r : ℝ => leafC * control ^ degree * Z ^ loss * r) (hindex i).symm
  have hmask : OriginalMaskPrimeData (source).mask (1 : Ideal (𝓞 K)) := emptyOriginalSIntegerMask
  have hmaskNorm : (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℝ) ≤ Z ^ b.columnBound := by
    simpa only [map_one, Nat.cast_one] using Real.one_le_rpow (hZ).le b.columnBound_nonneg
  have hsum := CanonicalPrimitiveExceptionalChoices.direct_bound
    (A := A) (σ := σ) (η := η) (hS := hS) μv ν C hDiff b primitive
    Z hZ control hcontrol loss centered (data ξ) internal t canonicalLeft canonicalRight
    (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one (hZ).le)
    source stages (raw).originalAtlas hcap exceptional normalization rows
    (1 : Ideal (𝓞 K)) squarefree_one one_ne_zero (fun _ _ => one_dvd _)
    (1 : Ideal (𝓞 K)) one_ne_zero hmask hmaskNorm hN lower 0 hwindow hpoint
  have hpad : (if centered then b.paddingMax else 0) ≤ b.paddingMax := by
    split_ifs
    · exact le_rfl
    · exact b.padding_nonneg
  have hexponent : loss + CanonicalPrimitiveExceptionalChoices.indexLoss b +
      CanonicalPrimitiveExceptionalChoices.indexLoss b +
      CanonicalPrimitiveExceptionalChoices.indexLoss b + 0 ≤
        b.paddingMax + 3 * b.step + b.ε := by
    simpa only [add_zero] using
      (le_add_of_nonneg_right b.loss_pos.le).trans
        (CanonicalPrimitiveExceptionalChoices.terminal_exponent_le b
          (if centered then b.paddingMax else 0) hpad)
  have hconstant : CanonicalPrimitiveExceptionalChoices.directConstant μv ν C hDiff b primitive ≤
      CanonicalPrimitiveExceptionalChoices.constant μv ν C hDiff b primitive := by
    have hp := CanonicalPrimitiveExceptionalChoices.pooledConstant_pos μv ν C hDiff b primitive
    unfold CanonicalPrimitiveExceptionalChoices.constant
    linarith
  calc
    cost = (parents).exceptionalBudget (raw).originalAtlas exceptional normalization /
        Z ^ ((internal).m + (internal).q) := by
      change (parents).exceptionalBudget (raw).originalAtlas exceptional normalization /
        Z ^ (a.m + a.q) = _
      exact congrArg
        (fun r : ℝ => (parents).exceptionalBudget (raw).originalAtlas exceptional normalization / r) hden.symm
    _ ≤ CanonicalPrimitiveExceptionalChoices.directConstant μv ν C hDiff b primitive *
        control ^ degree * Z ^ (loss + CanonicalPrimitiveExceptionalChoices.indexLoss b +
          CanonicalPrimitiveExceptionalChoices.indexLoss b +
          CanonicalPrimitiveExceptionalChoices.indexLoss b + 0) /
            (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℝ) := hsum
    _ = CanonicalPrimitiveExceptionalChoices.directConstant μv ν C hDiff b primitive *
        control ^ degree * Z ^ (loss + CanonicalPrimitiveExceptionalChoices.indexLoss b +
          CanonicalPrimitiveExceptionalChoices.indexLoss b +
          CanonicalPrimitiveExceptionalChoices.indexLoss b + 0) := by simp only [map_one, Nat.cast_one, div_one]
    _ ≤ _ := CanonicalPrimitiveEngineControl.monomial_mono
      (CanonicalPrimitiveExceptionalChoices.constant_pos μv ν C hDiff b primitive).le
      hconstant hcontrol (hZ).le le_rfl hexponent

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectEngineExceptionalCost_le
