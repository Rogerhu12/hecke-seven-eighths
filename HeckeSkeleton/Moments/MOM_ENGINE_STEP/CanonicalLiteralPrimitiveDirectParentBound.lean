import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectSourceIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveParentBound
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PreparedDualBudgetBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonGaussOrigin

/-!
# The original direct parent reaches its existing complete family

The original sector tensors prove their signed-origin conditions internally.
The universal second-stage estimate is applied to the same prepared stages,
and their terminal budgets are bounded by the original budgets. The ordinary
source uses its proved integral bound on the existing dependent family.
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

local notation "ordinaryKernel" => literalPrimitiveDirect_ordinaryCost_le_kernel
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

variable {sTail sZero : Finset (ℕ × ℕ)} {terminalSlots : ℕ}
variable {Lmax Nsave decay εzero Cerror Czero : ℝ}

/-- The same first finite rows are controlled by the two original second
terminals, the actual exceptional rows and the existing ordinary kernels. -/
theorem literalPrimitiveDirect_rawCost_le_kernel
    (T : stages.DualTerminalCalibration sTail sZero terminalSlots Lmax Nsave decay)
    (hCerror : 0 ≤ Cerror) (hCzero : 0 ≤ Czero)
    (hstage : ∀ {j : Type*} (G : ActualGaussSource C j)
      (stage : ActualGaussStage (E := ℝ)
        (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
        μv hDiff G (rowBallFiniteFamily K A.Sf 1))
      (hmask : stage.mask = ∅)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
        (traceSchwartzToMixed K stage.profile) (rowBallFiniteFamily K A.Sf 1) 0).re)
      (cal : stage.DualTerminalCalibration sTail sZero terminalSlots Z Lmax Nsave decay)
      (x : j → ℝ) (z : ℝ),
      G.phaseEnergy (hDiff := hDiff) x z ≤
        (cal.fourierPhase x z).rawCost εzero Cerror Czero)
    (analytic : ∀ j : stages.prepared.liveLeaves raw.originalAtlas exceptional normalization,
      (factories j).Input) :
    source.rawRowCost hDiff / Z ^ (a.m + a.q) ≤
      stages.dualSecondZeroBudget T normalization εzero Czero / Z ^ (a.m + a.q) +
        stages.dualSecondTailBudget T normalization Cerror / Z ^ (a.m + a.q) +
        stages.prepared.exceptionalBudget raw.originalAtlas exceptional normalization /
          Z ^ (a.m + a.q) +
        ∑ b : (completeFamily analytic).active Finset.univ,
          ∫ z, (completeFamily analytic).childPair Finset.univ b z
            ∂(completeFamily analytic).kernel Finset.univ completeMeasure (a.m + a.q) b := by
  have hcanonical : 0 ≤ (sIntegerTensorTerm K A.Sf
      (traceSchwartzToMixed K (CanonicalRowBall.archTest K A.Sf 1))
      (rowBallFiniteFamily K A.Sf 1) 0).re := by
    rw [CanonicalRowBall.originalTensor_zero, Complex.ofReal_re]
    exact inv_nonneg.mpr (CanonicalRowBall.mass_pos K A.Sf).le
  have conditions : stages.DualSourceConditions := by
    intro DE D
    exact {
      left_mask := fun _ _ => rfl
      right_mask := fun _ _ => rfl
      left_origin_nonneg := fun _ _ => hcanonical
      right_origin_nonneg := fun _ _ => hcanonical }
  have hraw := stages.prepared.rawRowCost_le_dual_live
    T.prepared conditions.prepared raw.originalAtlas exceptional normalization
    εzero Cerror Czero hstage
  have hzero := T.prepared_dualSecondZeroBudget_le normalization εzero Czero hCzero
  have htail := T.prepared_dualSecondTailBudget_le normalization Cerror hCerror
  have hfiber : source.fiber = 1 := rfl
  rw [hfiber, Nat.cast_one, one_mul] at hraw
  have htotal : source.rawRowCost hDiff ≤
      stages.dualSecondZeroBudget T normalization εzero Czero +
        stages.dualSecondTailBudget T normalization Cerror +
        stages.prepared.exceptionalBudget raw.originalAtlas exceptional normalization +
        stages.prepared.ordinaryBudget raw.originalAtlas exceptional normalization :=
    hraw.trans (add_le_add (add_le_add (add_le_add hzero htail) le_rfl) le_rfl)
  have hnormalized := div_le_div_of_nonneg_right htotal
    (Real.rpow_nonneg (zero_le_one.trans hZ.le) (a.m + a.q))
  simp only [add_div] at hnormalized
  have hord : stages.prepared.ordinaryBudget raw.originalAtlas exceptional normalization /
      Z ^ (a.m + a.q) ≤
      ∑ b : (completeFamily analytic).active Finset.univ,
          ∫ z, (completeFamily analytic).childPair Finset.univ b z
            ∂(completeFamily analytic).kernel Finset.univ completeMeasure (a.m + a.q) b := by
    simpa only [ActualDirectFirstSource.SecondStages.ordinaryBudget, ActualDirectFirstSource.SecondStages.liveLeaf] using
      ordinaryKernel analytic (a.m + a.q)
  exact hnormalized.trans (add_le_add_left hord _)

local notation "rawKernel" => literalPrimitiveDirect_rawCost_le_kernel
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

/-- The first signed exit and the separately bounded exceptional term
are combined with the proved source inequality on this exact family. -/
theorem literalPrimitiveDirect_parent_le_kernel
    (T : stages.DualTerminalCalibration sTail sZero terminalSlots Lmax Nsave decay)
    (hCerror : 0 ≤ Cerror) (hCzero : 0 ≤ Czero)
    (hstage : ∀ {j : Type*} (G : ActualGaussSource C j)
      (stage : ActualGaussStage (E := ℝ)
        (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
        μv hDiff G (rowBallFiniteFamily K A.Sf 1))
      (hmask : stage.mask = ∅)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
        (traceSchwartzToMixed K stage.profile) (rowBallFiniteFamily K A.Sf 1) 0).re)
      (cal : stage.DualTerminalCalibration sTail sZero terminalSlots Z Lmax Nsave decay)
      (x : j → ℝ) (z : ℝ),
      G.phaseEnergy (hDiff := hDiff) x z ≤
        (cal.fourierPhase x z).rawCost εzero Cerror Czero)
    (analytic : ∀ j : stages.prepared.liveLeaves raw.originalAtlas exceptional normalization,
      (factories j).Input)
    (firstZero firstTail exceptionalCost : ℝ)
    (hfirst : pairedStageEnergy centered (data ξ) a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
      firstZero + firstTail + source.rawRowCost hDiff / Z ^ (a.m + a.q))
    (hexceptional : stages.prepared.exceptionalBudget raw.originalAtlas exceptional normalization /
      Z ^ (a.m + a.q) ≤ exceptionalCost) :
    pairedStageEnergy centered (data ξ) a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
      firstZero + stages.dualSecondZeroBudget T normalization εzero Czero / Z ^ (a.m + a.q) +
        exceptionalCost +
        (firstTail + stages.dualSecondTailBudget T normalization Cerror / Z ^ (a.m + a.q)) +
        ∑ b : (completeFamily analytic).active Finset.univ,
          ∫ z, (completeFamily analytic).childPair Finset.univ b z
            ∂(completeFamily analytic).kernel Finset.univ completeMeasure (a.m + a.q) b := by
  have hraw := rawKernel T hCerror hCzero hstage analytic
  linarith only [hfirst, hraw, hexceptional]

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirect_rawCost_le_kernel
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirect_parent_le_kernel
