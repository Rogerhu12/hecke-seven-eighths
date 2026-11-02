import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitivePooledEngine
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineSetup
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveExceptionalChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledExceptionalIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledScalar
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalExactIndex

set_option linter.unusedSectionVars false

/-!
# The complete exceptional budget of the original pooled engine

This candidate keeps the already selected pool and the literal supported,
gated source. Its original scalar, moving prime power and allocation
divisor become the original amplified arithmetic index before the uniform
index estimate is invoked. The actual second-row fibre cap occurs once.
All pointwise and source estimates are constructed from original windows.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
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

open CanonicalPrimitiveEngineChoices HeckeGeneral.Bridge


private theorem exceptional_sourceOrders_mono {s t : Finset (ℕ × ℕ)} (h : s ⊆ t) :
    CanonicalLogProfiles.sourceOrders s ⊆ CanonicalLogProfiles.sourceOrders t := by
  sorry

private theorem exceptional_global_local_weight
    {I : Type*} [Fintype I] {cap : ℕ}
    (L : OriginalArithmeticLabels K I cap)
    (tag : I → Option (ℕ × ExteriorPrime A)) (i : I) :
    L.carrier.indexWeight (L.index i) =
      (L.localBranch tag i).indexWeight (L.localIndex tag i) := by
  sorry

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
variable (hlower : b.hi⁻¹ ≤ b.lo)
variable (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive ψ (data ξ).theta
  (Set.Icc b.lo b.hi))
variable (horders : CanonicalPrimitiveExceptionalChoices.orders
  (A := A) (σ := σ) (η := η) (hS := hS) b primitive ⊆ orders)
variable (hexceptionalLarge : CanonicalPrimitiveExceptionalChoices.threshold
  μv ν C hDiff b primitive ≤ Z)

local notation "hlarge" => (CanonicalPrimitiveExceptionalChoices.threshold_windows
  μv ν C hDiff b primitive Z hexceptionalLarge).1
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
local notation "control" => CanonicalPrimitiveEngineControl.value amplitude t
local notation "internal" => Q.fullSupportParameters a Z
local notation "raw" => ((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ)
  internal Z t).raw canonicalLeft canonicalRight
local notation "firstSource" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t canonicalLeft canonicalRight hZ hbudget centered
  (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one (hZ).le) b.tilt b.tilt_pos b.tilt_le_half


local notation "hN" => Q.literalPrimitiveFirstSource_column_norm μv ν C hroot hemb W ξ
  a Z t canonicalLeft canonicalRight hZ hbudget centered
  (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one (hZ).le) b.tilt b.tilt_pos b.tilt_le_half
  b.cap b.hi b.loss b.lengthBound b.lengthBound b.columnBound b.hi_ge_one hcap hannulusZ
  hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le window₂ hrows htime (fun _ h => h.2) hcolumn

variable {bad : Finset (HeightOneSpectrum (𝓞 K))}
variable (pool : PowerScaleExteriorPool A bad Z (b.step / 3) b.loss)
variable (hdensity : 0 < pool.rowDensity b.rowBound b.columnBound)

local notation "source" => Q.literalPrimitivePooledSource
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) («hZ» := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) («hannulusZ» := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  («htotal» := htotal) («hN» := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)

local notation "stages" => Q.literalPrimitivePooledStages
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) («hZ» := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) («hannulusZ» := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  («htotal» := htotal) («hN» := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)
  (hstep := b.step_pos) (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))

local notation "exceptional" => Q.literalPrimitivePooledPredicates
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) («hZ» := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) («hannulusZ» := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  («htotal» := htotal) («hN» := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)
  (hstep := b.step_pos) (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))

local notation "normalization" => Q.literalPrimitivePooledNormalization
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) («hZ» := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) («hannulusZ» := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  («htotal» := htotal) («hN» := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)

local notation "actualRows" => Q.literalPrimitivePreparedPooledStagesOriginalFibreRows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight) («hZ» := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := (b.firstBox.cutoff Z)) (hcutoff := (b.firstBox.cutoff_ge_one (hZ).le))
  (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (cap := b.cap) (annulus := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
  (hannulus := b.hi_ge_one) (hcap := hcap) («hannulusZ» := hannulusZ) (domain := canonicalDomain)
  (profiles := window₂) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := (b.firstCutoff_le Z (hZ).le)) (reference := reference) (href := href)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  («htotal» := htotal) («hN» := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
  (pool := pool) (hdensity := hdensity)
  (hstep := b.step_pos) (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (cutoff₂ := (b.secondCutoff Z)) (hcutoff₂ := (b.secondCutoff_ge_one Z (hZ).le))

local notation "parents" => (stages).supported.gated
local notation "labels" => (parents).arithmeticLabels (raw).originalAtlas hcap exceptional normalization
local notation "tags" => (parents).arithmeticTag (raw).originalAtlas exceptional normalization
local notation "indices" => (parents).arithmeticIndex (raw).originalAtlas hcap exceptional normalization
local notation "liveKeys" => (parents).liveLeaves (raw).originalAtlas exceptional normalization
local notation "movingAt" => fun (i : liveKeys) =>
  ((parents).originalNominalTagAt (raw).originalAtlas i.val).movingLength Z +
    ((parents).originalNominalTagAt (raw).originalAtlas i.val).poolLength b.step
local notation "localWeight" => fun (i : liveKeys) =>
  ((labels).localBranch tags i).indexWeight ((labels).localIndex tags i)
local notation "amplifiedWeight" => fun (i : liveKeys) =>
  amplifiedIndexWeight pool b.rowBound b.columnBound
    ((labels).mainCarrier tags) ((labels).errorCarrier tags) (indices i)
local notation "lower" => fun (i : liveKeys) =>
  idealLogLength Z ((parents).innerDivisor (raw).originalAtlas i.val)
local notation "volumeOrders" => CanonicalPrimitiveExceptionalChoices.orders
  (A := A) (σ := σ) (η := η) (hS := hS) b primitive
local notation "integralC" => CanonicalPrimitiveExceptionalChoices.integralCoefficient
  (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive
local notation "leafC" => CanonicalPrimitiveExceptionalChoices.leafCoefficient
  (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive
local notation "degree" => CanonicalPrimitiveExceptionalChoices.degree b
local notation "paidLoss" => b.paddingMax + 3 * b.step + b.ε / 2 +
  CanonicalPrimitiveExceptionalChoices.firstTiltError b
local notation "cost" => Q.literalPrimitivePooledEngineExceptionalCost
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
  (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
  (hcap := hcap) («hlarge» := hlarge) (reference := reference) (href := href)
  (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (htime := htime)
  (pool := pool) (hdensity := hdensity)

include hamplitude hprime hone hplaces hlower horders in
/-- The original pooled exceptional budget from the original annular
profiles, the raw fixed-character volume primitive and the same selected
pool. Neither a completed leaf estimate nor an index-mass bound is input. -/
theorem literalPrimitivePooledEngineExceptionalCost_le :
    cost ≤ CanonicalPrimitiveExceptionalChoices.constant μv ν C hDiff b primitive *
      control ^ degree * Z ^ (b.paddingMax + 3 * b.step + b.ε) := by
  sorry

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledEngineExceptionalCost_le
