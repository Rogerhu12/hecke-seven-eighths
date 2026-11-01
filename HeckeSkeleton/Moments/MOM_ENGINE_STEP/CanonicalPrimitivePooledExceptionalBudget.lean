import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitivePooledEngine
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineSetup
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveExceptionalChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledExceptionalIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledScalar
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalExactIndex

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
  intro p hp
  have hp' : p ≤ (s.sup Prod.fst, s.sup Prod.snd) := Finset.mem_Iic.mp hp
  exact Finset.mem_Iic.mpr ⟨
    hp'.1.trans (Finset.sup_le fun q hq => Finset.le_sup (f := Prod.fst) (h hq)),
    hp'.2.trans (Finset.sup_le fun q hq => Finset.le_sup (f := Prod.snd) (h hq))⟩

private theorem exceptional_global_local_weight
    {I : Type*} [Fintype I] {cap : ℕ}
    (L : OriginalArithmeticLabels K I cap)
    (tag : I → Option (ℕ × ExteriorPrime A)) (i : I) :
    L.carrier.indexWeight (L.index i) =
      (L.localBranch tag i).indexWeight (L.localIndex tag i) := by
  cases h : tag i with
  | none => simp only [OriginalArithmeticLabels.localBranch,
      OriginalArithmeticLabels.localIndex, h] <;> rfl
  | some q => simp only [OriginalArithmeticLabels.localBranch,
      OriginalArithmeticLabels.localIndex, h] <;> rfl

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
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hp0 : 0 ≤ amplitude := zero_le_one.trans hamplitude
  have hc0 : 0 ≤ integralC :=
    CanonicalPrimitiveExceptionalChoices.integralCoefficient_nonneg
      (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive
  have hslot : b.hi ≤ Z ^ (2 * b.loss) := by
    calc
      b.hi = b.hi ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ b.hi ^ (b.cap + 2) := pow_le_pow_right₀ b.hi_ge_one (by omega)
      _ ≤ Z ^ b.loss := hannulusZ
      _ ≤ Z ^ (2 * b.loss) :=
        Real.rpow_le_rpow_of_exponent_le (hZ).le (by linarith [b.loss_pos])
  have hslots : (b.cap : ℝ) * b.loss ≤ b.ε / 16 := by
    linarith [b.cap_mul_loss_le_ε, b.ε_pos]
  have hsupport : 2 * b.loss + b.loss ≤ b.ε / 16 := by
    linarith [b.loss_le_ε, b.ε_pos]
  have hvolume : CanonicalPrimitiveExceptionalChoices.volumeLoss b ≤ b.ε / 16 := by
    unfold CanonicalPrimitiveExceptionalChoices.volumeLoss
    linarith [b.ε_pos]
  let smallWindow := (window₂).restrictOrders
    (exceptional_sourceOrders_mono (exceptional_sourceOrders_mono horders))
  have hprimeSmall : ∀ j, Function.support (smallWindow.primeRep j t) ⊆ Set.Ioo (1 : ℝ) 2 :=
    hprime
  let paidDomain := (CanonicalPrimitiveEngineSetup.boundedDomain b domain hpadding).canonicalComparisonScales
  have hpoint (i : liveKeys) :
      ((parents).parentLeaf (raw).originalAtlas exceptional normalization i.val).exceptionalCost /
          Z ^ (a.m + a.q) ≤
        (parents).originalScalarAt (raw).originalAtlas i.val *
          (integralC * amplitude ^ degree *
            Z ^ (((if centered then b.paddingMax else 0) + 3 * b.step + b.ε / 2) +
              CanonicalPrimitiveExceptionalChoices.firstTiltError b + movingAt i) *
            (labels).carrier.exceptionalDyadWeight Z (lower i) ((labels).index i)) := by
    have h := Q.literalPrimitivePooledExceptional_integral
      (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
      («hZ» := hZ) (hbudget := hbudget) (centered := centered)
      (cutoff := b.firstBox.cutoff Z) (hcutoff := b.firstBox.cutoff_ge_one (hZ).le)
      (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
      (hY₁ := hY₁) (hY₂ := hY₂) (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
      (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
      (step := b.step) (hstep := b.step_pos) (hDiff := hDiff)
      (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
      (cutoff₂ := b.secondCutoff Z) (hcutoff₂ := b.secondCutoff_ge_one Z (hZ).le)
      (hcutoffPower := b.firstCutoff_le Z (hZ).le) (hcutoffPower₂ := b.secondCutoff_le Z (hZ).le)
      (reference := reference) (href := href)
      (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
      (primitive := primitive) (ε := CanonicalPrimitiveExceptionalChoices.volumeLoss b)
      (widthMax := CanonicalPrimitiveExceptionalChoices.sourceWidth b)
      (hε := CanonicalPrimitiveExceptionalChoices.volumeLoss_pos b)
      (hwidthMax := CanonicalPrimitiveExceptionalChoices.sourceWidth_nonneg b)
      (originalBound := amplitude) (hamplitude := hamplitude)
      (originalWindow := smallWindow) (hrows := hrows) (htime := htime) (hprime := hprimeSmall)
      (hcap := hcap) («hannulusZ» := hannulusZ) (domain := paidDomain)
      (hone := hone) (hplaces := hplaces) (hlower := hlower)
      (hδsum := by linarith [b.tilt_le_quarter])
      (slotLoss := b.loss) (finalLoss := b.ε)
      (hslotLossNonneg := b.loss_pos.le) (hfinalLoss := b.ε_pos.le)
      (hslotLoss := hslot) (hslots := hslots) (hsupport := hsupport) (hvolume := hvolume)
      (hwidth := hwidth.trans (CanonicalPrimitiveExceptionalChoices.parentWidth_le b))
      (hthreshold := (CanonicalPrimitiveExceptionalChoices.threshold_windows
        μv ν C hDiff b primitive Z hexceptionalLarge).2.1)
      (lengthBound := b.lengthBound) (columnBound := b.columnBound)
      (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
      («htotal» := htotal) («hN» := hN)
      (hfirstBox := CanonicalPrimitiveExceptionalChoices.firstSupportWidth_le b)
      (pool := pool) (hdensity := hdensity) (fun _ => b.padding_nonneg) i
    simpa only [CanonicalPrimitiveExceptionalChoices.degree_eq] using h
  have hscalar (i : liveKeys) :
      (parents).originalScalarAt (raw).originalAtlas i.val * Z ^ movingAt i * localWeight i ≤
        CanonicalPrimitiveExceptionalChoices.fiberCap b * amplifiedWeight i := by
    exact Q.literalPrimitivePooled_originalScalar_moving_index_le
      (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
      (a := a) (Z := Z) (t := t) (Y₁ := canonicalLeft) (Y₂ := canonicalRight)
      («hZ» := hZ) (hbudget := hbudget) (centered := centered)
      (cutoff := b.firstBox.cutoff Z) (hcutoff := b.firstBox.cutoff_ge_one (hZ).le)
      (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
      (cap := b.cap) (hi := b.hi) (loss := b.loss) (cutoffExponent := b.loss)
      (hhi := b.hi_ge_one) (hcap := hcap) («hannulusZ» := hannulusZ) (domain := canonicalDomain)
      (lo := b.lo) (orders := orders) (originalBound := amplitude)
      (originalWindow := window₂) (hrows := hrows) (htime := htime)
      (hcutoffPower := b.firstCutoff_le Z (hZ).le) (reference := reference) (href := href)
      (lengthBound := b.lengthBound) (columnBound := b.columnBound)
      (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
      («htotal» := htotal) («hN» := hN) (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
      (pool := pool) (hdensity := hdensity) (step := b.step) (hstep := b.step_pos)
      (hDiff := hDiff) (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
      (cutoff₂ := b.secondCutoff Z) (hcutoff₂ := b.secondCutoff_ge_one Z (hZ).le) i
  have hdivisor (i : liveKeys) : (parents).innerDivisor (raw).originalAtlas i.val ≠ 0 :=
    ((stages).live_inner_divisor_squarefree (raw).originalAtlas exceptional normalization i).ne_zero
  have hglobalDivisor (i : liveKeys) :
      ((labels).index i).2.2.2.1.val = (parents).innerDivisor (raw).originalAtlas i.val :=
    (parents).arithmeticLabels_secondDivisor (raw).originalAtlas hcap exceptional normalization i
  have hglobal (i : liveKeys) :
      (labels).carrier.exceptionalDyadWeight Z (lower i) ((labels).index i) = localWeight i := by
    have h := (labels).carrier.exceptionalDyadWeight_at_divisor Z hZ ((labels).index i)
      (by rw [hglobalDivisor i]; exact hdivisor i)
    rw [hglobalDivisor i] at h
    exact h.trans (exceptional_global_local_weight labels tags i)
  have hamplifiedDivisor (i : liveKeys) :
      amplifiedInnerDivisor (indices i) = (parents).innerDivisor (raw).originalAtlas i.val :=
    (parents).arithmeticIndex_innerDivisor (raw).originalAtlas hcap exceptional normalization i
  have hamplified (i : liveKeys) :
      amplifiedExceptionalDyadWeight pool b.rowBound b.columnBound
          ((labels).mainCarrier tags) ((labels).errorCarrier tags) (lower i) (indices i) =
        amplifiedWeight i := by
    have h := amplifiedExceptionalDyadWeight_at_divisor pool b.rowBound b.columnBound
      ((labels).mainCarrier tags) ((labels).errorCarrier tags) (indices i)
      (by rw [hamplifiedDivisor i]; exact hdivisor i)
    simpa only [hamplifiedDivisor i] using h
  have hbase : ((if centered then b.paddingMax else 0) + 3 * b.step + b.ε / 2) +
      CanonicalPrimitiveExceptionalChoices.firstTiltError b ≤ paidLoss := by
    cases centered <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith [b.padding_nonneg]
  have hleaf (i : liveKeys) :
      ((parents).parentLeaf (raw).originalAtlas exceptional normalization i.val).exceptionalCost /
          Z ^ ((internal).m + (internal).q) ≤
        leafC * amplitude ^ degree * Z ^ paidLoss *
          amplifiedExceptionalDyadWeight pool b.rowBound b.columnBound
            ((labels).mainCarrier tags) ((labels).errorCarrier tags) (lower i) (indices i) := by
    rw [Q.fullSupportParameters_width, hamplified i]
    have hi := hpoint i
    rw [hglobal i] at hi
    have hweight : 0 ≤ localWeight i :=
      ((labels).localBranch tags i).indexWeight_nonneg ((labels).localIndex tags i)
    calc
      _ ≤ (parents).originalScalarAt (raw).originalAtlas i.val *
          (integralC * amplitude ^ degree *
            Z ^ (((if centered then b.paddingMax else 0) + 3 * b.step + b.ε / 2) +
              CanonicalPrimitiveExceptionalChoices.firstTiltError b + movingAt i) * localWeight i) := hi
      _ ≤ (parents).originalScalarAt (raw).originalAtlas i.val *
          (integralC * amplitude ^ degree * Z ^ (paidLoss + movingAt i) * localWeight i) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (hZ).le (add_le_add_right hbase _))
              (mul_nonneg hc0 (pow_nonneg hp0 _))) hweight)
          ((parents).originalScalarAt_nonneg (raw).originalAtlas i.val)
      _ = (integralC * amplitude ^ degree * Z ^ paidLoss) *
          ((parents).originalScalarAt (raw).originalAtlas i.val * Z ^ movingAt i * localWeight i) := by
        rw [Real.rpow_add hz]
        ring
      _ ≤ (integralC * amplitude ^ degree * Z ^ paidLoss) *
          (CanonicalPrimitiveExceptionalChoices.fiberCap b * amplifiedWeight i) :=
        mul_le_mul_of_nonneg_left (hscalar i)
          (mul_nonneg (mul_nonneg hc0 (pow_nonneg hp0 _)) (Real.rpow_nonneg hz.le _))
      _ = _ := by unfold CanonicalPrimitiveExceptionalChoices.leafCoefficient; ring
  let rows := actualRows
  have hbox : b.columnBound ≤ CanonicalPrimitiveExceptionalChoices.indexBox b := by
    exact le_add_of_nonneg_right
      (mul_nonneg (by norm_num) (div_nonneg b.step_pos.le (by norm_num)))
  let broadRows := rows.enlargeBound (hZ).le hbox
  have hmask : OriginalMaskPrimeData (source).mask (1 : Ideal (𝓞 K)) :=
    emptyOriginalSIntegerMask
  have hmaskNorm : (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℝ) ≤
      Z ^ CanonicalPrimitiveExceptionalChoices.indexBox b := by
    simpa only [map_one, Nat.cast_one] using
      Real.one_le_rpow (hZ).le (CanonicalPrimitiveExceptionalChoices.indexBox_nonneg b)
  have hwindow (i : liveKeys) :
      (Ideal.absNorm ((parents).innerDivisor (raw).originalAtlas i.val) : ℝ) ≤
        Z ^ (lower i + 0) := by
    rw [add_zero, rpow_idealLogLength Z hZ _ (hdivisor i)]
  have hsum := CanonicalPrimitiveExceptionalChoices.pooled_bound μv ν C hDiff b primitive
    Z (CanonicalPrimitiveExceptionalChoices.threshold_windows
      μv ν C hDiff b primitive Z hexceptionalLarge).2.2 bad pool
    b.rowBound b.columnBound amplitude b.rowBound_nonneg le_rfl le_rfl hamplitude paidLoss
    centered (data ξ) internal t canonicalLeft canonicalRight
    (b.firstBox.cutoff Z) (b.firstBox.cutoff_ge_one (hZ).le)
    source stages (raw).originalAtlas hcap exceptional normalization b.columnBound le_rfl broadRows
    (1 : Ideal (𝓞 K)) squarefree_one one_ne_zero (fun _ _ => one_dvd _)
    (1 : Ideal (𝓞 K)) one_ne_zero hmask hmaskNorm hN lower 0 hwindow hleaf
  have hsum' : cost ≤
      CanonicalPrimitiveExceptionalChoices.pooledConstant μv ν C hDiff b primitive *
        amplitude ^ degree *
        Z ^ (paidLoss + CanonicalPrimitiveExceptionalChoices.indexLoss b +
          CanonicalPrimitiveExceptionalChoices.indexLoss b +
          CanonicalPrimitiveExceptionalChoices.indexLoss b + b.loss) := by
    simpa only [Q.fullSupportParameters_width, add_zero, map_one, Nat.cast_one, div_one] using hsum
  have hcontrol : amplitude ^ degree ≤ control ^ degree :=
    pow_le_pow_left₀ hp0 (CanonicalPrimitiveEngineControl.amplitude_le amplitude t hamplitude) _
  have hcoefficient :
      CanonicalPrimitiveExceptionalChoices.pooledConstant μv ν C hDiff b primitive ≤
        CanonicalPrimitiveExceptionalChoices.constant μv ν C hDiff b primitive := by
    have hd := CanonicalPrimitiveExceptionalChoices.directConstant_pos μv ν C hDiff b primitive
    unfold CanonicalPrimitiveExceptionalChoices.constant
    linarith
  calc
    cost ≤ CanonicalPrimitiveExceptionalChoices.pooledConstant μv ν C hDiff b primitive *
        amplitude ^ degree * Z ^ (paidLoss + CanonicalPrimitiveExceptionalChoices.indexLoss b +
          CanonicalPrimitiveExceptionalChoices.indexLoss b +
          CanonicalPrimitiveExceptionalChoices.indexLoss b + b.loss) := hsum'
    _ ≤ CanonicalPrimitiveExceptionalChoices.pooledConstant μv ν C hDiff b primitive *
        control ^ degree * Z ^ (paidLoss + CanonicalPrimitiveExceptionalChoices.indexLoss b +
          CanonicalPrimitiveExceptionalChoices.indexLoss b +
          CanonicalPrimitiveExceptionalChoices.indexLoss b + b.loss) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcontrol
          (CanonicalPrimitiveExceptionalChoices.pooledConstant_pos μv ν C hDiff b primitive).le)
        (Real.rpow_nonneg hz.le _)
    _ ≤ _ := CanonicalPrimitiveEngineControl.monomial_mono
      (CanonicalPrimitiveExceptionalChoices.constant_pos μv ν C hDiff b primitive).le
      hcoefficient (CanonicalPrimitiveEngineControl.one_le amplitude t hamplitude)
      (hZ).le le_rfl (CanonicalPrimitiveExceptionalChoices.terminal_exponent_le b b.paddingMax le_rfl)

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledEngineExceptionalCost_le
