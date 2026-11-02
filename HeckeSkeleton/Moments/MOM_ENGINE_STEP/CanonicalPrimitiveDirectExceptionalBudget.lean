import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveDirectEngine
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveExceptionalChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineSetup
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectExceptionalIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalExactIndex

set_option linter.unusedSectionVars false

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
  sorry

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
  sorry

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectEngineExceptionalCost_le
