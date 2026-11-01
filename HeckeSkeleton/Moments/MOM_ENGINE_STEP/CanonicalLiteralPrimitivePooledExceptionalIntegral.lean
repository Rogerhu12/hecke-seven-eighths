import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledExceptionalSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveExceptionalFirstProfile
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPooledExceptionalKernels
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalOriginalIntegral

/-!
# Integrate the original pooled exceptional leaves

Every main and valuation case uses its actual gated parent, two original
first scalars, actual allocation divisor and the two fixed Fourier kernels.
The first profile bound and exceptional source estimate are produced here
from the original data. The original scalar and nominal moving length stay
explicit for the original amplified index sum.
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

local notation "total" => Q.literalPrimitiveFirstTotal μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
local notation "parents" => (stages).supported.gated
local notation "liveKeys" => (parents).liveLeaves (raw).originalAtlas exceptional normalization
local notation "labels" => (parents).arithmeticLabels (raw).originalAtlas hcap exceptional normalization
local notation "movingAt" => fun (key : (parents).CoveredLeafKey (raw).originalAtlas) =>
  ((parents).originalNominalTagAt (raw).originalAtlas key).movingLength Z +
    ((parents).originalNominalTagAt (raw).originalAtlas key).poolLength step
local notation "firstKernel" => ActualGaussStage.canonicalRowBallKernel
  (A := A) (Γ := Γ₀) μv ν δ₁ hδ₁ hδ₁half
local notation "secondKernel" => ActualGaussStage.canonicalRowBallKernel
  (A := A) (Γ := Γ₀) μv ν δ₂ hδ₂ hδ₂half
local notation "firstConstant" =>
  CanonicalLiteralPrimitiveExceptionalFirstProfile.firstConstant K cap hi
local notation "secondConstant" => hi ^ cap * orbitalFieldFactor K *
  ((Γ₀).index : ℝ) * fixedCoefficient
local notation "fourierCost" => CanonicalExceptionalPaidIntegral.fourierFactor
  heightOrder heightOrder firstKernel secondKernel
local notation "integralConstant" => ((data ξ).theta.card : ℝ) ^ 2 *
  firstConstant * secondConstant * (1 + 2 * Real.pi) ^ heightOrder * fourierCost
local notation "remaining" => (if centered then padding else 0) + 3 * step + finalLoss / 2
local notation "tilt" => 4 * max lengthBound columnBound * (δ₁ + δ₂)

include originalWindow hrows htime hprime href hamplitude hlo hhi hcap hY₁ hY₂ hlower hδsum
  hslotLossNonneg hfinalLoss hslotLoss hslots hone hplaces hsupport hcutoffPower₂
  hwidth hthreshold hvolume hfirstBox hN hlengthBound htotal in
/-- This is the original indexed pooled parent cost. Its two source bounds,
finite theta sum, integrability and Fourier moments are all produced
inside the proof. The original allocation divisor and moving length remain
explicit in the same arithmetic index. -/
theorem literalPrimitivePooledExceptional_integral
    (hpadding : centered = true → 0 ≤ padding) (i : liveKeys) :
    ((parents).parentLeaf (raw).originalAtlas exceptional normalization i.val).exceptionalCost /
        Z ^ (a.m + a.q) ≤
      (parents).originalScalarAt (raw).originalAtlas i.val *
        (integralConstant * originalBound ^ (14 * cap + 10) * Z ^ (remaining + tilt + movingAt i.val) *
          (labels).carrier.exceptionalDyadWeight Z
            (idealLogLength Z ((parents).innerDivisor (raw).originalAtlas i.val)) ((labels).index i)) := by
  have hP : 0 ≤ originalBound := zero_le_one.trans hamplitude
  have hfirstConstant : 0 ≤ firstConstant :=
    CanonicalLiteralPrimitiveExceptionalFirstProfile.firstConstant_nonneg
      K cap (zero_le_one.trans hhi)
  have hsecondConstant : 0 ≤ secondConstant := by
    have hc := (CanonicalLiteralExceptionalSourceBudget.coefficient_pos
      (A := A) (σ := σ) (η := η) (hS := hS) primitive ε widthMax loss cutoffExponent
      hε hwidthMax hloss hcutoffExponent δ₁ δ₂ hi cap hhi).le
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hhi) _)
        (orbitalFieldFactor_nonneg K)) (Nat.cast_nonneg _)) hc
  have hfirstCost : 0 ≤ firstConstant * originalBound ^ (2 * cap) :=
    mul_nonneg hfirstConstant (pow_nonneg hP _)
  have hsecondCost : 0 ≤ secondConstant * originalBound ^ degree :=
    mul_nonneg hsecondConstant (pow_nonneg hP _)
  have hzero : (0, 0) ∈ CanonicalLogProfiles.sourceOrders
      (CanonicalLogProfiles.sourceOrders orders) :=
    CanonicalLogProfiles.subset_sourceOrders _ (CanonicalLogProfiles.subset_sourceOrders _
      (CanonicalLiteralExceptionalUnifiedChoice.orders_zero
        (A := A) (σ := σ) (η := η) (hS := hS)
        primitive ε maskExponent hε hmaskExponent))
  have hsource : ∃
      (X : ((parents).parentLeaf (raw).originalAtlas exceptional normalization i.val).ConstantAtomExtraction)
      (aa bb : ℂ) (haa : aa ≠ 0) (hbb : bb ≠ 0)
      (characters : PairedFiniteCharacters (data ξ).theta
        (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ₀)),
      ((parents).parentLeaf (raw).originalAtlas exceptional normalization i.val).exceptional =
          characters.exceptional ∧
      ((source).pools i.val.1 i.val.2.1).weightBound * (‖aa‖ * ‖bb‖) ≤
        (firstConstant * originalBound ^ (2 * cap)) *
          Z ^ ((a.m + a.q) - total i.val.1 i.val.2.1 + tilt) ∧
      ∀ thetaPair : (data ξ).theta × (data ξ).theta, ∀ z : ℝ × ℝ,
        ((X.stripOuter aa bb haa hbb).thetaClassLeaf characters thetaPair).exceptionalIntegrand z /
            (parents).firstAllowanceAt (raw).originalAtlas total i.val ≤
          ((secondConstant * originalBound ^ degree) *
            (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ heightOrder) *
              Z ^ (remaining + movingAt i.val) /
            (Ideal.absNorm (commonRadical ((parents).commonLabel (raw).originalAtlas i.val).1
              ((parents).commonLabel (raw).originalAtlas i.val).2) : ℝ) *
                Z ^ (-idealLogLength Z ((parents).innerDivisor (raw).originalAtlas i.val)) := by
    have hparent := (parents).liveLeaves_spec (raw).originalAtlas exceptional normalization i
    have hS := (parents).live_first_divisor_squarefree (raw).originalAtlas exceptional normalization i
    rcases i with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩
    · have hblock := ((parents DE D).coveredLeaf (raw).originalAtlas (raw).originalAtlas
        ((normalization).left DE D) ((normalization).right DE D)
        ((normalization).left_pos DE D) ((normalization).right_pos DE D)
        (exceptional DE D) ⟨S, χ, .inl leaf⟩).live_of_scale_live _ _ hparent
      have hpool := (((stages DE D).left S χ).supported.gated.coveredLeaf
        (((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ)
        ((exceptional DE D).left S χ) ((source).charts DE D).kernel
        ((source).charts DE D).leftPoint leaf).live_of_scale_live _ _ hblock
      rcases leaf with leaf | (⟨prime, leaf⟩ | (⟨prime, leaf⟩ | ⟨prime, leaf⟩))
      · have hfiberOriginal := ((((stages DE D).left S χ).main).supported.gated.fiberCoveredLeaf
          ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).main)
          ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).main)
          (((exceptional DE D).left S χ).main)
          ((source).charts DE D).kernel ((source).charts DE D).leftPoint leaf).live_of_scale_live _ _ hpool
        let first := OriginalNominalGeometry.canonicalMain
          (a := internal) (Z := Z) (step := step) (((source).block DE).literalLeftCoordinates D.val)
          supportError (zero_lt_one.trans hZ) hsupportError
        let rowWindow := (((source).pools DE D).divisorPools.leftData S).literalMainRows
          internal (((source).block DE).literalLeftCoordinates D.val) supportError hsupportError
          hstep (leftRows DE D S)
        let stage := ((stages DE D).left S χ).main
        let cover := (((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).main
        let point := ((source).charts DE D).leftPoint
        let movingCost := step / 3
        let firstFixed := ((source).block DE).literalLeftFixed D.val
        let hfirst := ((source).block DE).literalLeftFixed_generates C D.val
        let phases := CanonicalLiteralActualCharacters.unamplifiedPhases
          firstFixed (CanonicalLiteralFirstPhase.leftElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst
        let predicate := stage.supported.gated.literalHybridPredicates
          cover cover P R phases Q.moving Q.correction (data ξ).theta
        have hfiber : (stage.supported.gated.fiberCoveredLeaf cover cover predicate
            ((source).charts DE D).kernel point leaf).Live := hfiberOriginal
        let v := leaf.1
        let j := leaf.2
        let bareLive := (v.leaf predicate ((source).charts DE D).kernel point j).live_of_scale_live _ _ hfiber
        let construction := literalLeftMainExceptionalExtraction
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
            (retainedScale := first.retainedScale) (g := first.enlargement) (hscale := first.retainedScale_pos)
            (domain := domainInternal) (v := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
            (firstFixed := firstFixed) (hfirst := hfirst) (j := j) (hS := hS)
            (hlive := bareLive)
        let oldLeftAtoms := literalLeftMainAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ v.2.2.1
        let oldRightAtoms := literalLeftMainAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ v.2.2.2.1
        let leftScalar := literalLeftMainScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ v.2.2.1 * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rightScalar := literalLeftMainScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ v.2.2.2.1 * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rawRows := v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel
        let characters := rawRows.literalFiniteCharacters C P R phases Q.moving Q.correction
          (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
          (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) (data ξ).theta
        let outer := construction.val.stripOuter leftScalar rightScalar
          construction.property.2.1 construction.property.2.2
        let key : (parents).CoveredLeafKey (raw).originalAtlas := ⟨DE, D, S, χ, .inl (.inl leaf)⟩
        let X : ((parents).parentLeaf (raw).originalAtlas exceptional normalization key).ConstantAtomExtraction := {
          leftScalar := construction.val.leftScalar
          rightScalar := construction.val.rightScalar
          leftResidual := construction.val.leftResidual
          rightResidual := construction.val.rightResidual
          left := construction.val.left
          right := construction.val.right }
        refine ⟨X, leftScalar, rightScalar, construction.property.2.1,
          construction.property.2.2, characters, rfl, ?_, ?_⟩
        · exact literalPrimitiveLeftMainExceptional_firstProfile_le
            (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
            (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
            (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
            (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
            (domain := domain) (lengthBound := lengthBound) (columnBound := columnBound)
            (hlengthBound := hlengthBound) (htotal := htotal) (hN := hN)
            (δ₂ := δ₂) (hδ₂ := hδ₂.le) (cap := cap) (annulus := hi) (amplitude := originalBound)
            (hannulus := hhi) (hamplitude := hamplitude) (hY₁ := hY₁) (hY₂ := hY₂)
            (profiles := originalWindow) (hzero := hzero) (ht := htime) (hprime := hprime)
            (hwindow := fun _ h => h.2) (hcap := hcap) (hδsum := hδsum)
            (hcolumnBound := hcolumnBound) (loss := loss) (cutoffExponent := cutoffExponent)
            (hloss := hloss) (hcutoffExponent := hcutoffExponent) (hannulusZ := hannulusZ)
            (hrows := hrows) (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
            (pool := pool) (hdensity := hdensity)
            DE D S χ v.2.2.1 v.2.2.2.1
        · intro thetaPair z
          have hnorm : firstLeftAllowance Z
              (first.skeleton.A + (first.skeleton.q + first.skeleton.R + first.skeleton.E))
              first.ideals.first.val first.ideals.opposite.val =
            (parents).firstAllowanceAt (raw).originalAtlas total key := by
            change firstLeftAllowance Z
              (((internal).n₁ + (internal).n₂ + (internal).z) +
                ((internal).q + idealLogLength Z (firstActiveRadical
                  (((source).block DE).literalLeftCoordinates D.val).first.val
                  (((source).block DE).literalLeftCoordinates D.val).opposite.val) +
                  idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val))
              (((source).block DE).literalLeftCoordinates D.val).first.val
              (((source).block DE).literalLeftCoordinates D.val).opposite.val =
                firstLeftAllowance Z (total DE D) DE.val.1 DE.val.2
            rw [((source).block DE).literalLeftCoordinates_first,
              ((source).block DE).literalLeftCoordinates_opposite]
            congr 1
            unfold literalPrimitiveFirstTotal
            ring
          have hradical :
              (Ideal.absNorm (commonRadical
                (primePowerProduct v.block.primes v.block.leftMultiplicity).val
                (primePowerProduct v.block.primes v.block.rightMultiplicity).val) : ℝ) =
              (Ideal.absNorm (commonRadical ((parents).commonLabel (raw).originalAtlas key).1
                ((parents).commonLabel (raw).originalAtlas key).2) : ℝ) :=
            congrArg₂ (fun I J : Ideal (𝓞 K) => (Ideal.absNorm (commonRadical I J) : ℝ))
              v.block.common_left v.block.common_right
          have hmoving : movingAt key = movingCost := by
            change (0 : ℝ) + step / 3 = step / 3
            exact zero_add _
          have houter :
              ((X.stripOuter leftScalar rightScalar construction.property.2.1
                construction.property.2.2).thetaClassLeaf characters thetaPair).exceptionalIntegrand z =
              (outer.thetaClassLeaf characters thetaPair).exceptionalIntegrand z := by
            rfl
          by_cases hc : centered = true
          · have hp := literalPrimitiveLeftMainExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (hfirstBox := hfirstBox)
              (hwidth := hwidth) (hthreshold := hthreshold) (hvolume := hvolume)
              hc (hpadding hc) thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_pos hc, hmoving] using hp
          · have hc' : centered = false := Bool.eq_false_of_not_eq_true hc
            have hp := literalPrimitiveLeftMainOrdinaryExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              hc' thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_neg hc, zero_add, hmoving] using hp
      · have hfiberOriginal := ((((stages DE D).left S χ).one prime).supported.gated.fiberCoveredLeaf
          ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual prime 1)
          ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual prime 1)
          (((exceptional DE D).left S χ).one prime)
          ((source).charts DE D).kernel (fun i => ((source).charts DE D).leftPoint i.val) leaf).live_of_scale_live _ _ hpool
        let first := OriginalNominalGeometry.canonicalPoolError
          (a := internal) pool (AmplifierValuation.one) prime (((source).block DE).literalLeftCoordinates D.val)
          supportError hsupportError
        let rowWindow := (((source).pools DE D).divisorPools.leftData S).literalPoolRows
          internal (((source).block DE).literalLeftCoordinates D.val) supportError hsupportError
          hstep (leftRows DE D S) (AmplifierValuation.one) prime
        let stage := (((source).pools DE D).divisorPools.leftData S).literalValuationStage
          (hΓ := hΓ₀) (μv := μv) (hDiff := hDiff) (ν := ν)
          (((source).pools DE D).leftDivisorCoefficient S χ) P internal
          (((source).block DE).literalLeftCoordinates D.val) supportError hsupportError
          hstep (leftRows DE D S) δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ (AmplifierValuation.one) prime
        let cover := (((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual prime (AmplifierValuation.one).multiplicity
        let point : (((source).pools DE D).divisorPools.leftData S).valuationColumns prime.val (AmplifierValuation.one).multiplicity → ℝ := (fun i => ((source).charts DE D).leftPoint i.val)
        let movingCost := (amplifierMovingExponent (AmplifierValuation.one).multiplicity : ℝ) *
          idealLogLength Z prime.val.val.asIdeal
        let firstFixed := ((source).block DE).literalLeftFixed D.val
        let hfirst := ((source).block DE).literalLeftFixed_generates C D.val
        let phases := CanonicalLiteralActualCharacters.amplifiedPhases C
          firstFixed (CanonicalLiteralFirstPhase.leftElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst prime.val (AmplifierValuation.one).multiplicity
        let predicate := stage.supported.gated.literalHybridPredicates
          cover cover P R phases Q.moving Q.correction (data ξ).theta
        have hfiber : (stage.supported.gated.fiberCoveredLeaf cover cover predicate
            ((source).charts DE D).kernel point leaf).Live := hfiberOriginal
        let v := leaf.1
        let j := leaf.2
        let bareLive := (v.leaf predicate ((source).charts DE D).kernel point j).live_of_scale_live _ _ hfiber
        let construction := literalLeftPoolExceptionalExtraction
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
            (retainedScale := first.retainedScale) (g := first.enlargement) (hscale := first.retainedScale_pos)
            (domain := domainInternal) (v := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
            (firstFixed := firstFixed) (hfirst := hfirst) (j := j) (hS := hS)
            (q := prime) (n := (AmplifierValuation.one).multiplicity) (hlive := hfiber)
        let oldLeftAtoms := literalLeftPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ prime (AmplifierValuation.one).multiplicity v.2.2.1
        let oldRightAtoms := literalLeftPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ prime (AmplifierValuation.one).multiplicity v.2.2.2.1
        let leftScalar := literalLeftPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ prime (AmplifierValuation.one).multiplicity v.2.2.1 * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rightScalar := literalLeftPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ prime (AmplifierValuation.one).multiplicity v.2.2.2.1 * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rawRows := v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel
        let characters := rawRows.literalFiniteCharacters C P R phases Q.moving Q.correction
          (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
          (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) (data ξ).theta
        let outer := construction.val.stripOuter leftScalar rightScalar
          construction.property.2.1 construction.property.2.2
        let key : (parents).CoveredLeafKey (raw).originalAtlas := ⟨DE, D, S, χ, .inl (.inr (.inl ⟨prime, leaf⟩))⟩
        let X : ((parents).parentLeaf (raw).originalAtlas exceptional normalization key).ConstantAtomExtraction := {
          leftScalar := construction.val.leftScalar
          rightScalar := construction.val.rightScalar
          leftResidual := construction.val.leftResidual
          rightResidual := construction.val.rightResidual
          left := construction.val.left
          right := construction.val.right }
        refine ⟨X, leftScalar, rightScalar, construction.property.2.1,
          construction.property.2.2, characters, rfl, ?_, ?_⟩
        · exact literalPrimitiveLeftPoolExceptional_firstProfile_le
            (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
            (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
            (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
            (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
            (domain := domain) (lengthBound := lengthBound) (columnBound := columnBound)
            (hlengthBound := hlengthBound) (htotal := htotal) (hN := hN)
            (δ₂ := δ₂) (hδ₂ := hδ₂.le) (cap := cap) (annulus := hi) (amplitude := originalBound)
            (hannulus := hhi) (hamplitude := hamplitude) (hY₁ := hY₁) (hY₂ := hY₂)
            (profiles := originalWindow) (hzero := hzero) (ht := htime) (hprime := hprime)
            (hwindow := fun _ h => h.2) (hcap := hcap) (hδsum := hδsum)
            (hcolumnBound := hcolumnBound) (loss := loss) (cutoffExponent := cutoffExponent)
            (hloss := hloss) (hcutoffExponent := hcutoffExponent) (hannulusZ := hannulusZ)
            (hrows := hrows) (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
            (pool := pool) (hdensity := hdensity)
            DE D S χ prime (AmplifierValuation.one).multiplicity v.2.2.1 v.2.2.2.1
        · intro thetaPair z
          have hnorm : firstLeftAllowance Z
              (first.skeleton.A + (first.skeleton.q + first.skeleton.R + first.skeleton.E))
              first.ideals.first.val first.ideals.opposite.val =
            (parents).firstAllowanceAt (raw).originalAtlas total key := by
            change firstLeftAllowance Z
              (((internal).n₁ + (internal).n₂ + (internal).z) +
                ((internal).q + idealLogLength Z (firstActiveRadical
                  (((source).block DE).literalLeftCoordinates D.val).first.val
                  (((source).block DE).literalLeftCoordinates D.val).opposite.val) +
                  idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val))
              (((source).block DE).literalLeftCoordinates D.val).first.val
              (((source).block DE).literalLeftCoordinates D.val).opposite.val =
                firstLeftAllowance Z (total DE D) DE.val.1 DE.val.2
            rw [((source).block DE).literalLeftCoordinates_first,
              ((source).block DE).literalLeftCoordinates_opposite]
            congr 1
            unfold literalPrimitiveFirstTotal
            ring
          have hradical :
              (Ideal.absNorm (commonRadical
                (primePowerProduct v.block.primes v.block.leftMultiplicity).val
                (primePowerProduct v.block.primes v.block.rightMultiplicity).val) : ℝ) =
              (Ideal.absNorm (commonRadical ((parents).commonLabel (raw).originalAtlas key).1
                ((parents).commonLabel (raw).originalAtlas key).2) : ℝ) :=
            congrArg₂ (fun I J : Ideal (𝓞 K) => (Ideal.absNorm (commonRadical I J) : ℝ))
              v.block.common_left v.block.common_right
          have hmoving : movingAt key = movingCost := by
            change ((AmplifierValuation.one).movingMultiplicity : ℝ) *
                idealLogLength Z prime.val.val.asIdeal + 0 = _
            have he : (AmplifierValuation.one).movingMultiplicity =
                amplifierMovingExponent (AmplifierValuation.one).multiplicity := rfl
            rw [he, add_zero]
          have houter :
              ((X.stripOuter leftScalar rightScalar construction.property.2.1
                construction.property.2.2).thetaClassLeaf characters thetaPair).exceptionalIntegrand z =
              (outer.thetaClassLeaf characters thetaPair).exceptionalIntegrand z := by
            rfl
          by_cases hc : centered = true
          · have hp := literalPrimitiveLeftPoolExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (hfirstBox := hfirstBox)
              (hwidth := hwidth) (hthreshold := hthreshold) (hvolume := hvolume)
              (valuation := AmplifierValuation.one) (prime := prime)
              hc (hpadding hc) thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_pos hc, hmoving] using hp
          · have hc' : centered = false := Bool.eq_false_of_not_eq_true hc
            have hp := literalPrimitiveLeftPoolOrdinaryExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (valuation := AmplifierValuation.one) (prime := prime)
              hc' thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_neg hc, zero_add, hmoving] using hp
      · have hfiberOriginal := ((((stages DE D).left S χ).six prime).supported.gated.fiberCoveredLeaf
          ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual prime 6)
          ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual prime 6)
          (((exceptional DE D).left S χ).six prime)
          ((source).charts DE D).kernel (fun i => ((source).charts DE D).leftPoint i.val) leaf).live_of_scale_live _ _ hpool
        let first := OriginalNominalGeometry.canonicalPoolError
          (a := internal) pool (AmplifierValuation.six) prime (((source).block DE).literalLeftCoordinates D.val)
          supportError hsupportError
        let rowWindow := (((source).pools DE D).divisorPools.leftData S).literalPoolRows
          internal (((source).block DE).literalLeftCoordinates D.val) supportError hsupportError
          hstep (leftRows DE D S) (AmplifierValuation.six) prime
        let stage := (((source).pools DE D).divisorPools.leftData S).literalValuationStage
          (hΓ := hΓ₀) (μv := μv) (hDiff := hDiff) (ν := ν)
          (((source).pools DE D).leftDivisorCoefficient S χ) P internal
          (((source).block DE).literalLeftCoordinates D.val) supportError hsupportError
          hstep (leftRows DE D S) δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ (AmplifierValuation.six) prime
        let cover := (((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual prime (AmplifierValuation.six).multiplicity
        let point : (((source).pools DE D).divisorPools.leftData S).valuationColumns prime.val (AmplifierValuation.six).multiplicity → ℝ := (fun i => ((source).charts DE D).leftPoint i.val)
        let movingCost := (amplifierMovingExponent (AmplifierValuation.six).multiplicity : ℝ) *
          idealLogLength Z prime.val.val.asIdeal
        let firstFixed := ((source).block DE).literalLeftFixed D.val
        let hfirst := ((source).block DE).literalLeftFixed_generates C D.val
        let phases := CanonicalLiteralActualCharacters.amplifiedPhases C
          firstFixed (CanonicalLiteralFirstPhase.leftElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst prime.val (AmplifierValuation.six).multiplicity
        let predicate := stage.supported.gated.literalHybridPredicates
          cover cover P R phases Q.moving Q.correction (data ξ).theta
        have hfiber : (stage.supported.gated.fiberCoveredLeaf cover cover predicate
            ((source).charts DE D).kernel point leaf).Live := hfiberOriginal
        let v := leaf.1
        let j := leaf.2
        let bareLive := (v.leaf predicate ((source).charts DE D).kernel point j).live_of_scale_live _ _ hfiber
        let construction := literalLeftPoolExceptionalExtraction
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
            (retainedScale := first.retainedScale) (g := first.enlargement) (hscale := first.retainedScale_pos)
            (domain := domainInternal) (v := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
            (firstFixed := firstFixed) (hfirst := hfirst) (j := j) (hS := hS)
            (q := prime) (n := (AmplifierValuation.six).multiplicity) (hlive := hfiber)
        let oldLeftAtoms := literalLeftPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ prime (AmplifierValuation.six).multiplicity v.2.2.1
        let oldRightAtoms := literalLeftPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ prime (AmplifierValuation.six).multiplicity v.2.2.2.1
        let leftScalar := literalLeftPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ prime (AmplifierValuation.six).multiplicity v.2.2.1 * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rightScalar := literalLeftPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ prime (AmplifierValuation.six).multiplicity v.2.2.2.1 * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rawRows := v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel
        let characters := rawRows.literalFiniteCharacters C P R phases Q.moving Q.correction
          (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
          (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) (data ξ).theta
        let outer := construction.val.stripOuter leftScalar rightScalar
          construction.property.2.1 construction.property.2.2
        let key : (parents).CoveredLeafKey (raw).originalAtlas := ⟨DE, D, S, χ, .inl (.inr (.inr (.inl ⟨prime, leaf⟩)))⟩
        let X : ((parents).parentLeaf (raw).originalAtlas exceptional normalization key).ConstantAtomExtraction := {
          leftScalar := construction.val.leftScalar
          rightScalar := construction.val.rightScalar
          leftResidual := construction.val.leftResidual
          rightResidual := construction.val.rightResidual
          left := construction.val.left
          right := construction.val.right }
        refine ⟨X, leftScalar, rightScalar, construction.property.2.1,
          construction.property.2.2, characters, rfl, ?_, ?_⟩
        · exact literalPrimitiveLeftPoolExceptional_firstProfile_le
            (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
            (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
            (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
            (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
            (domain := domain) (lengthBound := lengthBound) (columnBound := columnBound)
            (hlengthBound := hlengthBound) (htotal := htotal) (hN := hN)
            (δ₂ := δ₂) (hδ₂ := hδ₂.le) (cap := cap) (annulus := hi) (amplitude := originalBound)
            (hannulus := hhi) (hamplitude := hamplitude) (hY₁ := hY₁) (hY₂ := hY₂)
            (profiles := originalWindow) (hzero := hzero) (ht := htime) (hprime := hprime)
            (hwindow := fun _ h => h.2) (hcap := hcap) (hδsum := hδsum)
            (hcolumnBound := hcolumnBound) (loss := loss) (cutoffExponent := cutoffExponent)
            (hloss := hloss) (hcutoffExponent := hcutoffExponent) (hannulusZ := hannulusZ)
            (hrows := hrows) (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
            (pool := pool) (hdensity := hdensity)
            DE D S χ prime (AmplifierValuation.six).multiplicity v.2.2.1 v.2.2.2.1
        · intro thetaPair z
          have hnorm : firstLeftAllowance Z
              (first.skeleton.A + (first.skeleton.q + first.skeleton.R + first.skeleton.E))
              first.ideals.first.val first.ideals.opposite.val =
            (parents).firstAllowanceAt (raw).originalAtlas total key := by
            change firstLeftAllowance Z
              (((internal).n₁ + (internal).n₂ + (internal).z) +
                ((internal).q + idealLogLength Z (firstActiveRadical
                  (((source).block DE).literalLeftCoordinates D.val).first.val
                  (((source).block DE).literalLeftCoordinates D.val).opposite.val) +
                  idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val))
              (((source).block DE).literalLeftCoordinates D.val).first.val
              (((source).block DE).literalLeftCoordinates D.val).opposite.val =
                firstLeftAllowance Z (total DE D) DE.val.1 DE.val.2
            rw [((source).block DE).literalLeftCoordinates_first,
              ((source).block DE).literalLeftCoordinates_opposite]
            congr 1
            unfold literalPrimitiveFirstTotal
            ring
          have hradical :
              (Ideal.absNorm (commonRadical
                (primePowerProduct v.block.primes v.block.leftMultiplicity).val
                (primePowerProduct v.block.primes v.block.rightMultiplicity).val) : ℝ) =
              (Ideal.absNorm (commonRadical ((parents).commonLabel (raw).originalAtlas key).1
                ((parents).commonLabel (raw).originalAtlas key).2) : ℝ) :=
            congrArg₂ (fun I J : Ideal (𝓞 K) => (Ideal.absNorm (commonRadical I J) : ℝ))
              v.block.common_left v.block.common_right
          have hmoving : movingAt key = movingCost := by
            change ((AmplifierValuation.six).movingMultiplicity : ℝ) *
                idealLogLength Z prime.val.val.asIdeal + 0 = _
            have he : (AmplifierValuation.six).movingMultiplicity =
                amplifierMovingExponent (AmplifierValuation.six).multiplicity := rfl
            rw [he, add_zero]
          have houter :
              ((X.stripOuter leftScalar rightScalar construction.property.2.1
                construction.property.2.2).thetaClassLeaf characters thetaPair).exceptionalIntegrand z =
              (outer.thetaClassLeaf characters thetaPair).exceptionalIntegrand z := by
            rfl
          by_cases hc : centered = true
          · have hp := literalPrimitiveLeftPoolExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (hfirstBox := hfirstBox)
              (hwidth := hwidth) (hthreshold := hthreshold) (hvolume := hvolume)
              (valuation := AmplifierValuation.six) (prime := prime)
              hc (hpadding hc) thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_pos hc, hmoving] using hp
          · have hc' : centered = false := Bool.eq_false_of_not_eq_true hc
            have hp := literalPrimitiveLeftPoolOrdinaryExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (valuation := AmplifierValuation.six) (prime := prime)
              hc' thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_neg hc, zero_add, hmoving] using hp
      · have hfiberOriginal := ((((stages DE D).left S χ).seven prime).supported.gated.fiberCoveredLeaf
          ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual prime 7)
          ((((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual prime 7)
          (((exceptional DE D).left S χ).seven prime)
          ((source).charts DE D).kernel (fun i => ((source).charts DE D).leftPoint i.val) leaf).live_of_scale_live _ _ hpool
        let first := OriginalNominalGeometry.canonicalPoolError
          (a := internal) pool (AmplifierValuation.seven) prime (((source).block DE).literalLeftCoordinates D.val)
          supportError hsupportError
        let rowWindow := (((source).pools DE D).divisorPools.leftData S).literalPoolRows
          internal (((source).block DE).literalLeftCoordinates D.val) supportError hsupportError
          hstep (leftRows DE D S) (AmplifierValuation.seven) prime
        let stage := (((source).pools DE D).divisorPools.leftData S).literalValuationStage
          (hΓ := hΓ₀) (μv := μv) (hDiff := hDiff) (ν := ν)
          (((source).pools DE D).leftDivisorCoefficient S χ) P internal
          (((source).block DE).literalLeftCoordinates D.val) supportError hsupportError
          hstep (leftRows DE D S) δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ (AmplifierValuation.seven) prime
        let cover := (((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ).residual prime (AmplifierValuation.seven).multiplicity
        let point : (((source).pools DE D).divisorPools.leftData S).valuationColumns prime.val (AmplifierValuation.seven).multiplicity → ℝ := (fun i => ((source).charts DE D).leftPoint i.val)
        let movingCost := (amplifierMovingExponent (AmplifierValuation.seven).multiplicity : ℝ) *
          idealLogLength Z prime.val.val.asIdeal
        let firstFixed := ((source).block DE).literalLeftFixed D.val
        let hfirst := ((source).block DE).literalLeftFixed_generates C D.val
        let phases := CanonicalLiteralActualCharacters.amplifiedPhases C
          firstFixed (CanonicalLiteralFirstPhase.leftElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst prime.val (AmplifierValuation.seven).multiplicity
        let predicate := stage.supported.gated.literalHybridPredicates
          cover cover P R phases Q.moving Q.correction (data ξ).theta
        have hfiber : (stage.supported.gated.fiberCoveredLeaf cover cover predicate
            ((source).charts DE D).kernel point leaf).Live := hfiberOriginal
        let v := leaf.1
        let j := leaf.2
        let bareLive := (v.leaf predicate ((source).charts DE D).kernel point j).live_of_scale_live _ _ hfiber
        let construction := literalLeftPoolExceptionalExtraction
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
            (retainedScale := first.retainedScale) (g := first.enlargement) (hscale := first.retainedScale_pos)
            (domain := domainInternal) (v := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
            (firstFixed := firstFixed) (hfirst := hfirst) (j := j) (hS := hS)
            (q := prime) (n := (AmplifierValuation.seven).multiplicity) (hlive := hfiber)
        let oldLeftAtoms := literalLeftPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ prime (AmplifierValuation.seven).multiplicity v.2.2.1
        let oldRightAtoms := literalLeftPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ prime (AmplifierValuation.seven).multiplicity v.2.2.2.1
        let leftScalar := literalLeftPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ prime (AmplifierValuation.seven).multiplicity v.2.2.1 * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rightScalar := literalLeftPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ prime (AmplifierValuation.seven).multiplicity v.2.2.2.1 * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rawRows := v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel
        let characters := rawRows.literalFiniteCharacters C P R phases Q.moving Q.correction
          (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
          (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) (data ξ).theta
        let outer := construction.val.stripOuter leftScalar rightScalar
          construction.property.2.1 construction.property.2.2
        let key : (parents).CoveredLeafKey (raw).originalAtlas := ⟨DE, D, S, χ, .inl (.inr (.inr (.inr ⟨prime, leaf⟩)))⟩
        let X : ((parents).parentLeaf (raw).originalAtlas exceptional normalization key).ConstantAtomExtraction := {
          leftScalar := construction.val.leftScalar
          rightScalar := construction.val.rightScalar
          leftResidual := construction.val.leftResidual
          rightResidual := construction.val.rightResidual
          left := construction.val.left
          right := construction.val.right }
        refine ⟨X, leftScalar, rightScalar, construction.property.2.1,
          construction.property.2.2, characters, rfl, ?_, ?_⟩
        · exact literalPrimitiveLeftPoolExceptional_firstProfile_le
            (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
            (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
            (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
            (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
            (domain := domain) (lengthBound := lengthBound) (columnBound := columnBound)
            (hlengthBound := hlengthBound) (htotal := htotal) (hN := hN)
            (δ₂ := δ₂) (hδ₂ := hδ₂.le) (cap := cap) (annulus := hi) (amplitude := originalBound)
            (hannulus := hhi) (hamplitude := hamplitude) (hY₁ := hY₁) (hY₂ := hY₂)
            (profiles := originalWindow) (hzero := hzero) (ht := htime) (hprime := hprime)
            (hwindow := fun _ h => h.2) (hcap := hcap) (hδsum := hδsum)
            (hcolumnBound := hcolumnBound) (loss := loss) (cutoffExponent := cutoffExponent)
            (hloss := hloss) (hcutoffExponent := hcutoffExponent) (hannulusZ := hannulusZ)
            (hrows := hrows) (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
            (pool := pool) (hdensity := hdensity)
            DE D S χ prime (AmplifierValuation.seven).multiplicity v.2.2.1 v.2.2.2.1
        · intro thetaPair z
          have hnorm : firstLeftAllowance Z
              (first.skeleton.A + (first.skeleton.q + first.skeleton.R + first.skeleton.E))
              first.ideals.first.val first.ideals.opposite.val =
            (parents).firstAllowanceAt (raw).originalAtlas total key := by
            change firstLeftAllowance Z
              (((internal).n₁ + (internal).n₂ + (internal).z) +
                ((internal).q + idealLogLength Z (firstActiveRadical
                  (((source).block DE).literalLeftCoordinates D.val).first.val
                  (((source).block DE).literalLeftCoordinates D.val).opposite.val) +
                  idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val))
              (((source).block DE).literalLeftCoordinates D.val).first.val
              (((source).block DE).literalLeftCoordinates D.val).opposite.val =
                firstLeftAllowance Z (total DE D) DE.val.1 DE.val.2
            rw [((source).block DE).literalLeftCoordinates_first,
              ((source).block DE).literalLeftCoordinates_opposite]
            congr 1
            unfold literalPrimitiveFirstTotal
            ring
          have hradical :
              (Ideal.absNorm (commonRadical
                (primePowerProduct v.block.primes v.block.leftMultiplicity).val
                (primePowerProduct v.block.primes v.block.rightMultiplicity).val) : ℝ) =
              (Ideal.absNorm (commonRadical ((parents).commonLabel (raw).originalAtlas key).1
                ((parents).commonLabel (raw).originalAtlas key).2) : ℝ) :=
            congrArg₂ (fun I J : Ideal (𝓞 K) => (Ideal.absNorm (commonRadical I J) : ℝ))
              v.block.common_left v.block.common_right
          have hmoving : movingAt key = movingCost := by
            change ((AmplifierValuation.seven).movingMultiplicity : ℝ) *
                idealLogLength Z prime.val.val.asIdeal + 0 = _
            have he : (AmplifierValuation.seven).movingMultiplicity =
                amplifierMovingExponent (AmplifierValuation.seven).multiplicity := rfl
            rw [he, add_zero]
          have houter :
              ((X.stripOuter leftScalar rightScalar construction.property.2.1
                construction.property.2.2).thetaClassLeaf characters thetaPair).exceptionalIntegrand z =
              (outer.thetaClassLeaf characters thetaPair).exceptionalIntegrand z := by
            rfl
          by_cases hc : centered = true
          · have hp := literalPrimitiveLeftPoolExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (hfirstBox := hfirstBox)
              (hwidth := hwidth) (hthreshold := hthreshold) (hvolume := hvolume)
              (valuation := AmplifierValuation.seven) (prime := prime)
              hc (hpadding hc) thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_pos hc, hmoving] using hp
          · have hc' : centered = false := Bool.eq_false_of_not_eq_true hc
            have hp := literalPrimitiveLeftPoolOrdinaryExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (valuation := AmplifierValuation.seven) (prime := prime)
              hc' thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_neg hc, zero_add, hmoving] using hp
    · have hblock := ((parents DE D).coveredLeaf (raw).originalAtlas (raw).originalAtlas
        ((normalization).left DE D) ((normalization).right DE D)
        ((normalization).left_pos DE D) ((normalization).right_pos DE D)
        (exceptional DE D) ⟨S, χ, .inr leaf⟩).live_of_scale_live _ _ hparent
      have hpool := (((stages DE D).right S χ).supported.gated.coveredLeaf
        (((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ)
        ((exceptional DE D).right S χ) ((source).charts DE D).kernel
        (fun i => -((source).charts DE D).rightPoint i) leaf).live_of_scale_live _ _ hblock
      rcases leaf with leaf | (⟨prime, leaf⟩ | (⟨prime, leaf⟩ | ⟨prime, leaf⟩))
      · have hfiberOriginal := ((((stages DE D).right S χ).main).supported.gated.fiberCoveredLeaf
          ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).main)
          ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).main)
          (((exceptional DE D).right S χ).main)
          ((source).charts DE D).kernel (fun i => -((source).charts DE D).rightPoint i) leaf).live_of_scale_live _ _ hpool
        let first := OriginalNominalGeometry.canonicalMain
          (a := internal) (Z := Z) (step := step) (((source).block DE).literalRightCoordinates D.val)
          supportError (zero_lt_one.trans hZ) hsupportError
        let rowWindow := (((source).pools DE D).divisorPools.rightData S).literalMainRows
          internal (((source).block DE).literalRightCoordinates D.val) supportError hsupportError
          hstep (rightRows DE D S)
        let stage := ((stages DE D).right S χ).main
        let cover := (((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).main
        let point := (fun i => Real.log (A.exteriorNorm (((source).block DE).rightResidual i)))
        let movingCost := step / 3
        let firstFixed := ((source).block DE).literalRightFixed D.val
        let hfirst := ((source).block DE).literalRightFixed_generates C D.val
        let phases := CanonicalLiteralActualCharacters.unamplifiedPhases
          firstFixed (CanonicalLiteralFirstPhase.rightElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst
        let predicate := stage.supported.gated.literalHybridPredicates
          cover cover P R phases Q.moving Q.correction (data ξ).theta
        have hpoint : (fun i => -((source).charts DE D).rightPoint i) = point := by
          funext k
          change -(-Real.log _) = _
          exact neg_neg _
        have hfiber : (stage.supported.gated.fiberCoveredLeaf cover cover predicate
            ((source).charts DE D).kernel point leaf).Live := by
          rw [hpoint] at hfiberOriginal
          exact hfiberOriginal
        let v := leaf.1
        let j := leaf.2
        let bareLive := (v.leaf predicate ((source).charts DE D).kernel point j).live_of_scale_live _ _ hfiber
        let construction := literalRightMainExceptionalExtraction
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
            (retainedScale := first.retainedScale) (g := first.enlargement) (hscale := first.retainedScale_pos)
            (domain := domainInternal) (v := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
            (firstFixed := firstFixed) (hfirst := hfirst) (j := j) (hS := hS)
            (hlive := bareLive)
        let oldLeftAtoms := literalRightMainAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ v.2.2.1
        let oldRightAtoms := literalRightMainAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ v.2.2.2.1
        let leftScalar := literalRightMainScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ v.2.2.1 * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rightScalar := literalRightMainScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ v.2.2.2.1 * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rawRows := v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel
        let characters := rawRows.literalFiniteCharacters C P R phases Q.moving Q.correction
          (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
          (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) (data ξ).theta
        let outer := construction.val.stripOuter leftScalar rightScalar
          construction.property.2.1 construction.property.2.2
        let key : (parents).CoveredLeafKey (raw).originalAtlas := ⟨DE, D, S, χ, .inr (.inl leaf)⟩
        let X : ((parents).parentLeaf (raw).originalAtlas exceptional normalization key).ConstantAtomExtraction := {
          leftScalar := construction.val.leftScalar
          rightScalar := construction.val.rightScalar
          leftResidual := construction.val.leftResidual
          rightResidual := construction.val.rightResidual
          left := construction.val.left
          right := construction.val.right }
        refine ⟨X, leftScalar, rightScalar, construction.property.2.1,
          construction.property.2.2, characters, rfl, ?_, ?_⟩
        · exact literalPrimitiveRightMainExceptional_firstProfile_le
            (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
            (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
            (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
            (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
            (domain := domain) (lengthBound := lengthBound) (columnBound := columnBound)
            (hlengthBound := hlengthBound) (htotal := htotal) (hN := hN)
            (δ₂ := δ₂) (hδ₂ := hδ₂.le) (cap := cap) (annulus := hi) (amplitude := originalBound)
            (hannulus := hhi) (hamplitude := hamplitude) (hY₁ := hY₁) (hY₂ := hY₂)
            (profiles := originalWindow) (hzero := hzero) (ht := htime) (hprime := hprime)
            (hwindow := fun _ h => h.2) (hcap := hcap) (hδsum := hδsum)
            (hcolumnBound := hcolumnBound) (loss := loss) (cutoffExponent := cutoffExponent)
            (hloss := hloss) (hcutoffExponent := hcutoffExponent) (hannulusZ := hannulusZ)
            (hrows := hrows) (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
            (pool := pool) (hdensity := hdensity)
            DE D S χ v.2.2.1 v.2.2.2.1
        · intro thetaPair z
          have hnorm : firstLeftAllowance Z
              (first.skeleton.A + (first.skeleton.q + first.skeleton.R + first.skeleton.E))
              first.ideals.first.val first.ideals.opposite.val =
            (parents).firstAllowanceAt (raw).originalAtlas total key := by
            change firstLeftAllowance Z
              (((internal).n₁ + (internal).n₂ + (internal).z) +
                ((internal).q + idealLogLength Z (firstActiveRadical
                  (((source).block DE).literalRightCoordinates D.val).first.val
                  (((source).block DE).literalRightCoordinates D.val).opposite.val) +
                  idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val))
              (((source).block DE).literalRightCoordinates D.val).first.val
              (((source).block DE).literalRightCoordinates D.val).opposite.val =
                firstRightAllowance Z (total DE D) DE.val.1 DE.val.2
            rw [((source).block DE).literalRightCoordinates_first,
              ((source).block DE).literalRightCoordinates_opposite]
            simp only [firstLeftAllowance, firstRightAllowance,
              firstActiveRadical_swap_of_support _ _ ((source).block DE).common_support_eq]
            congr 1
            unfold literalPrimitiveFirstTotal
            ring
          have hradical :
              (Ideal.absNorm (commonRadical
                (primePowerProduct v.block.primes v.block.leftMultiplicity).val
                (primePowerProduct v.block.primes v.block.rightMultiplicity).val) : ℝ) =
              (Ideal.absNorm (commonRadical ((parents).commonLabel (raw).originalAtlas key).1
                ((parents).commonLabel (raw).originalAtlas key).2) : ℝ) :=
            congrArg₂ (fun I J : Ideal (𝓞 K) => (Ideal.absNorm (commonRadical I J) : ℝ))
              v.block.common_left v.block.common_right
          have hmoving : movingAt key = movingCost := by
            change (0 : ℝ) + step / 3 = step / 3
            exact zero_add _
          have houter :
              ((X.stripOuter leftScalar rightScalar construction.property.2.1
                construction.property.2.2).thetaClassLeaf characters thetaPair).exceptionalIntegrand z =
              (outer.thetaClassLeaf characters thetaPair).exceptionalIntegrand z := by
            have hl :
                ((X.stripOuter leftScalar rightScalar construction.property.2.1
                  construction.property.2.2).thetaClassLeaf characters thetaPair).leftFirst =
                (outer.thetaClassLeaf characters thetaPair).leftFirst := by
              funext h k
              change -(-Real.log _) = _
              exact neg_neg _
            have hr :
                ((X.stripOuter leftScalar rightScalar construction.property.2.1
                  construction.property.2.2).thetaClassLeaf characters thetaPair).rightFirst =
                (outer.thetaClassLeaf characters thetaPair).rightFirst := by
              funext h k
              change -(-Real.log _) = _
              exact neg_neg _
            unfold ActualHybridLeaf.exceptionalIntegrand
            rw [hl, hr] <;> rfl
          by_cases hc : centered = true
          · have hp := literalPrimitiveRightMainExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (hfirstBox := hfirstBox)
              (hwidth := hwidth) (hthreshold := hthreshold) (hvolume := hvolume)
              hc (hpadding hc) thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_pos hc, hmoving] using hp
          · have hc' : centered = false := Bool.eq_false_of_not_eq_true hc
            have hp := literalPrimitiveRightMainOrdinaryExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              hc' thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_neg hc, zero_add, hmoving] using hp
      · have hfiberOriginal := ((((stages DE D).right S χ).one prime).supported.gated.fiberCoveredLeaf
          ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual prime 1)
          ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual prime 1)
          (((exceptional DE D).right S χ).one prime)
          ((source).charts DE D).kernel (fun i => -((source).charts DE D).rightPoint i.val) leaf).live_of_scale_live _ _ hpool
        let first := OriginalNominalGeometry.canonicalPoolError
          (a := internal) pool (AmplifierValuation.one) prime (((source).block DE).literalRightCoordinates D.val)
          supportError hsupportError
        let rowWindow := (((source).pools DE D).divisorPools.rightData S).literalPoolRows
          internal (((source).block DE).literalRightCoordinates D.val) supportError hsupportError
          hstep (rightRows DE D S) (AmplifierValuation.one) prime
        let stage := (((source).pools DE D).divisorPools.rightData S).literalValuationStage
          (hΓ := hΓ₀) (μv := μv) (hDiff := hDiff) (ν := ν)
          (((source).pools DE D).rightDivisorCoefficient S χ) P internal
          (((source).block DE).literalRightCoordinates D.val) supportError hsupportError
          hstep (rightRows DE D S) δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ (AmplifierValuation.one) prime
        let cover := (((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual prime (AmplifierValuation.one).multiplicity
        let point : (((source).pools DE D).divisorPools.rightData S).valuationColumns prime.val (AmplifierValuation.one).multiplicity → ℝ := (fun i => Real.log (A.exteriorNorm (((source).block DE).rightResidual i.val)))
        let movingCost := (amplifierMovingExponent (AmplifierValuation.one).multiplicity : ℝ) *
          idealLogLength Z prime.val.val.asIdeal
        let firstFixed := ((source).block DE).literalRightFixed D.val
        let hfirst := ((source).block DE).literalRightFixed_generates C D.val
        let phases := CanonicalLiteralActualCharacters.amplifiedPhases C
          firstFixed (CanonicalLiteralFirstPhase.rightElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst prime.val (AmplifierValuation.one).multiplicity
        let predicate := stage.supported.gated.literalHybridPredicates
          cover cover P R phases Q.moving Q.correction (data ξ).theta
        have hpoint : (fun i => -((source).charts DE D).rightPoint i.val) = point := by
          funext k
          change -(-Real.log _) = _
          exact neg_neg _
        have hfiber : (stage.supported.gated.fiberCoveredLeaf cover cover predicate
            ((source).charts DE D).kernel point leaf).Live := by
          rw [hpoint] at hfiberOriginal
          exact hfiberOriginal
        let v := leaf.1
        let j := leaf.2
        let bareLive := (v.leaf predicate ((source).charts DE D).kernel point j).live_of_scale_live _ _ hfiber
        let construction := literalRightPoolExceptionalExtraction
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
            (retainedScale := first.retainedScale) (g := first.enlargement) (hscale := first.retainedScale_pos)
            (domain := domainInternal) (v := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
            (firstFixed := firstFixed) (hfirst := hfirst) (j := j) (hS := hS)
            (q := prime) (n := (AmplifierValuation.one).multiplicity) (hlive := hfiber)
        let oldLeftAtoms := literalRightPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ prime (AmplifierValuation.one).multiplicity v.2.2.1
        let oldRightAtoms := literalRightPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ prime (AmplifierValuation.one).multiplicity v.2.2.2.1
        let leftScalar := literalRightPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ prime (AmplifierValuation.one).multiplicity v.2.2.1 * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rightScalar := literalRightPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ prime (AmplifierValuation.one).multiplicity v.2.2.2.1 * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rawRows := v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel
        let characters := rawRows.literalFiniteCharacters C P R phases Q.moving Q.correction
          (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
          (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) (data ξ).theta
        let outer := construction.val.stripOuter leftScalar rightScalar
          construction.property.2.1 construction.property.2.2
        let key : (parents).CoveredLeafKey (raw).originalAtlas := ⟨DE, D, S, χ, .inr (.inr (.inl ⟨prime, leaf⟩))⟩
        let X : ((parents).parentLeaf (raw).originalAtlas exceptional normalization key).ConstantAtomExtraction := {
          leftScalar := construction.val.leftScalar
          rightScalar := construction.val.rightScalar
          leftResidual := construction.val.leftResidual
          rightResidual := construction.val.rightResidual
          left := construction.val.left
          right := construction.val.right }
        refine ⟨X, leftScalar, rightScalar, construction.property.2.1,
          construction.property.2.2, characters, rfl, ?_, ?_⟩
        · exact literalPrimitiveRightPoolExceptional_firstProfile_le
            (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
            (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
            (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
            (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
            (domain := domain) (lengthBound := lengthBound) (columnBound := columnBound)
            (hlengthBound := hlengthBound) (htotal := htotal) (hN := hN)
            (δ₂ := δ₂) (hδ₂ := hδ₂.le) (cap := cap) (annulus := hi) (amplitude := originalBound)
            (hannulus := hhi) (hamplitude := hamplitude) (hY₁ := hY₁) (hY₂ := hY₂)
            (profiles := originalWindow) (hzero := hzero) (ht := htime) (hprime := hprime)
            (hwindow := fun _ h => h.2) (hcap := hcap) (hδsum := hδsum)
            (hcolumnBound := hcolumnBound) (loss := loss) (cutoffExponent := cutoffExponent)
            (hloss := hloss) (hcutoffExponent := hcutoffExponent) (hannulusZ := hannulusZ)
            (hrows := hrows) (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
            (pool := pool) (hdensity := hdensity)
            DE D S χ prime (AmplifierValuation.one).multiplicity v.2.2.1 v.2.2.2.1
        · intro thetaPair z
          have hnorm : firstLeftAllowance Z
              (first.skeleton.A + (first.skeleton.q + first.skeleton.R + first.skeleton.E))
              first.ideals.first.val first.ideals.opposite.val =
            (parents).firstAllowanceAt (raw).originalAtlas total key := by
            change firstLeftAllowance Z
              (((internal).n₁ + (internal).n₂ + (internal).z) +
                ((internal).q + idealLogLength Z (firstActiveRadical
                  (((source).block DE).literalRightCoordinates D.val).first.val
                  (((source).block DE).literalRightCoordinates D.val).opposite.val) +
                  idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val))
              (((source).block DE).literalRightCoordinates D.val).first.val
              (((source).block DE).literalRightCoordinates D.val).opposite.val =
                firstRightAllowance Z (total DE D) DE.val.1 DE.val.2
            rw [((source).block DE).literalRightCoordinates_first,
              ((source).block DE).literalRightCoordinates_opposite]
            simp only [firstLeftAllowance, firstRightAllowance,
              firstActiveRadical_swap_of_support _ _ ((source).block DE).common_support_eq]
            congr 1
            unfold literalPrimitiveFirstTotal
            ring
          have hradical :
              (Ideal.absNorm (commonRadical
                (primePowerProduct v.block.primes v.block.leftMultiplicity).val
                (primePowerProduct v.block.primes v.block.rightMultiplicity).val) : ℝ) =
              (Ideal.absNorm (commonRadical ((parents).commonLabel (raw).originalAtlas key).1
                ((parents).commonLabel (raw).originalAtlas key).2) : ℝ) :=
            congrArg₂ (fun I J : Ideal (𝓞 K) => (Ideal.absNorm (commonRadical I J) : ℝ))
              v.block.common_left v.block.common_right
          have hmoving : movingAt key = movingCost := by
            change ((AmplifierValuation.one).movingMultiplicity : ℝ) *
                idealLogLength Z prime.val.val.asIdeal + 0 = _
            have he : (AmplifierValuation.one).movingMultiplicity =
                amplifierMovingExponent (AmplifierValuation.one).multiplicity := rfl
            rw [he, add_zero]
          have houter :
              ((X.stripOuter leftScalar rightScalar construction.property.2.1
                construction.property.2.2).thetaClassLeaf characters thetaPair).exceptionalIntegrand z =
              (outer.thetaClassLeaf characters thetaPair).exceptionalIntegrand z := by
            have hl :
                ((X.stripOuter leftScalar rightScalar construction.property.2.1
                  construction.property.2.2).thetaClassLeaf characters thetaPair).leftFirst =
                (outer.thetaClassLeaf characters thetaPair).leftFirst := by
              funext h k
              change -(-Real.log _) = _
              exact neg_neg _
            have hr :
                ((X.stripOuter leftScalar rightScalar construction.property.2.1
                  construction.property.2.2).thetaClassLeaf characters thetaPair).rightFirst =
                (outer.thetaClassLeaf characters thetaPair).rightFirst := by
              funext h k
              change -(-Real.log _) = _
              exact neg_neg _
            unfold ActualHybridLeaf.exceptionalIntegrand
            rw [hl, hr] <;> rfl
          by_cases hc : centered = true
          · have hp := literalPrimitiveRightPoolExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (hfirstBox := hfirstBox)
              (hwidth := hwidth) (hthreshold := hthreshold) (hvolume := hvolume)
              (valuation := AmplifierValuation.one) (prime := prime)
              hc (hpadding hc) thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_pos hc, hmoving] using hp
          · have hc' : centered = false := Bool.eq_false_of_not_eq_true hc
            have hp := literalPrimitiveRightPoolOrdinaryExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (valuation := AmplifierValuation.one) (prime := prime)
              hc' thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_neg hc, zero_add, hmoving] using hp
      · have hfiberOriginal := ((((stages DE D).right S χ).six prime).supported.gated.fiberCoveredLeaf
          ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual prime 6)
          ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual prime 6)
          (((exceptional DE D).right S χ).six prime)
          ((source).charts DE D).kernel (fun i => -((source).charts DE D).rightPoint i.val) leaf).live_of_scale_live _ _ hpool
        let first := OriginalNominalGeometry.canonicalPoolError
          (a := internal) pool (AmplifierValuation.six) prime (((source).block DE).literalRightCoordinates D.val)
          supportError hsupportError
        let rowWindow := (((source).pools DE D).divisorPools.rightData S).literalPoolRows
          internal (((source).block DE).literalRightCoordinates D.val) supportError hsupportError
          hstep (rightRows DE D S) (AmplifierValuation.six) prime
        let stage := (((source).pools DE D).divisorPools.rightData S).literalValuationStage
          (hΓ := hΓ₀) (μv := μv) (hDiff := hDiff) (ν := ν)
          (((source).pools DE D).rightDivisorCoefficient S χ) P internal
          (((source).block DE).literalRightCoordinates D.val) supportError hsupportError
          hstep (rightRows DE D S) δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ (AmplifierValuation.six) prime
        let cover := (((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual prime (AmplifierValuation.six).multiplicity
        let point : (((source).pools DE D).divisorPools.rightData S).valuationColumns prime.val (AmplifierValuation.six).multiplicity → ℝ := (fun i => Real.log (A.exteriorNorm (((source).block DE).rightResidual i.val)))
        let movingCost := (amplifierMovingExponent (AmplifierValuation.six).multiplicity : ℝ) *
          idealLogLength Z prime.val.val.asIdeal
        let firstFixed := ((source).block DE).literalRightFixed D.val
        let hfirst := ((source).block DE).literalRightFixed_generates C D.val
        let phases := CanonicalLiteralActualCharacters.amplifiedPhases C
          firstFixed (CanonicalLiteralFirstPhase.rightElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst prime.val (AmplifierValuation.six).multiplicity
        let predicate := stage.supported.gated.literalHybridPredicates
          cover cover P R phases Q.moving Q.correction (data ξ).theta
        have hpoint : (fun i => -((source).charts DE D).rightPoint i.val) = point := by
          funext k
          change -(-Real.log _) = _
          exact neg_neg _
        have hfiber : (stage.supported.gated.fiberCoveredLeaf cover cover predicate
            ((source).charts DE D).kernel point leaf).Live := by
          rw [hpoint] at hfiberOriginal
          exact hfiberOriginal
        let v := leaf.1
        let j := leaf.2
        let bareLive := (v.leaf predicate ((source).charts DE D).kernel point j).live_of_scale_live _ _ hfiber
        let construction := literalRightPoolExceptionalExtraction
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
            (retainedScale := first.retainedScale) (g := first.enlargement) (hscale := first.retainedScale_pos)
            (domain := domainInternal) (v := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
            (firstFixed := firstFixed) (hfirst := hfirst) (j := j) (hS := hS)
            (q := prime) (n := (AmplifierValuation.six).multiplicity) (hlive := hfiber)
        let oldLeftAtoms := literalRightPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ prime (AmplifierValuation.six).multiplicity v.2.2.1
        let oldRightAtoms := literalRightPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ prime (AmplifierValuation.six).multiplicity v.2.2.2.1
        let leftScalar := literalRightPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ prime (AmplifierValuation.six).multiplicity v.2.2.1 * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rightScalar := literalRightPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ prime (AmplifierValuation.six).multiplicity v.2.2.2.1 * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rawRows := v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel
        let characters := rawRows.literalFiniteCharacters C P R phases Q.moving Q.correction
          (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
          (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) (data ξ).theta
        let outer := construction.val.stripOuter leftScalar rightScalar
          construction.property.2.1 construction.property.2.2
        let key : (parents).CoveredLeafKey (raw).originalAtlas := ⟨DE, D, S, χ, .inr (.inr (.inr (.inl ⟨prime, leaf⟩)))⟩
        let X : ((parents).parentLeaf (raw).originalAtlas exceptional normalization key).ConstantAtomExtraction := {
          leftScalar := construction.val.leftScalar
          rightScalar := construction.val.rightScalar
          leftResidual := construction.val.leftResidual
          rightResidual := construction.val.rightResidual
          left := construction.val.left
          right := construction.val.right }
        refine ⟨X, leftScalar, rightScalar, construction.property.2.1,
          construction.property.2.2, characters, rfl, ?_, ?_⟩
        · exact literalPrimitiveRightPoolExceptional_firstProfile_le
            (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
            (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
            (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
            (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
            (domain := domain) (lengthBound := lengthBound) (columnBound := columnBound)
            (hlengthBound := hlengthBound) (htotal := htotal) (hN := hN)
            (δ₂ := δ₂) (hδ₂ := hδ₂.le) (cap := cap) (annulus := hi) (amplitude := originalBound)
            (hannulus := hhi) (hamplitude := hamplitude) (hY₁ := hY₁) (hY₂ := hY₂)
            (profiles := originalWindow) (hzero := hzero) (ht := htime) (hprime := hprime)
            (hwindow := fun _ h => h.2) (hcap := hcap) (hδsum := hδsum)
            (hcolumnBound := hcolumnBound) (loss := loss) (cutoffExponent := cutoffExponent)
            (hloss := hloss) (hcutoffExponent := hcutoffExponent) (hannulusZ := hannulusZ)
            (hrows := hrows) (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
            (pool := pool) (hdensity := hdensity)
            DE D S χ prime (AmplifierValuation.six).multiplicity v.2.2.1 v.2.2.2.1
        · intro thetaPair z
          have hnorm : firstLeftAllowance Z
              (first.skeleton.A + (first.skeleton.q + first.skeleton.R + first.skeleton.E))
              first.ideals.first.val first.ideals.opposite.val =
            (parents).firstAllowanceAt (raw).originalAtlas total key := by
            change firstLeftAllowance Z
              (((internal).n₁ + (internal).n₂ + (internal).z) +
                ((internal).q + idealLogLength Z (firstActiveRadical
                  (((source).block DE).literalRightCoordinates D.val).first.val
                  (((source).block DE).literalRightCoordinates D.val).opposite.val) +
                  idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val))
              (((source).block DE).literalRightCoordinates D.val).first.val
              (((source).block DE).literalRightCoordinates D.val).opposite.val =
                firstRightAllowance Z (total DE D) DE.val.1 DE.val.2
            rw [((source).block DE).literalRightCoordinates_first,
              ((source).block DE).literalRightCoordinates_opposite]
            simp only [firstLeftAllowance, firstRightAllowance,
              firstActiveRadical_swap_of_support _ _ ((source).block DE).common_support_eq]
            congr 1
            unfold literalPrimitiveFirstTotal
            ring
          have hradical :
              (Ideal.absNorm (commonRadical
                (primePowerProduct v.block.primes v.block.leftMultiplicity).val
                (primePowerProduct v.block.primes v.block.rightMultiplicity).val) : ℝ) =
              (Ideal.absNorm (commonRadical ((parents).commonLabel (raw).originalAtlas key).1
                ((parents).commonLabel (raw).originalAtlas key).2) : ℝ) :=
            congrArg₂ (fun I J : Ideal (𝓞 K) => (Ideal.absNorm (commonRadical I J) : ℝ))
              v.block.common_left v.block.common_right
          have hmoving : movingAt key = movingCost := by
            change ((AmplifierValuation.six).movingMultiplicity : ℝ) *
                idealLogLength Z prime.val.val.asIdeal + 0 = _
            have he : (AmplifierValuation.six).movingMultiplicity =
                amplifierMovingExponent (AmplifierValuation.six).multiplicity := rfl
            rw [he, add_zero]
          have houter :
              ((X.stripOuter leftScalar rightScalar construction.property.2.1
                construction.property.2.2).thetaClassLeaf characters thetaPair).exceptionalIntegrand z =
              (outer.thetaClassLeaf characters thetaPair).exceptionalIntegrand z := by
            have hl :
                ((X.stripOuter leftScalar rightScalar construction.property.2.1
                  construction.property.2.2).thetaClassLeaf characters thetaPair).leftFirst =
                (outer.thetaClassLeaf characters thetaPair).leftFirst := by
              funext h k
              change -(-Real.log _) = _
              exact neg_neg _
            have hr :
                ((X.stripOuter leftScalar rightScalar construction.property.2.1
                  construction.property.2.2).thetaClassLeaf characters thetaPair).rightFirst =
                (outer.thetaClassLeaf characters thetaPair).rightFirst := by
              funext h k
              change -(-Real.log _) = _
              exact neg_neg _
            unfold ActualHybridLeaf.exceptionalIntegrand
            rw [hl, hr] <;> rfl
          by_cases hc : centered = true
          · have hp := literalPrimitiveRightPoolExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (hfirstBox := hfirstBox)
              (hwidth := hwidth) (hthreshold := hthreshold) (hvolume := hvolume)
              (valuation := AmplifierValuation.six) (prime := prime)
              hc (hpadding hc) thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_pos hc, hmoving] using hp
          · have hc' : centered = false := Bool.eq_false_of_not_eq_true hc
            have hp := literalPrimitiveRightPoolOrdinaryExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (valuation := AmplifierValuation.six) (prime := prime)
              hc' thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_neg hc, zero_add, hmoving] using hp
      · have hfiberOriginal := ((((stages DE D).right S χ).seven prime).supported.gated.fiberCoveredLeaf
          ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual prime 7)
          ((((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual prime 7)
          (((exceptional DE D).right S χ).seven prime)
          ((source).charts DE D).kernel (fun i => -((source).charts DE D).rightPoint i.val) leaf).live_of_scale_live _ _ hpool
        let first := OriginalNominalGeometry.canonicalPoolError
          (a := internal) pool (AmplifierValuation.seven) prime (((source).block DE).literalRightCoordinates D.val)
          supportError hsupportError
        let rowWindow := (((source).pools DE D).divisorPools.rightData S).literalPoolRows
          internal (((source).block DE).literalRightCoordinates D.val) supportError hsupportError
          hstep (rightRows DE D S) (AmplifierValuation.seven) prime
        let stage := (((source).pools DE D).divisorPools.rightData S).literalValuationStage
          (hΓ := hΓ₀) (μv := μv) (hDiff := hDiff) (ν := ν)
          (((source).pools DE D).rightDivisorCoefficient S χ) P internal
          (((source).block DE).literalRightCoordinates D.val) supportError hsupportError
          hstep (rightRows DE D S) δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ (AmplifierValuation.seven) prime
        let cover := (((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ).residual prime (AmplifierValuation.seven).multiplicity
        let point : (((source).pools DE D).divisorPools.rightData S).valuationColumns prime.val (AmplifierValuation.seven).multiplicity → ℝ := (fun i => Real.log (A.exteriorNorm (((source).block DE).rightResidual i.val)))
        let movingCost := (amplifierMovingExponent (AmplifierValuation.seven).multiplicity : ℝ) *
          idealLogLength Z prime.val.val.asIdeal
        let firstFixed := ((source).block DE).literalRightFixed D.val
        let hfirst := ((source).block DE).literalRightFixed_generates C D.val
        let phases := CanonicalLiteralActualCharacters.amplifiedPhases C
          firstFixed (CanonicalLiteralFirstPhase.rightElement C ((source).block DE).primes
            ((source).block DE).leftMultiplicity ((source).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst prime.val (AmplifierValuation.seven).multiplicity
        let predicate := stage.supported.gated.literalHybridPredicates
          cover cover P R phases Q.moving Q.correction (data ξ).theta
        have hpoint : (fun i => -((source).charts DE D).rightPoint i.val) = point := by
          funext k
          change -(-Real.log _) = _
          exact neg_neg _
        have hfiber : (stage.supported.gated.fiberCoveredLeaf cover cover predicate
            ((source).charts DE D).kernel point leaf).Live := by
          rw [hpoint] at hfiberOriginal
          exact hfiberOriginal
        let v := leaf.1
        let j := leaf.2
        let bareLive := (v.leaf predicate ((source).charts DE D).kernel point j).live_of_scale_live _ _ hfiber
        let construction := literalRightPoolExceptionalExtraction
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
            (retainedScale := first.retainedScale) (g := first.enlargement) (hscale := first.retainedScale_pos)
            (domain := domainInternal) (v := v) («exceptional» := predicate) (F := ((source).charts DE D).kernel)
            (firstFixed := firstFixed) (hfirst := hfirst) (j := j) (hS := hS)
            (q := prime) (n := (AmplifierValuation.seven).multiplicity) (hlive := hfiber)
        let oldLeftAtoms := literalRightPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ prime (AmplifierValuation.seven).multiplicity v.2.2.1
        let oldRightAtoms := literalRightPoolAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ firstFixed hfirst δ₂ prime (AmplifierValuation.seven).multiplicity v.2.2.2.1
        let leftScalar := literalRightPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ prime (AmplifierValuation.seven).multiplicity v.2.2.1 * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rightScalar := literalRightPoolScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
          Z t Y₁ Y₂ centered hZ hY₁ hY₂ ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
          (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
          ((source).pools DE D) S χ prime (AmplifierValuation.seven).multiplicity v.2.2.2.1 * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
        let rawRows := v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel
        let characters := rawRows.literalFiniteCharacters C P R phases Q.moving Q.correction
          (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
          (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) (data ξ).theta
        let outer := construction.val.stripOuter leftScalar rightScalar
          construction.property.2.1 construction.property.2.2
        let key : (parents).CoveredLeafKey (raw).originalAtlas := ⟨DE, D, S, χ, .inr (.inr (.inr (.inr ⟨prime, leaf⟩)))⟩
        let X : ((parents).parentLeaf (raw).originalAtlas exceptional normalization key).ConstantAtomExtraction := {
          leftScalar := construction.val.leftScalar
          rightScalar := construction.val.rightScalar
          leftResidual := construction.val.leftResidual
          rightResidual := construction.val.rightResidual
          left := construction.val.left
          right := construction.val.right }
        refine ⟨X, leftScalar, rightScalar, construction.property.2.1,
          construction.property.2.2, characters, rfl, ?_, ?_⟩
        · exact literalPrimitiveRightPoolExceptional_firstProfile_le
            (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
            (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
            (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
            (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
            (domain := domain) (lengthBound := lengthBound) (columnBound := columnBound)
            (hlengthBound := hlengthBound) (htotal := htotal) (hN := hN)
            (δ₂ := δ₂) (hδ₂ := hδ₂.le) (cap := cap) (annulus := hi) (amplitude := originalBound)
            (hannulus := hhi) (hamplitude := hamplitude) (hY₁ := hY₁) (hY₂ := hY₂)
            (profiles := originalWindow) (hzero := hzero) (ht := htime) (hprime := hprime)
            (hwindow := fun _ h => h.2) (hcap := hcap) (hδsum := hδsum)
            (hcolumnBound := hcolumnBound) (loss := loss) (cutoffExponent := cutoffExponent)
            (hloss := hloss) (hcutoffExponent := hcutoffExponent) (hannulusZ := hannulusZ)
            (hrows := hrows) (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
            (pool := pool) (hdensity := hdensity)
            DE D S χ prime (AmplifierValuation.seven).multiplicity v.2.2.1 v.2.2.2.1
        · intro thetaPair z
          have hnorm : firstLeftAllowance Z
              (first.skeleton.A + (first.skeleton.q + first.skeleton.R + first.skeleton.E))
              first.ideals.first.val first.ideals.opposite.val =
            (parents).firstAllowanceAt (raw).originalAtlas total key := by
            change firstLeftAllowance Z
              (((internal).n₁ + (internal).n₂ + (internal).z) +
                ((internal).q + idealLogLength Z (firstActiveRadical
                  (((source).block DE).literalRightCoordinates D.val).first.val
                  (((source).block DE).literalRightCoordinates D.val).opposite.val) +
                  idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val))
              (((source).block DE).literalRightCoordinates D.val).first.val
              (((source).block DE).literalRightCoordinates D.val).opposite.val =
                firstRightAllowance Z (total DE D) DE.val.1 DE.val.2
            rw [((source).block DE).literalRightCoordinates_first,
              ((source).block DE).literalRightCoordinates_opposite]
            simp only [firstLeftAllowance, firstRightAllowance,
              firstActiveRadical_swap_of_support _ _ ((source).block DE).common_support_eq]
            congr 1
            unfold literalPrimitiveFirstTotal
            ring
          have hradical :
              (Ideal.absNorm (commonRadical
                (primePowerProduct v.block.primes v.block.leftMultiplicity).val
                (primePowerProduct v.block.primes v.block.rightMultiplicity).val) : ℝ) =
              (Ideal.absNorm (commonRadical ((parents).commonLabel (raw).originalAtlas key).1
                ((parents).commonLabel (raw).originalAtlas key).2) : ℝ) :=
            congrArg₂ (fun I J : Ideal (𝓞 K) => (Ideal.absNorm (commonRadical I J) : ℝ))
              v.block.common_left v.block.common_right
          have hmoving : movingAt key = movingCost := by
            change ((AmplifierValuation.seven).movingMultiplicity : ℝ) *
                idealLogLength Z prime.val.val.asIdeal + 0 = _
            have he : (AmplifierValuation.seven).movingMultiplicity =
                amplifierMovingExponent (AmplifierValuation.seven).multiplicity := rfl
            rw [he, add_zero]
          have houter :
              ((X.stripOuter leftScalar rightScalar construction.property.2.1
                construction.property.2.2).thetaClassLeaf characters thetaPair).exceptionalIntegrand z =
              (outer.thetaClassLeaf characters thetaPair).exceptionalIntegrand z := by
            have hl :
                ((X.stripOuter leftScalar rightScalar construction.property.2.1
                  construction.property.2.2).thetaClassLeaf characters thetaPair).leftFirst =
                (outer.thetaClassLeaf characters thetaPair).leftFirst := by
              funext h k
              change -(-Real.log _) = _
              exact neg_neg _
            have hr :
                ((X.stripOuter leftScalar rightScalar construction.property.2.1
                  construction.property.2.2).thetaClassLeaf characters thetaPair).rightFirst =
                (outer.thetaClassLeaf characters thetaPair).rightFirst := by
              funext h k
              change -(-Real.log _) = _
              exact neg_neg _
            unfold ActualHybridLeaf.exceptionalIntegrand
            rw [hl, hr] <;> rfl
          by_cases hc : centered = true
          · have hp := literalPrimitiveRightPoolExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (hfirstBox := hfirstBox)
              (hwidth := hwidth) (hthreshold := hthreshold) (hvolume := hvolume)
              (valuation := AmplifierValuation.seven) (prime := prime)
              hc (hpadding hc) thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_pos hc, hmoving] using hp
          · have hc' : centered = false := Bool.eq_false_of_not_eq_true hc
            have hp := literalPrimitiveRightPoolOrdinaryExceptional_pointwise
              (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
              (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
              (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
              (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
              (hY₁ := hY₁) (hY₂ := hY₂) (cap := cap) (loss := loss) (cutoffExponent := cutoffExponent)
              (hloss := hloss) (hcutoffExponent := hcutoffExponent) (step := step) (hstep := hstep)
              (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
              (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
              (hcutoffPower := hcutoffPower) (hcutoffPower₂ := hcutoffPower₂)
              (reference := reference) (href := href) (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi)
              (primitive := primitive) (ε := ε) (widthMax := widthMax) (hε := hε) (hwidthMax := hwidthMax)
              (originalBound := originalBound) (hamplitude := hamplitude)
              (originalWindow := originalWindow) (hrows := hrows) (htime := htime) (hprime := hprime)
              (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (hone := hone) (hplaces := hplaces)
              (hlower := hlower) (hδsum := hδsum) (slotLoss := slotLoss) (finalLoss := finalLoss)
              (hslotLossNonneg := hslotLossNonneg) (hfinalLoss := hfinalLoss)
              (hslotLoss := hslotLoss) (hslots := hslots) (hsupport := hsupport)
              (DE := DE) (D := D) (S := S) (χ := χ) (leaf := leaf) (hsquarefree := hS) (hlive := hfiber)
              (lengthBound := lengthBound) (columnBound := columnBound)
              (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
              (htotal := htotal) (hN := hN) (pool := pool) (hdensity := hdensity)
              (valuation := AmplifierValuation.seven) (prime := prime)
              hc' thetaPair z
            rw [← houter, hnorm, hradical] at hp
            simpa only [if_neg hc, zero_add, hmoving] using hp
  obtain ⟨X, aa, bb, haa, hbb, characters, hpredicate, hfirst, hsecond⟩ := hsource
  have hb := (parents).exceptionalCost_of_original_source (raw).originalAtlas hcap hZ total
    exceptional i X aa bb haa hbb characters hpredicate (a.m + a.q)
    (firstConstant * originalBound ^ (2 * cap)) (secondConstant * originalBound ^ degree)
    (remaining + movingAt i.val) (idealLogLength Z ((parents).innerDivisor (raw).originalAtlas i.val)) tilt
    heightOrder hfirstCost hsecondCost hfirst hsecond
  have hkernels :
      ((parents).parentLeaf (raw).originalAtlas exceptional normalization i.val).firstKernel = firstKernel ∧
      ((parents).parentLeaf (raw).originalAtlas exceptional normalization i.val).secondKernel = secondKernel := by
    rcases i with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩
    all_goals
      rcases leaf with leaf | (⟨prime, leaf⟩ | (⟨prime, leaf⟩ | ⟨prime, leaf⟩)) <;>
        exact ⟨rfl, rfl⟩
  rw [hkernels.1, hkernels.2] at hb
  have hdegree : 2 * cap + degree = 14 * cap + 10 := by
    rw [CanonicalLiteralExceptionalSourceBudget.profileDegree_eq]
    unfold CanonicalLiteralExceptionalAtomBudget.commonDegree
    omega
  have hpower : originalBound ^ (2 * cap) * originalBound ^ degree =
      originalBound ^ (14 * cap + 10) := by rw [← pow_add, hdegree]
  have he :
      ((data ξ).theta.card : ℝ) ^ 2 * (firstConstant * originalBound ^ (2 * cap)) *
          (secondConstant * originalBound ^ degree) * (1 + 2 * Real.pi) ^ heightOrder *
          fourierCost = integralConstant * originalBound ^ (14 * cap + 10) := by
    calc
      _ = integralConstant * (originalBound ^ (2 * cap) * originalBound ^ degree) := by ring
      _ = _ := by rw [hpower]
  have hexponent : (remaining + movingAt i.val) + tilt =
      remaining + tilt + movingAt i.val := by ring
  rw [he, hexponent] at hb
  exact hb

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledExceptional_integral
