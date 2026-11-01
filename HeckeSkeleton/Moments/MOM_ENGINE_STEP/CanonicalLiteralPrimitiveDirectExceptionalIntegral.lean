import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectExceptionalSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveExceptionalFirstProfile
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalExactIndex

/-!
# Integrate the same original direct exceptional leaves

Both first scalars are the actual redistributed scalars. Their original
profile estimate is combined with the proved exceptional source estimate
on the same parent leaf. The original two Fourier kernels are fixed
before the labels, the exact allocation divisor is retained, and the
original Cauchy scalar remains explicit for the original index sum.
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
local notation "raw" => atoms.raw Y₁ Y₂


local notation "source" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
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

variable (normBound lengthBound : ℝ)
variable (hlengthBound : 0 ≤ lengthBound)
variable (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
variable (hfirstBox : normBound ≤ widthMax)
variable (hN : ∀ i ∈ source.columns,
  (Ideal.absNorm (source.ideal i).val : ℝ) ≤ Z ^ normBound)

local notation "stages" => Q.literalPrimitiveDirectStages μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap hi loss cutoffExponent hhi hcap hannulusZ domain originalWindow hrows htime
  (fun _ h => h.2) hcutoffPower step hstep hloss hcutoffExponent hDiff
  δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂
local notation "leftRows" => Q.literalPrimitiveLeftDirectRows μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap hi loss cutoffExponent hhi hcap hannulusZ domain originalWindow hrows htime
  (fun _ h => h.2) hcutoffPower step hstep hloss hcutoffExponent
local notation "rightRows" => Q.literalPrimitiveRightDirectRows μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap hi loss cutoffExponent hhi hcap hannulusZ domain originalWindow hrows htime
  (fun _ h => h.2) hcutoffPower step hstep hloss hcutoffExponent

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
local notation "normalization" => source.canonicalNormalization hZ total
local notation "predicates" => Q.literalPrimitiveDirectPredicates μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap hi loss cutoffExponent hhi hcap hannulusZ domain originalWindow hrows htime
  (fun _ h => h.2) hcutoffPower step hstep hloss hcutoffExponent hDiff
  δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂
local notation "parents" => stages.prepared
local notation "liveKeys" => parents.liveLeaves raw.originalAtlas predicates normalization
local notation "labels" => parents.arithmeticLabels raw.originalAtlas hcap predicates normalization
local notation "firstKernel" => ActualGaussStage.canonicalRowBallKernel
  (A := A) (Γ := Γ₀) μv ν δ₁ hδ₁ hδ₁half
local notation "secondKernel" => ActualGaussStage.canonicalRowBallKernel
  (A := A) (Γ := Γ₀) μv ν δ₂ hδ₂ hδ₂half
local notation "firstConstant" =>
  CanonicalLiteralPrimitiveExceptionalFirstProfile.firstConstant K cap hi
local notation "secondConstant" => hi ^ cap * orbitalFieldFactor K *
  (Γ₀.index : ℝ) * fixedCoefficient
local notation "fourierCost" => CanonicalExceptionalPaidIntegral.fourierFactor
  heightOrder heightOrder firstKernel secondKernel
local notation "integralConstant" => ((data ξ).theta.card : ℝ) ^ 2 *
  firstConstant * secondConstant * (1 + 2 * Real.pi) ^ heightOrder * fourierCost
local notation "remaining" => (if centered then padding else 0) + 3 * step + finalLoss / 2
local notation "tilt" => 4 * max lengthBound normBound * (δ₁ + δ₂)

include originalWindow hrows htime hprime href hamplitude hlo hhi hcap hY₁ hY₂ hlower hδsum
  hslotLossNonneg hfinalLoss hslotLoss hslots hone hplaces hsupport hcutoffPower₂
  hwidth hthreshold hvolume hfirstBox hN hlengthBound htotal in
/-- This is the original indexed parent cost. Its two source bounds,
finite theta sum, integrability and Fourier moments are all produced
inside the proof. The original allocation divisor becomes exactly the
same harmonic index weight. -/
theorem literalPrimitiveDirectExceptional_integral
    (hpadding : centered = true → 0 ≤ padding) (i : liveKeys) :
    (parents.parentLeaf raw.originalAtlas predicates normalization i.val).exceptionalCost /
        Z ^ (a.m + a.q) ≤
      parents.originalScalarAt raw.originalAtlas i.val *
        (integralConstant * originalBound ^ (14 * cap + 10) * Z ^ (remaining + tilt) *
          labels.carrier.indexWeight (labels.index i)) := by
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
      (X : (parents.parentLeaf raw.originalAtlas predicates normalization i.val).ConstantAtomExtraction)
      (aa bb : ℂ) (haa : aa ≠ 0) (hbb : bb ≠ 0)
      (characters : PairedFiniteCharacters (data ξ).theta
        (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ₀)),
      (parents.parentLeaf raw.originalAtlas predicates normalization i.val).exceptional =
          characters.exceptional ∧
      (source.pieces i.val.1 i.val.2.1).weightBound * (‖aa‖ * ‖bb‖) ≤
        (firstConstant * originalBound ^ (2 * cap)) *
          Z ^ ((a.m + a.q) - total i.val.1 i.val.2.1 + tilt) ∧
      ∀ thetaPair : (data ξ).theta × (data ξ).theta, ∀ z : ℝ × ℝ,
        ((X.stripOuter aa bb haa hbb).thetaClassLeaf characters thetaPair).exceptionalIntegrand z /
            parents.firstAllowanceAt raw.originalAtlas total i.val ≤
          ((secondConstant * originalBound ^ degree) *
            (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ heightOrder) *
              Z ^ remaining /
            (Ideal.absNorm (commonRadical (parents.commonLabel raw.originalAtlas i.val).1
              (parents.commonLabel raw.originalAtlas i.val).2) : ℝ) *
                Z ^ (-idealLogLength Z (parents.innerDivisor raw.originalAtlas i.val)) := by
    have hparent := parents.liveLeaves_spec raw.originalAtlas predicates normalization i
    have hS := parents.live_first_divisor_squarefree raw.originalAtlas predicates normalization i
    rcases i with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩
    · have hblock := ((parents DE D).coveredLeaf raw.originalAtlas raw.originalAtlas
        (normalization.left DE D) (normalization.right DE D)
        (normalization.left_pos DE D) (normalization.right_pos DE D)
        (predicates DE D) ⟨S, χ, .inl leaf⟩).live_of_scale_live _ _ hparent
      have hfiber := (((stages DE D).left S χ).supported.gated.fiberCoveredLeaf
        ((source.pieces DE D).leftSourceCover raw.originalAtlas S χ)
        ((source.pieces DE D).leftSourceCover raw.originalAtlas S χ)
        ((predicates DE D).left S χ) (source.charts DE D).kernel (source.charts DE D).leftPoint leaf).live_of_scale_live
          _ _ hblock
      let v := leaf.1
      let j := leaf.2
      let first := OriginalNominalGeometry.canonicalDirect
        (a := internal) (Z := Z) (step := step) ((source.block DE).literalLeftCoordinates D.val)
        supportError (zero_lt_one.trans hZ) hsupportError
      let rowWindow := leftRows DE D
      let point := (source.charts DE D).leftPoint
      let firstFixed := (source.block DE).literalLeftFixed D.val
      let hfirst := (source.block DE).literalLeftFixed_generates C D.val
      let phases := CanonicalLiteralActualCharacters.unamplifiedPhases
        firstFixed (CanonicalLiteralFirstPhase.leftElement C (source.block DE).primes
          (source.block DE).leftMultiplicity (source.block DE).rightMultiplicity
          (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst
      let predicate := (predicates DE D).left S χ
      have bareLive : (v.leaf predicate (source.charts DE D).kernel point j).Live :=
        (v.leaf predicate (source.charts DE D).kernel point j).live_of_scale_live _ _ hfiber
      let construction := literalLeftDirectExceptionalExtraction
          (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
          (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
          (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := source.block DE) (C := C)
          (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
          (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
          (radius := source.radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
          (p := source.pieces DE D) (S := S) (χ := χ) (hDiff := hDiff)
          (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
          (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
          (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
          (dyad := fun _ _ i => Fin.elim0 i)
          (retainedScale := first.retainedScale) (g := first.enlargement) (hscale := first.retainedScale_pos)
          (domain := domainInternal) (v := v) (exceptional := predicate) (F := (source.charts DE D).kernel)
          (firstFixed := firstFixed) (hfirst := hfirst) (j := j) (hS := hS)
          (hlive := bareLive)
      let oldLeftAtoms := literalLeftDirectAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
        Z t Y₁ Y₂ centered hZ hY₁ hY₂ (source.block DE) C (CanonicalRowBall.archTest K A.Sf 1)
        (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
        (rowBallFiniteFamily_compactSupport K A.Sf 1) source.radius D.val δ₁ hδ₁ hδ₁half
        (source.pieces DE D) S χ firstFixed hfirst δ₂ v.2.2.1
      let oldRightAtoms := literalLeftDirectAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
        Z t Y₁ Y₂ centered hZ hY₁ hY₂ (source.block DE) C (CanonicalRowBall.archTest K A.Sf 1)
        (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
        (rowBallFiniteFamily_compactSupport K A.Sf 1) source.radius D.val δ₁ hδ₁ hδ₁half
        (source.pieces DE D) S χ firstFixed hfirst δ₂ v.2.2.2.1
      let leftScalar := literalLeftDirectScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
        Z t Y₁ Y₂ centered hZ hY₁ hY₂ (source.block DE) C (CanonicalRowBall.archTest K A.Sf 1)
        (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
        (rowBallFiniteFamily_compactSupport K A.Sf 1) source.radius D.val δ₁ hδ₁ hδ₁half
        (source.pieces DE D) S χ v.2.2.1 * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
      let rightScalar := literalLeftDirectScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
        Z t Y₁ Y₂ centered hZ hY₁ hY₂ (source.block DE) C (CanonicalRowBall.archTest K A.Sf 1)
        (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
        (rowBallFiniteFamily_compactSupport K A.Sf 1) source.radius D.val δ₁ hδ₁ hδ₁half
        (source.pieces DE D) S χ v.2.2.2.1 * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
      let rawRows := v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel
      let characters := rawRows.literalFiniteCharacters C P R phases Q.moving Q.correction
        (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
        (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) (data ξ).theta
      let key : parents.CoveredLeafKey raw.originalAtlas := ⟨DE, D, S, χ, .inl leaf⟩
      let X : (parents.parentLeaf raw.originalAtlas predicates normalization key).ConstantAtomExtraction := {
        leftScalar := construction.val.leftScalar
        rightScalar := construction.val.rightScalar
        leftResidual := construction.val.leftResidual
        rightResidual := construction.val.rightResidual
        left := construction.val.left
        right := construction.val.right }
      refine ⟨X, leftScalar, rightScalar, construction.property.2.1,
        construction.property.2.2, characters, rfl, ?_, ?_⟩
      · exact literalPrimitiveLeftDirectExceptional_firstProfile_le
          (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
          (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
          (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
          (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
          (domain := domain) (lengthBound := lengthBound) (columnBound := normBound)
          (hlengthBound := hlengthBound) (htotal := htotal) (hN := hN)
          (δ₂ := δ₂) (hδ₂ := hδ₂.le) (cap := cap) (annulus := hi) (amplitude := originalBound)
          (hannulus := hhi) (hamplitude := hamplitude) (hY₁ := hY₁) (hY₂ := hY₂)
          (profiles := originalWindow) (hzero := hzero) (ht := htime) (hprime := hprime)
          (hwindow := fun _ h => h.2) (hcap := hcap) (hδsum := hδsum)
          DE D S χ v.2.2.1 v.2.2.2.1
      · intro thetaPair z
        have hnorm : firstLeftAllowance Z
            (first.skeleton.A + (first.skeleton.q + first.skeleton.R + first.skeleton.E))
            first.ideals.first.val first.ideals.opposite.val =
          parents.firstAllowanceAt raw.originalAtlas total key := by
          change firstLeftAllowance Z
            ((internal.n₁ + internal.n₂ + internal.z) +
              (internal.q + idealLogLength Z (firstActiveRadical
                ((source.block DE).literalLeftCoordinates D.val).first.val
                ((source.block DE).literalLeftCoordinates D.val).opposite.val) +
                idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val))
            ((source.block DE).literalLeftCoordinates D.val).first.val
            ((source.block DE).literalLeftCoordinates D.val).opposite.val =
              firstLeftAllowance Z (total DE D) DE.val.1 DE.val.2
          rw [(source.block DE).literalLeftCoordinates_first,
            (source.block DE).literalLeftCoordinates_opposite]
          congr 1
          unfold literalPrimitiveFirstTotal
          ring
        have hradical :
            (Ideal.absNorm (commonRadical
              (primePowerProduct v.block.primes v.block.leftMultiplicity).val
              (primePowerProduct v.block.primes v.block.rightMultiplicity).val) : ℝ) =
            (Ideal.absNorm (commonRadical (parents.commonLabel raw.originalAtlas key).1
              (parents.commonLabel raw.originalAtlas key).2) : ℝ) :=
          congrArg₂ (fun I J : Ideal (𝓞 K) => (Ideal.absNorm (commonRadical I J) : ℝ))
            v.block.common_left v.block.common_right
        by_cases hc : centered = true
        · have hp := literalPrimitiveLeftDirectExceptional_pointwise
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
            (normBound := normBound) (hfirstBox := hfirstBox) (hN := hN)
            (hwidth := hwidth) (hthreshold := hthreshold) (hvolume := hvolume)
            hc (hpadding hc) thetaPair z
          rw [hnorm, hradical] at hp
          simpa only [if_pos hc] using hp
        · have hc' : centered = false := Bool.eq_false_of_not_eq_true hc
          have hp := literalPrimitiveLeftDirectOrdinaryExceptional_pointwise
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
            hc' thetaPair z
          rw [hnorm, hradical] at hp
          simpa only [if_neg hc, zero_add] using hp
    · have hblock := ((parents DE D).coveredLeaf raw.originalAtlas raw.originalAtlas
        (normalization.left DE D) (normalization.right DE D)
        (normalization.left_pos DE D) (normalization.right_pos DE D)
        (predicates DE D) ⟨S, χ, .inr leaf⟩).live_of_scale_live _ _ hparent
      have hfiber := (((stages DE D).right S χ).supported.gated.fiberCoveredLeaf
        ((source.pieces DE D).rightSourceCover raw.originalAtlas S χ)
        ((source.pieces DE D).rightSourceCover raw.originalAtlas S χ)
        ((predicates DE D).right S χ) (source.charts DE D).kernel (fun i => -(source.charts DE D).rightPoint i) leaf).live_of_scale_live
          _ _ hblock
      let v := leaf.1
      let j := leaf.2
      let first := OriginalNominalGeometry.canonicalDirect
        (a := internal) (Z := Z) (step := step) ((source.block DE).literalRightCoordinates D.val)
        supportError (zero_lt_one.trans hZ) hsupportError
      let rowWindow := rightRows DE D
      let point := (fun i => -(source.charts DE D).rightPoint i)
      let firstFixed := (source.block DE).literalRightFixed D.val
      let hfirst := (source.block DE).literalRightFixed_generates C D.val
      let phases := CanonicalLiteralActualCharacters.unamplifiedPhases
        firstFixed (CanonicalLiteralFirstPhase.rightElement C (source.block DE).primes
          (source.block DE).leftMultiplicity (source.block DE).rightMultiplicity
          (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val) hfirst
      let predicate := (predicates DE D).right S χ
      have bareLive : (v.leaf predicate (source.charts DE D).kernel point j).Live :=
        (v.leaf predicate (source.charts DE D).kernel point j).live_of_scale_live _ _ hfiber
      let construction := literalRightDirectExceptionalExtraction
          (hΓ := hΓ₀) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W.at ξ)
          (a := internal) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
          (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := source.block DE) (C := C)
          (φ := CanonicalRowBall.archTest K A.Sf 1) (finiteTest := rowBallFiniteFamily K A.Sf 1)
          (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1)
          (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1)
          (radius := source.radius) (D := D.val) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
          (p := source.pieces DE D) (S := S) (χ := χ) (hDiff := hDiff)
          (hroot := hroot) (hemb := hemb) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
          (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := 0) (width := 0)
          (hnorm := rowWindow) (character := fun _ _ => (PUnit.unit : PUnit.{1}))
          (dyad := fun _ _ i => Fin.elim0 i)
          (retainedScale := first.retainedScale) (g := first.enlargement) (hscale := first.retainedScale_pos)
          (domain := domainInternal) (v := v) (exceptional := predicate) (F := (source.charts DE D).kernel)
          (firstFixed := firstFixed) (hfirst := hfirst) (j := j) (hS := hS)
          (hlive := bareLive)
      let oldLeftAtoms := literalRightDirectAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
        Z t Y₁ Y₂ centered hZ hY₁ hY₂ (source.block DE) C (CanonicalRowBall.archTest K A.Sf 1)
        (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
        (rowBallFiniteFamily_compactSupport K A.Sf 1) source.radius D.val δ₁ hδ₁ hδ₁half
        (source.pieces DE D) S χ firstFixed hfirst δ₂ v.2.2.1
      let oldRightAtoms := literalRightDirectAtoms hΓ₀ μv ν Q ξ (W.at ξ) internal
        Z t Y₁ Y₂ centered hZ hY₁ hY₂ (source.block DE) C (CanonicalRowBall.archTest K A.Sf 1)
        (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
        (rowBallFiniteFamily_compactSupport K A.Sf 1) source.radius D.val δ₁ hδ₁ hδ₁half
        (source.pieces DE D) S χ firstFixed hfirst δ₂ v.2.2.2.1
      let leftScalar := literalRightDirectScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
        Z t Y₁ Y₂ centered hZ hY₁ hY₂ (source.block DE) C (CanonicalRowBall.archTest K A.Sf 1)
        (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
        (rowBallFiniteFamily_compactSupport K A.Sf 1) source.radius D.val δ₁ hδ₁ hδ₁half
        (source.pieces DE D) S χ v.2.2.1 * (oldLeftAtoms.normProfileFactor δ₁ δ₂ : ℂ)
      let rightScalar := literalRightDirectScalar hΓ₀ μv ν Q ξ (W.at ξ) internal
        Z t Y₁ Y₂ centered hZ hY₁ hY₂ (source.block DE) C (CanonicalRowBall.archTest K A.Sf 1)
        (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
        (rowBallFiniteFamily_compactSupport K A.Sf 1) source.radius D.val δ₁ hδ₁ hδ₁half
        (source.pieces DE D) S χ v.2.2.2.1 * (oldRightAtoms.normProfileFactor δ₁ δ₂ : ℂ)
      let rawRows := v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel
      let characters := rawRows.literalFiniteCharacters C P R phases Q.moving Q.correction
        (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
        (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) (data ξ).theta
      let key : parents.CoveredLeafKey raw.originalAtlas := ⟨DE, D, S, χ, .inr leaf⟩
      let X : (parents.parentLeaf raw.originalAtlas predicates normalization key).ConstantAtomExtraction := {
        leftScalar := construction.val.leftScalar
        rightScalar := construction.val.rightScalar
        leftResidual := construction.val.leftResidual
        rightResidual := construction.val.rightResidual
        left := construction.val.left
        right := construction.val.right }
      refine ⟨X, leftScalar, rightScalar, construction.property.2.1,
        construction.property.2.2, characters, rfl, ?_, ?_⟩
      · exact literalPrimitiveRightDirectExceptional_firstProfile_le
          (μv := μv) (ν := ν) (Q := Q) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
          (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
          (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
          (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
          (domain := domain) (lengthBound := lengthBound) (columnBound := normBound)
          (hlengthBound := hlengthBound) (htotal := htotal) (hN := hN)
          (δ₂ := δ₂) (hδ₂ := hδ₂.le) (cap := cap) (annulus := hi) (amplitude := originalBound)
          (hannulus := hhi) (hamplitude := hamplitude) (hY₁ := hY₁) (hY₂ := hY₂)
          (profiles := originalWindow) (hzero := hzero) (ht := htime) (hprime := hprime)
          (hwindow := fun _ h => h.2) (hcap := hcap) (hδsum := hδsum)
          DE D S χ v.2.2.1 v.2.2.2.1
      · intro thetaPair z
        have hnorm : firstLeftAllowance Z
            (first.skeleton.A + (first.skeleton.q + first.skeleton.R + first.skeleton.E))
            first.ideals.first.val first.ideals.opposite.val =
          parents.firstAllowanceAt raw.originalAtlas total key := by
          change firstLeftAllowance Z
            ((internal.n₁ + internal.n₂ + internal.z) +
              (internal.q + idealLogLength Z (firstActiveRadical
                ((source.block DE).literalRightCoordinates D.val).first.val
                ((source.block DE).literalRightCoordinates D.val).opposite.val) +
                idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val))
            ((source.block DE).literalRightCoordinates D.val).first.val
            ((source.block DE).literalRightCoordinates D.val).opposite.val =
              firstRightAllowance Z (total DE D) DE.val.1 DE.val.2
          rw [(source.block DE).literalRightCoordinates_first,
            (source.block DE).literalRightCoordinates_opposite]
          simp only [firstLeftAllowance, firstRightAllowance,
            firstActiveRadical_swap_of_support _ _ (source.block DE).common_support_eq]
          congr 1
          unfold literalPrimitiveFirstTotal
          ring
        have hradical :
            (Ideal.absNorm (commonRadical
              (primePowerProduct v.block.primes v.block.leftMultiplicity).val
              (primePowerProduct v.block.primes v.block.rightMultiplicity).val) : ℝ) =
            (Ideal.absNorm (commonRadical (parents.commonLabel raw.originalAtlas key).1
              (parents.commonLabel raw.originalAtlas key).2) : ℝ) :=
          congrArg₂ (fun I J : Ideal (𝓞 K) => (Ideal.absNorm (commonRadical I J) : ℝ))
            v.block.common_left v.block.common_right
        by_cases hc : centered = true
        · have hp := literalPrimitiveRightDirectExceptional_pointwise
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
            (normBound := normBound) (hfirstBox := hfirstBox) (hN := hN)
            (hwidth := hwidth) (hthreshold := hthreshold) (hvolume := hvolume)
            hc (hpadding hc) thetaPair z
          rw [hnorm, hradical] at hp
          simpa only [if_pos hc] using hp
        · have hc' : centered = false := Bool.eq_false_of_not_eq_true hc
          have hp := literalPrimitiveRightDirectOrdinaryExceptional_pointwise
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
            hc' thetaPair z
          rw [hnorm, hradical] at hp
          simpa only [if_neg hc, zero_add] using hp
  obtain ⟨X, aa, bb, haa, hbb, characters, hpredicate, hfirst, hsecond⟩ := hsource
  have hb := parents.exceptionalCost_of_original_source raw.originalAtlas hcap hZ total
    predicates i X aa bb haa hbb characters hpredicate (a.m + a.q)
    (firstConstant * originalBound ^ (2 * cap)) (secondConstant * originalBound ^ degree)
    remaining (idealLogLength Z (parents.innerDivisor raw.originalAtlas i.val)) tilt
    heightOrder hfirstCost hsecondCost hfirst hsecond
  have hinner := parents.originalIndex_innerDivisor raw.originalAtlas hcap predicates normalization i
  have hdivisor : (labels.index i).2.2.2.1.val ≠ 0 := by
    change (parents.originalIndex raw.originalAtlas hcap predicates normalization i).2.2.2.1.val ≠ 0
    rw [hinner]
    exact (stages.prepared_live_inner_divisor_squarefree raw.originalAtlas predicates normalization i).ne_zero
  have hindex : labels.carrier.exceptionalDyadWeight Z
      (idealLogLength Z (parents.innerDivisor raw.originalAtlas i.val)) (labels.index i) =
      labels.carrier.indexWeight (labels.index i) := by
    change labels.carrier.exceptionalDyadWeight Z
        (idealLogLength Z (parents.innerDivisor raw.originalAtlas i.val))
        (parents.originalIndex raw.originalAtlas hcap predicates normalization i) = _
    rw [← hinner]
    exact labels.carrier.exceptionalDyadWeight_at_divisor Z hZ _ hdivisor
  have hkernels :
      (parents.parentLeaf raw.originalAtlas predicates normalization i.val).firstKernel = firstKernel ∧
      (parents.parentLeaf raw.originalAtlas predicates normalization i.val).secondKernel = secondKernel := by
    rcases i with ⟨⟨DE, D, S, χ, leaf | leaf⟩, hj⟩ <;> exact ⟨rfl, rfl⟩
  rw [hindex, hkernels.1, hkernels.2] at hb
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
  rw [he] at hb
  exact hb

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectExceptional_integral
