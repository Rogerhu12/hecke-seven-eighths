import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveSideProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSideRadius

/-!
# Exact radii of the actual passive side

These are projections of `literalPassiveSideNormalization`, which first
constructs its paid calibration and then constructs the capacity input.
The branch is the actual independent passive allocation. Its computed
profile representatives come from the original table, and its clipping
coefficient is evaluated at this branch's own two quotient scales.

The individual analytic certificates are the final two arguments. No
finished normalization, radius estimate or capacity inequality is an
input. The original nominal row and support parameters identify the
single-prime deletion cost; the same chosen capacity remains in use.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckePort.Moments
open HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralAllocatedData CanonicalLiteralPassiveSource
open CanonicalLiteralPassiveFrames CanonicalLiteralPassiveNonzero
open CanonicalLiteralPaidCharacters

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset α} {right : Finset β}
variable {profiles : α → β → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := ℝ) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (hclass : chart.NonunitLabelStable) (hsector : chart.SectorLabelStable P)
variable (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
variable (weight : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → ℂ)
variable (keep₁ keep₂ : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)
variable {kLeft kRight : ℕ}
variable (rowMass : ActualSecondRowMass
  ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁)
    .restrictRows keep₂) C kLeft kRight)
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k) (W : d.ProfileData)
variable (B : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A) (choice : PhaseChoice F C)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (slots : OriginalSlotDictionary parent d.length)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A (choice.mask extra) })
variable (ha : a ∈ nonzeroLabels W B A (choice.mask extra))
variable (retainedScale g a₀ oldq wo cutoffExponent : ℝ)
variable (hscale : 0 < retainedScale)
variable (hradius : radius = CanonicalRowBall.gaussRadius retainedScale d.base g hscale
  (zero_lt_one.trans d.base_gt_one))
variable (hcutoff : X ≤ d.base ^ cutoffExponent)
variable (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
  (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ d.base ^ (2 * a₀))
variable (hpaidSupport : A.exteriorNorm
  ((choice.phases.moving P Rchar oldMoving).effectiveFullSupport remaining) ≤
    d.base ^ (oldq + wo))
variable (m q κ : ℝ)
variable (hwidth : m + q =
  secondCommonChildWidth d.base a₀ oldq wo (Real.log retainedScale / Real.log d.base) g
    (primePowerProduct b.primes b.leftMultiplicity).val
    (primePowerProduct b.primes b.rightMultiplicity).val
    (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity
      (chart.originalNonunitPattern ∅ X hX label)).val
    (secondPatternNonunitIdeal b.primes (chart.originalNonunitPattern ∅ X hX label)).val +
    idealLogLength d.base (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
    cutoffExponent)
variable (inverse : IdealTest K)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (hbackground : parent.plainBackground⁻¹ ∈ parent.theta ∨
  ¬ FiniteOrder parent.plainBackground)
variable (hslot : ∀ i, parent.slotCoefficient i ∈ parent.theta)
variable (side : SecondColumnSide) (firstSign : ℝ) (rectangle : Bool)

local notation "S" =>
  (({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁)
    .restrictRows keep₂
local notation "pattern" => chart.originalNonunitPattern ∅ X hX label
local notation "sector" => chart.originalSector P ∅ X hX label
local notation "idx" => (fun j => slots.index (SlotRestriction.index B.keep j))
local notation "paid" => paidSourceCharacters P Rchar choice.phases parent oldMoving
  correction remaining idx
local notation "t" => table W B A paid
local notation "E" => CanonicalLiteralPassiveSource.profiles W B A paid
local notation "allocation" => branch W B A (choice.mask extra) a
local notation "f" => frame W B A paid C S side (choice.mask extra) a firstSign rectangle

variable (keep₂_eq : keep₂ = fun h =>
  (chart.actualRows ∅ X hX label).literalCharacter C P Rchar F oldMoving correction
    (chart.originalNonunitPattern ∅ X hX label) (chart.originalSector P ∅ X hX label) h ∉
      parent.theta)
variable (parentParameters : RealParameters) (step : ℝ)
variable (geometry : OriginalNominalGeometry (K := K) parentParameters
  (frame W B A (paidSourceCharacters P Rchar choice.phases parent oldMoving correction
    remaining (fun j => slots.index (SlotRestriction.index B.keep j))) C
    ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁)
      .restrictRows keep₂) side (choice.mask extra) a firstSign rectangle).source.base step)
variable (capacityCutoff : ℝ) (hcapacityCutoff : 0 ≤ capacityCutoff)
variable (hsmall : 2 * capacityCutoff ≤ step)
variable (rowParameter : geometry.literalRowParameter capacityCutoff = m)
variable (supportParameter : geometry.literalSupportParameter
  (idealLogLength
    (frame W B A (paidSourceCharacters P Rchar choice.phases parent oldMoving correction
      remaining (fun j => slots.index (SlotRestriction.index B.keep j))) C
      ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁)
        .restrictRows keep₂) side (choice.mask extra) a firstSign rectangle).source.base
    (secondSixthRootIdeal b.primes
      (side.literalMultiplicity (chart.actualRows ∅ X hX label))
      (side.literalOppositeMultiplicity (chart.actualRows ∅ X hX label))).val) = q)
variable (kappa : κ = parentParameters.κ)
variable {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered parent parentParameters
  (frame W B A (paidSourceCharacters P Rchar choice.phases parent oldMoving correction
    remaining (fun j => slots.index (SlotRestriction.index B.keep j))) C
    ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁)
      .restrictRows keep₂) side (choice.mask extra) a firstSign rectangle).source.base
    Y₁ Y₂ floor padding)
variable (direct : geometry.tag = .direct → parent.geometry.slotCount = 0)
variable (error : ℝ) (herr : 0 ≤ error)
variable (hsecond : geometry.ideals.second.val =
  (primePowerProduct b.primes
    (side.literalMultiplicity (chart.actualRows ∅ X hX label))).val)
variable (hopposite : geometry.ideals.secondOpposite.val =
  (primePowerProduct b.primes
    (side.literalOppositeMultiplicity (chart.actualRows ∅ X hX label))).val)
variable (hunit : geometry.ideals.unitPart.val =
  (secondPatternUnitIdeal b.primes
    (side.literalMultiplicity (chart.actualRows ∅ X hX label))
    (side.literalOppositeMultiplicity (chart.actualRows ∅ X hX label))
    (chart.originalNonunitPattern ∅ X hX label)).val)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable (inverse_eq : inverse = CanonicalLiteralProfileData.frozenNormTest
  parent.inverseTest reference time)
variable {originalRows : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {originalHeights : Set ℝ} {originalOrders : Finset (ℕ × ℕ)}
variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi) (orders : Finset (ℕ × ℕ))
variable {bound : ℝ}
variable (original : RawProfileWindow originalRows originalHeights (Set.Icc lo hi)
  originalOrders parent bound)
variable (hreference : reference ∈ originalRows) (htime : time ∈ originalHeights)
variable (horders : orders ⊆ originalOrders)
variable (computed : CanonicalLiteralFullKappaInput.ComputedProfiles W (Set.Icc lo hi) orders bound)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (δ analyticHeight : ℝ) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)

local notation "calibration" =>
  chart.literalPassiveFrameCalibration P Rchar hclass hsector X hX label
    weight keep₁ keep₂ rowMass d W B F choice parent oldMoving correction hcorr remaining extra
    slots.index a ha retainedScale g a₀ oldq wo cutoffExponent hscale hradius hcutoff hproduct
    hpaidSupport m q κ hwidth inverse hone hroot hemb hbackground hslot side firstSign rectangle
    keep₂_eq

local notation "produced" =>
  chart.literalPassiveSideNormalization
    (P := P) (Rchar := Rchar) (hclass := hclass) (hsector := hsector)
    (X := X) (hX := hX) (label := label) (weight := weight)
    (keep₁ := keep₁) (keep₂ := keep₂) (rowMass := rowMass)
    (d := d) (W := W) (B := B) (F := F) (choice := choice)
    (parent := parent) (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (slots := slots) (a := a) (ha := ha)
    (retainedScale := retainedScale) (g := g) (a₀ := a₀) (oldq := oldq) (wo := wo)
    (cutoffExponent := cutoffExponent) (hscale := hscale) (hradius := hradius)
    (hcutoff := hcutoff) (hproduct := hproduct) (hpaidSupport := hpaidSupport)
    (m := m) (q := q) (κ := κ) (hwidth := hwidth) (inverse := inverse)
    (hone := hone) (hroot := hroot) (hemb := hemb)
    (hbackground := hbackground) (hslot := hslot) (side := side)
    (firstSign := firstSign) (rectangle := rectangle) (keep₂_eq := keep₂_eq)
    (parentParameters := parentParameters) (step := step) (geometry := geometry)
    (capacityCutoff := capacityCutoff) (hcapacityCutoff := hcapacityCutoff)
    (hsmall := hsmall) (rowParameter := rowParameter) (supportParameter := supportParameter)
    (kappa := kappa) (domain := domain) (direct := direct) (error := error) (herr := herr)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh) (hfit := hfit)
    (reference := reference) (time := time) (inverse_eq := inverse_eq)
    (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := original) (hreference := hreference) (htime := htime) (horders := horders)
    (computed := computed) (hprimeOrders := hprimeOrders)
    (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)

local notation "rootLength" => idealLogLength f.source.base
  (secondSixthRootIdeal S.primes (side.literalMultiplicity S)
    (side.literalOppositeMultiplicity S)).val
local notation "rawCoefficient" =>
  (computed.passiveTable B A paid).coefficient f.source.base
    (CanonicalLiteralAllocatedData.parameters t allocation rectangle m q κ)
    isCompact_Icc (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign rectangle
local notation "enlargement" =>
  CanonicalFullKappaPrime.radiusFactor K f.source.base δ mesh
    (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
    (CompleteMovingRowRecipe.primeMaskLogBound A f.source.base (m + q))

/-- The calibration stored in this side is the one constructed from
its physical rows and paid moving recipe. -/
@[simp] theorem literalPassiveSideNormalization_calibration :
    ∀ analytic hanalytic,
      (produced analytic hanalytic).calibration = calibration := by
  intro analytic hanalytic
  cases side <;> rfl

private theorem literalPassiveSideNormalization_amplitude_raw (z : ℝ × ℝ) :
    ∀ analytic hanalytic,
      (produced analytic hanalytic).amplitude (WithLp.toLp 2 z) =
        polynomialProfileRadius
          (CanonicalFullKappaPrime.enlargedCoefficient rawCoefficient
            (CanonicalFullKappaPrime.radiusFactor K f.source.base δ mesh
              (CanonicalHeckePrimeAnalytic.degreeBound K) analyticHeight
              (CompleteMovingRowRecipe.primeMaskLogBound A f.source.base
                (geometry.literalRowParameter capacityCutoff +
                  geometry.literalSupportParameter rootLength))))
          (orders.sup Prod.snd) (orders.sup Prod.snd) z := by
  intro analytic hanalytic
  cases side <;> rfl

/-- The actual analytic enlargement uses the original total parameter
`m + q`; the extra passive divisor is kept in the allocation scalar. -/
@[simp] theorem literalPassiveSideNormalization_amplitude (z : ℝ × ℝ) :
    ∀ analytic hanalytic,
      (produced analytic hanalytic).amplitude (WithLp.toLp 2 z) =
        polynomialProfileRadius
          (CanonicalFullKappaPrime.enlargedCoefficient rawCoefficient enlargement)
          (orders.sup Prod.snd) (orders.sup Prod.snd) z := by
  intro analytic hanalytic
  rw [literalPassiveSideNormalization_amplitude_raw]
  rw [rowParameter, supportParameter]

/-- This is the radius of the same capacity used to choose the child.
No new normalization is selected on the active carrier. -/
@[simp] theorem literalPassiveSideNormalization_radius (z : ℝ × ℝ) :
    ∀ analytic hanalytic,
      (produced analytic hanalytic).normalizedCapacityData.radius (WithLp.toLp 2 z) =
        polynomialProfileRadius
          (CanonicalFullKappaPrime.enlargedCoefficient rawCoefficient enlargement)
          (orders.sup Prod.snd) (orders.sup Prod.snd) z := by
  intro analytic hanalytic
  change (produced analytic hanalytic).amplitude (WithLp.toLp 2 z) = _
  rw [literalPassiveSideNormalization_amplitude]

@[simp] theorem literalPassiveSideNormalization_primeBound
    (i : Fin f.source.allocation.keep.card) :
    ∀ analytic hanalytic,
      (produced analytic hanalytic).normalizedCapacityData.primeBound i = 1 := by
  intro analytic hanalytic
  cases side <;> rfl

/-- The error fallback belongs only to the raw scale ledger; it does
not replace the already computed profile coefficient above. -/
@[simp] theorem literalPassiveSideNormalization_rawClipError :
    ∀ analytic hanalytic,
      (produced analytic hanalytic).capacity.rawClipError =
        t.computedRawError geometry.skeleton.rawDegree error rectangle := by
  intro analytic hanalytic
  cases side <;> rfl

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalPassiveSideNormalization_calibration
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalPassiveSideNormalization_amplitude
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalPassiveSideNormalization_radius
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalPassiveSideNormalization_primeBound
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalPassiveSideNormalization_rawClipError
