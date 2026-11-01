import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveFrameCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveFrameIdentity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocationProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSideProductionAll

/-!
# The actual passive side constructs its normalized capacity data

The physical chart supplies the original ordinary rows. Its paid
calibration is built here for the stored passive allocation. The
original computed profile representatives are transported to the full
smooth table, then the existing full-kappa producer constructs both
raw and clipped windows on this exact quotient branch.

The original occurrence dictionary is restricted by the two actual
keep maps. The same nominal geometry constructs the capacity input;
no child, profile window, source inequality or final capacity bound is
an additional input. The final arguments are the individual analytic
certificates for the characters of the newly constructed data.
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

/-- This producer calls the actual paid calibration, then the original
full-kappa and sixth-root capacity producers. Its final two arguments
concern only the actual individual characters and their analytic
heights, including the branch κ=1 handled internally. -/
def literalPassiveSideNormalization :=
  let cal := chart.literalPassiveFrameCalibration P Rchar hclass hsector X hX label
    weight keep₁ keep₂ rowMass d W B F choice parent oldMoving correction hcorr remaining extra
    slots.index a ha retainedScale g a₀ oldq wo cutoffExponent hscale hradius hcutoff hproduct
    hpaidSupport m q κ hwidth inverse hone hroot hemb hbackground hslot side firstSign rectangle
    keep₂_eq
  let originalSlots := tableOriginalSlots W B A paid parent slots
  let profiles := computed.passiveTable B A paid
  have hdata : ∀ ξ, cal.data ξ = CanonicalLiteralAllocatedData.data P Rchar E (f).allocation
      choice.phases parent oldMoving correction hcorr C (S).primes (S).leftMultiplicity
      (S).rightMultiplicity pattern sector remaining 1
      (geometry.literalRowParameter capacityCutoff)
      (geometry.literalSupportParameter (idealLogLength (f).source.base
        (secondSixthRootIdeal (S).primes (side.literalMultiplicity S)
          (side.literalOppositeMultiplicity S)).val))
      (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
      originalSlots.index rectangle firstSign side.literalNegative ξ := by
    intro ξ
    rw [rowParameter, supportParameter]
    rw [← inverse_eq]
    rfl
  have hparameters : cal.parameters = CanonicalLiteralAllocatedData.parameters t (f).allocation
      rectangle (geometry.literalRowParameter capacityCutoff)
      (geometry.literalSupportParameter (idealLogLength (f).source.base
        (secondSixthRootIdeal (S).primes (side.literalMultiplicity S)
          (side.literalOppositeMultiplicity S)).val)) parentParameters.κ := by
    rw [rowParameter, supportParameter, ← kappa]
    rfl
  fun analytic hanalytic =>
    show SecondSideNormalization f ω ψ Set.univ Set.univ (Set.Icc 0 hi) orders from
      (t).produceLiteralSideAll E S side (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
        (columnExterior W B A) (columnExterior_val_of_mem W B A) firstSign rectangle
        a.val.1 a.val.2 ((Finset.mem_filter.mp a.property).2) cal
        P Rchar choice.phases parent oldMoving correction hcorr remaining 1
        parentParameters step geometry pattern sector originalSlots capacityCutoff reference time
        hdata hparameters domain direct hcapacityCutoff hsmall error herr
        b.left_positive b.right_positive hsecond hopposite hunit hstep mesh hmesh hfit
        lo hi hlo hhi orders original hreference htime horders profiles hprimeOrders
        δ analyticHeight hδ hδhi analytic hanalytic

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalPassiveSideNormalization
