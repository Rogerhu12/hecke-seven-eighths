import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrozenBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRowCharacters

/-!
# Full calibration of an actual literal rectangle frame

The original chart fixes the physical rows, nonunit pattern and residual
sector. Its two row restrictions and its common-atom weight are retained
literally. The allocated Fourier data are computed from the individual
profile table and the same allocation used by the frame.

All calibration conclusions are proved here: single-atom arithmetic,
the effective supports, the three Fourier profile identities, the full
allowed-row window, the frequency cutoff and the row, scalar and fibre
bounds. The common-row atom dictionary and profile/support certificates
are the previously constructed intermediate objects, not new aggregate
assumptions on a source or a child. The only character condition beyond
the original slot membership is the original background's principal-row
compatibility with the unchanged theta set.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralAllocatedData

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

def SecondColumnSide.literalNegative : SecondColumnSide → Bool
  | .left => false
  | .right => true

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
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (hcharacters : d.characters = CanonicalLiteralPhaseCalibration.sourceCharacters
  P Rchar F parent oldMoving correction remaining extra index)
variable (firstSupport : Finset (Ideal (𝓞 K)))
variable (hfirst : ∀ p ∈ firstSupport, Prime p)
variable (hextra : extra = literalDeletionIdeal firstSupport hfirst)
variable (support : d.SupportData ((primeSupport A.cS ∪ firstSupport) ∪
  primeSupport (primePowerProduct b.primes b.leftMultiplicity).val))
variable (retainedScale g a₀ oldq wo cutoffExponent : ℝ)
variable (hscale : 0 < retainedScale)
variable (hradius : radius = CanonicalRowBall.gaussRadius retainedScale d.base g hscale
  (zero_lt_one.trans d.base_gt_one))
variable (hcutoff : X ≤ d.base ^ cutoffExponent)
variable (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ d.base ^ a₀)
variable (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ d.base ^ a₀)
variable (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
  (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ d.base ^ (2 * a₀))
variable (hold : A.exteriorNorm ((F.moving P Rchar oldMoving).effectiveFullSupport
  (remaining * extra)) ≤ d.base ^ (oldq + wo))
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
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (rectangle : Bool)
variable (L : Ideal (𝓞 K)) (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)
variable (hL : Squarefree L)
variable (hselection : selection ∈ AllocationMass.idealAllocations L (k + 2))

local notation "S" =>
  (({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁)
    .restrictRows keep₂
local notation "pattern" => chart.originalNonunitPattern ∅ X hX label
local notation "sector" => chart.originalSector P ∅ X hX label
local notation "f" =>
  (d.factors S side χ ideal hideal firstSign rectangle).frame C L selection hne

/-- Internal assembly on the already calculated literal table and
common-row atoms. The actual source constructors supply those objects
from the original columns; no completed calibration is accepted. -/
def literalFrameFullCalibrationActive :
    ActualAllocatedSource.FullCalibration (f).source (σ := σ) ω ψ := by
  let B := (f).allocation
  let negative := side.literalNegative
  let newData := data P Rchar W B F parent oldMoving correction hcorr C (S).primes
    (S).leftMultiplicity (S).rightMultiplicity pattern sector remaining extra m q inverse index
    rectangle firstSign negative
  let params := parameters d B rectangle m q κ
  have hmask : d.characters.MaskIndicator := by
    rw [hcharacters]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator
      P Rchar F parent oldMoving correction remaining extra index
  let frozen := d.frozenBounds S C side χ ideal hideal firstSign rectangle L selection hne
    hmask hL hselection
  have hsupp (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) :=
    CanonicalLiteralAllocatedSupport.effectiveSupports_of_original_deletions
      P Rchar W B F parent oldMoving correction hcorr C (S).primes (S).leftMultiplicity
      (S).rightMultiplicity pattern sector remaining extra m q inverse index rectangle firstSign
      negative firstSupport hfirst hextra b.left_positive b.right_positive support
      rfl rfl rfl κ ξ u
  have hwindow (h : (S).live) (ξ : WithLp 2 (ℝ × ℝ)) :
      (newData ξ).allowedRow ((S).extractedRow C h).momentIdeal ∧
        A.exteriorNorm ((S).originalIdeal h.val) ≤ (S).normFactor C h.val * d.base ^ (m + q) :=
    chart.literalAllocated_active_reweighted_allowed_cutoff hclass P Rchar W B F parent oldMoving
      correction hcorr remaining extra X hX label retainedScale g a₀ oldq wo cutoffExponent
      hscale hradius hcutoff hproduct hold m q hwidth sector inverse index rectangle
      firstSign negative weight keep₁ keep₂ h ξ
  refine {
    data := newData
    parameters := params
    height := CanonicalLiteralAllocatedData.height
    count := fun _ => rfl
    lengths := ?_
    left_scale := ?_
    right_scale := ?_
    slot_sum := ?_
    dictionary := ?_
    left_support := ?_
    right_support := ?_
    slot_support := ?_
    left_profile := ?_
    right_profile := ?_
    slot_profile := ?_
    allowed := ?_
    cutoff := ?_
    rowBound := rowMass.rowBound
    rowBound_nonneg := rowMass.rowBound_nonneg
    row_bound := ?_
    scalarBound := frozen.scalarBound
    scalarBound_nonneg := frozen.scalarBound_nonneg
    scalar_bound := frozen.scalar_bound C
    fiberBound := rowMass.originalFiber
    fibers := ?_
    principal_in_theta := ?_
    slot_in_theta := ?_ }
  · intro ξ i
    cases side <;>
      exact W.fourierSlot_length (SlotRestriction.index B.keep i) firstSign _ ξ
  · cases side <;> exact CanonicalLiteralAllocatedData.left_scale d B rectangle m q κ
  · cases side <;> exact CanonicalLiteralAllocatedData.right_scale d B rectangle m q κ
  · cases side <;> rfl
  · intro ξ h
    let row := chart.originalReweightedPatternSector P hclass hsector ∅ X hX label
      weight keep₁ keep₂ h
    cases side with
    | left =>
      change (d.characters.restrictSlots B.keep).Calibration (σ := σ) (newData ξ) rfl
        ((S).extractedRow C h).momentIdeal ((S).factor C h.val) ((S).extractedRow C h).element
      rw [hcharacters]
      exact actualDictionary P Rchar W B F parent oldMoving correction hcorr C pattern sector
        remaining extra m q inverse index rectangle firstSign false S hone hroot hemb row ξ
    | right =>
      change (d.characters.restrictSlots B.keep).Calibration (σ := σ) (newData ξ) rfl
        ((S).extractedRow C h).momentIdeal (-((S).factor C h.val)) ((S).extractedRow C h).element
      rw [hcharacters]
      exact actualNegativeDictionary P Rchar W B F parent oldMoving correction hcorr C
        pattern sector remaining extra m q inverse index rectangle firstSign true
        S hone hroot hemb row ξ
  · intro ξ h _
    cases side <;> exact (hsupp ξ ((S).extractedRow C h).momentIdeal).1
  · intro ξ h _
    cases side <;> exact (hsupp ξ ((S).extractedRow C h).momentIdeal).2.1
  · intro ξ h _ i
    cases side <;> exact (hsupp ξ ((S).extractedRow C h).momentIdeal).2.2 i
  · intro ξ h _ I _
    cases side <;>
      exact CanonicalLiteralAllocatedData.left_profile W B firstSign _ rectangle m q κ ξ
        ((S).extractedRow C h).momentIdeal I
  · intro ξ h _ I _
    cases side <;>
      exact CanonicalLiteralAllocatedData.right_profile W B firstSign _ rectangle m q κ ξ
        ((S).extractedRow C h).momentIdeal I
  · intro ξ h _ i p _
    cases side <;>
      exact CanonicalLiteralAllocatedData.slot_profile W B firstSign _ ξ i p
  · intro ξ h _
    cases side <;> exact (hwindow h ξ).1
  · intro h _
    cases side <;> exact (hwindow h 0).2
  · intro h _
    rw [(f).source_row_weight]
    exact rowMass.row_bound h.val (Finset.mem_filter.mp h.property).1
  · intro I
    simpa only [(f).source_rows, (f).source_row_momentIdeal] using rowMass.extracted_fibers I
  · intro ξ u hp
    exact CanonicalLiteralAllocatedSupport.principal_in_theta
      P Rchar W B F parent oldMoving correction hcorr C (S).primes (S).leftMultiplicity
      (S).rightMultiplicity pattern sector remaining extra m q inverse index rectangle firstSign
      negative hbackground ξ u hp
  · intro ξ i
    exact CanonicalLiteralAllocatedSupport.slot_in_theta
      P Rchar W B F parent oldMoving correction hcorr C (S).primes (S).leftMultiplicity
      (S).rightMultiplicity pattern sector remaining extra m q inverse index rectangle firstSign
      negative hslot ξ i

/-- The original ordinary predicate is fixed by the raw character
recipe before this constructor. Its equality here is a finite-label
identity, not a nonexceptional-child hypothesis. The source row type,
its `univ` carrier and the original allocation remain unchanged. -/
def literalFrameCalibrationActive
    (keep₂_eq : keep₂ = fun h =>
      (chart.actualRows ∅ X hX label).literalCharacter C P Rchar F oldMoving correction
        pattern sector h ∉ parent.theta) :
    (f).source.Calibration (σ := σ) ω ψ := by
  let full := chart.literalFrameFullCalibrationActive P Rchar hclass hsector X hX label
    weight keep₁ keep₂ rowMass d W F parent oldMoving correction hcorr remaining extra index
    hcharacters firstSupport hfirst hextra support retainedScale g a₀ oldq wo cutoffExponent
    hscale hradius hcutoff hproduct hold m q κ hwidth inverse hone hroot hemb
    hbackground hslot side χ ideal hideal firstSign rectangle L selection hne hL hselection
  refine {
    data := full.data
    parameters := full.parameters
    height := full.height
    count := full.count
    lengths := full.lengths
    left_scale := full.left_scale
    right_scale := full.right_scale
    slot_sum := full.slot_sum
    dictionary := full.dictionary
    left_support := full.left_support
    right_support := full.right_support
    slot_support := full.slot_support
    left_profile := full.left_profile
    right_profile := full.right_profile
    slot_profile := full.slot_profile
    allowed := full.allowed
    cutoff := full.cutoff
    nonexceptional := ?_
    rowBound := full.rowBound
    rowBound_nonneg := full.rowBound_nonneg
    row_bound := full.row_bound
    scalarBound := full.scalarBound
    scalarBound_nonneg := full.scalarBound_nonneg
    scalar_bound := full.scalar_bound
    fiberBound := full.fiberBound
    fibers := full.fibers
    principal_in_theta := full.principal_in_theta
    slot_in_theta := full.slot_in_theta }
  intro ξ h _
  have hk : keep₂ h.val :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp h.property).1).2
  rw [keep₂_eq] at hk
  have he : (full.data ξ).rowCharacter ((f).source.row h).momentIdeal =
      (chart.actualRows ∅ X hX label).literalCharacter C P Rchar F oldMoving correction
        pattern sector h.val := by
    cases side <;>
      exact (chart.actualRows ∅ X hX label).literalCharacter_reweighted C P Rchar F oldMoving
        correction pattern sector weight keep₁ keep₂ h
  have hn : (full.data ξ).rowCharacter ((f).source.row h).momentIdeal ∉
      (full.data ξ).theta := by
    change (full.data ξ).rowCharacter ((f).source.row h).momentIdeal ∉ parent.theta
    rw [he]
    exact hk
  split_ifs
  · exact fun hp => hn (full.principal_in_theta ξ _ hp)
  · exact hn

/-- The original all-column interface is retained as a special case.
The produced data and all arithmetic fields are the same active-window
construction; only its proof of the physical bound is specialized. -/
def literalFrameFullCalibration :
    ActualAllocatedSource.FullCalibration (f).source (σ := σ) ω ψ := by
  have hp : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ d.base ^ (2 * a₀) := by
    intro i hi j hj _
    rw [map_mul, Nat.cast_mul]
    exact (mul_le_mul (hleft i hi) (hright j hj) (Nat.cast_nonneg _)
      (Real.rpow_nonneg (zero_lt_one.trans d.base_gt_one).le _)).trans_eq
        (by rw [← Real.rpow_add (zero_lt_one.trans d.base_gt_one)]; congr 1; ring)
  exact chart.literalFrameFullCalibrationActive P Rchar hclass hsector X hX label
    weight keep₁ keep₂ rowMass d W F parent oldMoving correction hcorr remaining extra index
    hcharacters firstSupport hfirst hextra support retainedScale g a₀ oldq wo cutoffExponent
    hscale hradius hcutoff hp hold m q κ hwidth inverse hone hroot hemb
    hbackground hslot side χ ideal hideal firstSign rectangle L selection hne hL hselection

/-- Compatibility with callers which already have the stronger
all-column window. The ordinary predicate and row set are unchanged. -/
def literalFrameCalibration
    (keep₂_eq : keep₂ = fun h =>
      (chart.actualRows ∅ X hX label).literalCharacter C P Rchar F oldMoving correction
        pattern sector h ∉ parent.theta) :
    (f).source.Calibration (σ := σ) ω ψ := by
  have hp : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ d.base ^ (2 * a₀) := by
    intro i hi j hj _
    rw [map_mul, Nat.cast_mul]
    exact (mul_le_mul (hleft i hi) (hright j hj) (Nat.cast_nonneg _)
      (Real.rpow_nonneg (zero_lt_one.trans d.base_gt_one).le _)).trans_eq
        (by rw [← Real.rpow_add (zero_lt_one.trans d.base_gt_one)]; congr 1; ring)
  exact chart.literalFrameCalibrationActive P Rchar hclass hsector X hX label
    weight keep₁ keep₂ rowMass d W F parent oldMoving correction hcorr remaining extra index
    hcharacters firstSupport hfirst hextra support retainedScale g a₀ oldq wo cutoffExponent
    hscale hradius hcutoff hp hold m q κ hwidth inverse hone hroot hemb
    hbackground hslot side χ ideal hideal firstSign rectangle L selection hne hL hselection
    keep₂_eq

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalFrameFullCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalFrameCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalFrameCalibrationActive
