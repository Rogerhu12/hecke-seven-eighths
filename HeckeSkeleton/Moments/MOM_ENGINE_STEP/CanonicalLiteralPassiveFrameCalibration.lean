import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidSupport

/-!
# The actual paid frame calibration after passive allocation

The data use the paid moving recipe and the original remaining ideal.
The passive mask is absent from their allowed-row budget and remains
in the preceding exact finite expansion. Each stored passive branch
supplies its own quotient profiles, retained slots and frozen scalar.
The original ordinary predicate is transported by equality of its
actual row character, including the pool sixth-power reduction.
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
variable (index : Fin k → Fin parent.geometry.slotCount)
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
local notation "idx" => (fun j => index (SlotRestriction.index B.keep j))
local notation "paid" => paidSourceCharacters P Rchar choice.phases parent oldMoving
  correction remaining idx
local notation "t" => table W B A paid
local notation "E" => CanonicalLiteralPassiveSource.profiles W B A paid
local notation "allocation" => branch W B A (choice.mask extra) a
local notation "f" => frame W B A paid C S side (choice.mask extra) a firstSign rectangle

/-- The paid support window is the one constructed from the original
old support, first active/divisor factors and reduced pool moving
factor. No passive ideal appears in this window. -/
def literalPassiveFrameFullCalibration :
    ActualAllocatedSource.FullCalibration (f).source (σ := σ) ω ψ := by
  let negative := side.literalNegative
  let newData := data P Rchar E allocation choice.phases parent oldMoving correction hcorr C
    (S).primes (S).leftMultiplicity (S).rightMultiplicity pattern sector remaining 1 m q inverse
    idx rectangle firstSign negative
  let params := parameters t allocation rectangle m q κ
  let frozen := CanonicalLiteralPassiveFrames.frozenBounds W B paid C S side
    (choice.mask extra) a firstSign rectangle
    (paidSourceCharacters_maskIndicator P Rchar choice.phases parent oldMoving correction
      remaining idx) ha
  have hsupp (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) :=
    CanonicalLiteralPassiveSupport.effectiveSupports
      (P := P) (R := Rchar) (W := W) (B := B) (paid := paid) (F := choice.phases)
      (parent := parent) (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
      (C := C) (p := (S).primes) (leftMultiplicity := (S).leftMultiplicity)
      (rightMultiplicity := (S).rightMultiplicity) (pattern := pattern) (ν := sector)
      (remaining := remaining) (m := m) (q := q) (inverse := inverse) (index := index)
      (rectangle := rectangle) (firstSign := firstSign) (negative := negative)
      (M := choice.mask extra) (a := a) κ ξ u
  have hpaid : A.exteriorNorm ((choice.phases.moving P Rchar oldMoving).effectiveFullSupport
      (remaining * 1)) ≤ (t).base ^ (oldq + wo) := by
    simpa only [mul_one] using hpaidSupport
  have hwindow (h : (S).live) (ξ : WithLp 2 (ℝ × ℝ)) :
      (newData ξ).allowedRow ((S).extractedRow C h).momentIdeal ∧
        A.exteriorNorm ((S).originalIdeal h.val) ≤ (S).normFactor C h.val * d.base ^ (m + q) :=
    chart.literalAllocated_active_reweighted_allowed_cutoff hclass P Rchar E allocation
      choice.phases parent oldMoving correction hcorr remaining 1 X hX label
      retainedScale g a₀ oldq wo cutoffExponent hscale hradius hcutoff hproduct hpaid m q
      hwidth sector inverse idx rectangle firstSign negative weight keep₁ keep₂ h ξ
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
    cases side <;> exact (E).fourierSlot_length
      (SlotRestriction.index (allocation).keep i) firstSign _ ξ
  · cases side <;> exact CanonicalLiteralAllocatedData.left_scale t allocation rectangle m q κ
  · cases side <;> exact CanonicalLiteralAllocatedData.right_scale t allocation rectangle m q κ
  · cases side <;> rfl
  · intro ξ h
    let row := chart.originalReweightedPatternSector P hclass hsector ∅ X hX label
      weight keep₁ keep₂ h
    cases side <;>
      exact actualPaidDictionary P Rchar choice.phases parent oldMoving correction remaining idx
        E allocation hcorr C S pattern sector m q inverse rectangle firstSign _
        hone hroot hemb row ξ
  · intro ξ h _
    cases side <;> exact (hsupp ξ ((S).extractedRow C h).momentIdeal).1
  · intro ξ h _
    cases side <;> exact (hsupp ξ ((S).extractedRow C h).momentIdeal).2.1
  · intro ξ h _ i
    cases side <;> exact (hsupp ξ ((S).extractedRow C h).momentIdeal).2.2 i
  · intro ξ h _ I _
    cases side <;> exact CanonicalLiteralAllocatedData.left_profile E allocation firstSign _
      rectangle m q κ ξ ((S).extractedRow C h).momentIdeal I
  · intro ξ h _ I _
    cases side <;> exact CanonicalLiteralAllocatedData.right_profile E allocation firstSign _
      rectangle m q κ ξ ((S).extractedRow C h).momentIdeal I
  · intro ξ h _ i p _
    cases side <;> exact CanonicalLiteralAllocatedData.slot_profile E allocation firstSign _ ξ i p
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
    exact CanonicalLiteralAllocatedSupport.principal_in_theta P Rchar E allocation choice.phases
      parent oldMoving correction hcorr C (S).primes (S).leftMultiplicity (S).rightMultiplicity
      pattern sector remaining 1 m q inverse idx rectangle firstSign negative hbackground ξ u hp
  · intro ξ i
    exact CanonicalLiteralAllocatedSupport.slot_in_theta P Rchar E allocation choice.phases
      parent oldMoving correction hcorr C (S).primes (S).leftMultiplicity (S).rightMultiplicity
      pattern sector remaining 1 m q inverse idx rectangle firstSign negative hslot ξ i

/-- The original ordinary filter supplies nonexceptionality for every
new passive allocation. Sixth-power reduction does not change it. -/
def literalPassiveFrameCalibration
    (keep₂_eq : keep₂ = fun h =>
      (chart.actualRows ∅ X hX label).literalCharacter C P Rchar F oldMoving correction
        pattern sector h ∉ parent.theta) :
    (f).source.Calibration (σ := σ) ω ψ := by
  let full := chart.literalPassiveFrameFullCalibration P Rchar hclass hsector X hX label
    weight keep₁ keep₂ rowMass d W B F choice parent oldMoving correction hcorr remaining extra
    index a ha retainedScale g a₀ oldq wo cutoffExponent hscale hradius hcutoff hproduct
    hpaidSupport m q κ hwidth inverse hone hroot hemb hbackground hslot side firstSign rectangle
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
    have hp := (chart.actualRows ∅ X hX label).literalCharacter_reweighted C P Rchar
      choice.phases oldMoving correction pattern sector weight keep₁ keep₂ h
    have hc := choice.literalCharacter_eq P Rchar (chart.actualRows ∅ X hX label)
      oldMoving correction pattern sector h.val
    cases side <;> exact hp.trans hc.symm
  have hn : (full.data ξ).rowCharacter ((f).source.row h).momentIdeal ∉
      (full.data ξ).theta := by
    change (full.data ξ).rowCharacter ((f).source.row h).momentIdeal ∉ parent.theta
    rw [he]
    exact hk
  split_ifs
  · exact fun hp => hn (full.principal_in_theta ξ _ hp)
  · exact hn

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalPassiveFrameFullCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalPassiveFrameCalibration
