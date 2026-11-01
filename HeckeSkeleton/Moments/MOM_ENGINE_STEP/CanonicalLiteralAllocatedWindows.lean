import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRowSectors
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActiveSecondWindows

/-!
# Physical row windows for the same literal allocated data

The original second physical cutoff and full-column norm windows pay
for the complete appended moving list. The support includes all old
moving factors, the three original fixed phases, the full first
support deletion, the active second factor and its complete sixth root.

Both calibration fields are conclusions: the allowed-row predicate and
the original-frequency cutoff. The sole width identity identifies the
actual two numeric coordinates with their original ledger formula; no
source or child estimate is an input. The second theorem transports
these conclusions to the same correlation-supported ordinary rows,
without reselecting their pattern, sector or arithmetic extraction.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support CommonSupportMass
open CanonicalLiteralAllocatedData

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset α} {right : Finset β}
variable {profiles : α → β → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)
variable (hclass : chart.NonunitLabelStable)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
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
variable (m q : ℝ)
variable (hwidth : m + q =
  secondCommonChildWidth d.base a₀ oldq wo (Real.log retainedScale / Real.log d.base) g
    (primePowerProduct b.primes b.leftMultiplicity).val
    (primePowerProduct b.primes b.rightMultiplicity).val
    (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity
      (chart.originalNonunitPattern ∅ X hX label)).val
    (secondPatternNonunitIdeal b.primes (chart.originalNonunitPattern ∅ X hX label)).val +
    idealLogLength d.base (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
    cutoffExponent)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

local notation "S" => chart.actualRows ∅ X hX label
local notation "pattern" => chart.originalNonunitPattern ∅ X hX label
local notation "child" => data P Rchar W B F parent oldMoving correction hcorr C b.primes
  b.leftMultiplicity b.rightMultiplicity pattern ν remaining extra m q inverse index
  rectangle firstSign negative

include hclass hradius hcutoff hproduct hold hwidth in
/-- The full actual mask is paid by the original physical row. The
ordinary frequency cutoff follows by its exact extraction norm and
the fact that a nonzero ideal's norm is at least one. -/
theorem literalAllocated_active_allowed_cutoff
    (h : (chart.actualRows ∅ X hX label).live) (ξ : WithLp 2 (ℝ × ℝ)) :
    (child ξ).allowedRow ((S).extractedRow C h).momentIdeal ∧
      A.exteriorNorm ((S).originalIdeal h.val) ≤
        (S).normFactor C h.val * d.base ^ (m + q) := by
  have hjoint := chart.actualRows_appended_active_pair_fullDeletion_joint_window hclass
    (F.moving P Rchar oldMoving) (remaining * extra) X hX label
    retainedScale d.base g a₀ oldq wo cutoffExponent hscale d.base_gt_one
    hradius hcutoff hproduct hold h
  dsimp only at hjoint
  rw [← hwidth] at hjoint
  have hallowed : (child ξ).allowedRow ((S).extractedRow C h).momentIdeal :=
    ⟨(HeckeAxiom.exteriorEquiv A ((S).extractedRow C h).ideal).property, hjoint⟩
  refine ⟨hallowed, ?_⟩
  let moving := (F.moving P Rchar oldMoving).appendSecondFactor C b.primes
    b.leftMultiplicity b.rightMultiplicity pattern
  let rem := remainingMaskIdeal A (remaining * extra) *
    secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity
  have hnorm : idealNorm K ((S).extractedRow C h).momentIdeal ≤ d.base ^ (m + q) := by
    calc
      _ ≤ idealNorm K ((S).extractedRow C h).momentIdeal *
          idealNorm K (moving.fullMaskSupport rem) := by
        exact le_mul_of_one_le_right (idealNorm_pos K _).le (one_le_idealNorm K _)
      _ ≤ _ := hjoint
  rw [((S).extractedRow C h).norm_factor]
  exact mul_le_mul_of_nonneg_left hnorm ((S).extractedRow C h).factor_pos.le

include hclass hradius hcutoff hproduct hold hwidth in
/-- The row updates in the real rectangle source do not alter its
original arithmetic ideal, norm factor or extracted moment ideal. -/
theorem literalAllocated_active_reweighted_allowed_cutoff
    (weight : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → ℂ)
    (keep₁ keep₂ : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)
    (h : ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁)
      .restrictRows keep₂).live) (ξ : WithLp 2 (ℝ × ℝ)) :
    let R₀ := (({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁)
      .restrictRows keep₂
    (data P Rchar W B F parent oldMoving correction hcorr C R₀.primes R₀.leftMultiplicity
      R₀.rightMultiplicity pattern ν remaining extra m q inverse index rectangle firstSign
      negative ξ).allowedRow (R₀.extractedRow C h).momentIdeal ∧
      A.exteriorNorm (R₀.originalIdeal h.val) ≤
        R₀.normFactor C h.val * d.base ^ (m + q) := by
  let R₁ := { chart.actualRows ∅ X hX label with weight := weight }
  let R₂ := R₁.restrictRows keep₁
  let h₁ : R₂.live := R₂.liveInclusion keep₂ h
  let h₀ : (chart.actualRows ∅ X hX label).live := R₁.liveInclusion keep₁ h₁
  exact chart.literalAllocated_active_allowed_cutoff hclass P Rchar W B F parent oldMoving
    correction hcorr remaining extra X hX label retainedScale g a₀ oldq wo cutoffExponent
    hscale hradius hcutoff hproduct hold m q hwidth ν inverse index rectangle firstSign
    negative h₀ ξ

include hclass hradius hcutoff hleft hright hold hwidth in
/-- Compatibility with the original all-column interface. The sharp
constructor above additionally covers centered zero cross-columns. -/
theorem literalAllocated_allowed_cutoff
    (h : (chart.actualRows ∅ X hX label).live) (ξ : WithLp 2 (ℝ × ℝ)) :
    (child ξ).allowedRow ((S).extractedRow C h).momentIdeal ∧
      A.exteriorNorm ((S).originalIdeal h.val) ≤
        (S).normFactor C h.val * d.base ^ (m + q) := by
  apply chart.literalAllocated_active_allowed_cutoff hclass P Rchar W B F parent oldMoving
    correction hcorr remaining extra X hX label retainedScale g a₀ oldq wo cutoffExponent
    hscale hradius hcutoff _ hold m q hwidth ν inverse index rectangle firstSign negative h ξ
  intro i hi j hj _
  rw [map_mul, Nat.cast_mul]
  exact (mul_le_mul (hleft i hi) (hright j hj) (Nat.cast_nonneg _)
    (Real.rpow_nonneg (zero_lt_one.trans d.base_gt_one).le _)).trans_eq
      (by rw [← Real.rpow_add (zero_lt_one.trans d.base_gt_one)]; congr 1; ring)

include hclass hradius hcutoff hleft hright hold hwidth in
/-- The former reweighted interface is the same all-column special
case, with the identical source row and data projections. -/
theorem literalAllocated_reweighted_allowed_cutoff
    (weight : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → ℂ)
    (keep₁ keep₂ : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)
    (h : ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁)
      .restrictRows keep₂).live) (ξ : WithLp 2 (ℝ × ℝ)) :
    let R₀ := (({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁)
      .restrictRows keep₂
    (data P Rchar W B F parent oldMoving correction hcorr C R₀.primes R₀.leftMultiplicity
      R₀.rightMultiplicity pattern ν remaining extra m q inverse index rectangle firstSign
      negative ξ).allowedRow (R₀.extractedRow C h).momentIdeal ∧
      A.exteriorNorm (R₀.originalIdeal h.val) ≤
        R₀.normFactor C h.val * d.base ^ (m + q) := by
  let R₁ := { chart.actualRows ∅ X hX label with weight := weight }
  let R₂ := R₁.restrictRows keep₁
  let h₁ : R₂.live := R₂.liveInclusion keep₂ h
  let h₀ : (chart.actualRows ∅ X hX label).live := R₁.liveInclusion keep₁ h₁
  exact chart.literalAllocated_allowed_cutoff hclass P Rchar W B F parent oldMoving
    correction hcorr remaining extra X hX label retainedScale g a₀ oldq wo cutoffExponent
    hscale hradius hcutoff hleft hright hold m q hwidth ν inverse index rectangle firstSign
    negative h₀ ξ

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalAllocated_allowed_cutoff
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalAllocated_reweighted_allowed_cutoff
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.literalAllocated_active_reweighted_allowed_cutoff
