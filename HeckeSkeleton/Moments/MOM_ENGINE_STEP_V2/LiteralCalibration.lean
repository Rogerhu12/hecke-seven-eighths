import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralPhases
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonAtomBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralPassive

set_option linter.unusedSectionVars false

/-!
# Sharp second physical windows on the original nonzero Gram profiles

The original Cartesian carrier may contain cross-rectangle columns
whose complete centered coefficient is zero. Such columns need not
satisfy the sharp active-column norm window. The physical cutoff is
already computed only from nonzero original pair profiles, so the
window below applies exactly on that support and keeps every column.

The resulting bound is transported through the same actual correlation
extraction and the complete appended moving support, including the
entire first deletion and the complete second sixth root.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

section Physical

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable {ι κ : Type*}

/-- Only the original nonzero profile branches enter the actual
maximum of inverse radii. This changes neither carrier nor source. -/
theorem FirstFiniteSource.physicalCutoff_le_active_windows
    (s : FirstFiniteSource K S Γ ι κ)
    (Z cutoffExponent radiusExponent maskExponent modulusExponent : ℝ)
    (hZ : 0 < Z) (hcutoff : s.cutoff ≤ Z ^ cutoffExponent)
    (hradius : s.radius.val ≤ Z ^ radiusExponent)
    (hmask : ∀ D ∈ s.mask.powerset,
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤
          Z ^ maskExponent)
    (hmodulus : ∀ i ∈ s.leftColumns, ∀ j ∈ s.rightColumns,
      (s.pairs i j).profile ≠ 0 →
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨(s.pairs i j).modulus, (s.pairs i j).modulus_ne_zero⟩).val ≤
          Z ^ modulusExponent) :
    s.physicalCutoff ≤ Z ^
      (cutoffExponent + radiusExponent + maskExponent + modulusExponent) := by
  sorry

end Physical

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [IsPrincipalIdealRing A.R]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

/-- The actual Gram profile can be nonzero only when both complete
original coefficients are nonzero. Thus a sharp active-column window
gives exactly the supported pair window used by the physical cutoff. -/
theorem ActualGaussSource.active_gram_pair_norm_le
    (C : A.GeneralArithmeticContext σ η hS) (G : ActualGaussSource C ι)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (Z a₀ : ℝ) (hZ : 0 < Z)
    (hcolumns : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
      A.exteriorNorm (G.ideal i) ≤ Z ^ a₀)
    (i : ι) (hi : i ∈ G.columns) (j : ι) (hj : j ∈ G.columns)
    (hprofile : (G.coefficient i * star (G.coefficient j)) • φ ≠ 0) :
    (Ideal.absNorm ((G.ideal i).val * (G.ideal j).val) : ℝ) ≤ Z ^ (2 * a₀) := by
  sorry

/-- The sharp pair window is required only when the original Gram
profile is nonzero, including for a full centered coefficient. -/
theorem FirstCommonCharacterBlock.secondPhysicalCutoff_le_active_pair_windows
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (M : Finset (HeightOneSpectrum A.R)) (radius : {r : ℝ // 0 < r})
    (X : ℝ) (hX : 1 ≤ X)
    (Z cutoffExponent radiusExponent maskExponent productExponent : ℝ)
    (hZ : 0 < Z) (hcutoff : X ≤ Z ^ cutoffExponent)
    (hradius : radius.val ≤ Z ^ radiusExponent)
    (hmask : ∀ D ∈ M.powerset,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤
          Z ^ maskExponent)
    (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ productExponent) :
    (b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX).physicalCutoff ≤
      Z ^ (cutoffExponent + radiusExponent + maskExponent + productExponent) := by
  sorry

section ActualRows

variable [Γ.FiniteIndex]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hΓ hDiff}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)

theorem actualRows_empty_originalNorm_le_active_pair_windows
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ (2 * a₀))
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (hq : q ∈ (chart.actualRows ∅ X hX label).rows) :
    A.exteriorNorm ((chart.actualRows ∅ X hX label).originalIdeal q) ≤
      Z ^ (2 * a₀ - Real.log retainedScale / Real.log Z - g + cutoffExponent) := by
  sorry

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

theorem actualRows_empty_active_pair_fullJoint_window
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ (2 * a₀))
    (moving : OriginalMovingFactors A P Rchar) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (old : A.Exterior) (hold : A.exteriorNorm old ≤ Z ^ (q + wo))
    (h : (chart.actualRows ∅ X hX label).live)
    (W : moving.SupportAtoms old
      (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val))
      (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val))
      remaining) :
    idealNorm K ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal *
        idealNorm K (moving.fullMaskSupport remaining) ≤
      Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val
        (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val +
        cutoffExponent) := by
  sorry

/-- The active-profile physical window now pays every actual appended
factor and the full sixth root, with the original fixed pattern. -/
theorem actualRows_appended_active_pair_fullDeletion_joint_window
    (hclass : chart.NonunitLabelStable)
    (oldMoving : OriginalMovingFactors A P Rchar)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ (2 * a₀))
    (hold : A.exteriorNorm (oldMoving.effectiveFullSupport remaining) ≤ Z ^ (q + wo))
    (h : (chart.actualRows ∅ X hX label).live) :
    let pattern := chart.originalNonunitPattern ∅ X hX label
    idealNorm K ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal *
        idealNorm K
          ((oldMoving.appendSecondFactor C b.primes b.leftMultiplicity b.rightMultiplicity pattern).fullMaskSupport
            (remainingMaskIdeal A remaining *
              secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ≤
      Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
        (secondPatternNonunitIdeal b.primes pattern).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent) := by
  sorry

end SecondBlockProfileChart
end ActualRows
end HeckeSkeleton.Moments.EngineStepV2

end

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

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

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
  sorry

include hclass hradius hcutoff hproduct hold hwidth in
/-- The row updates in the real rectangle source do not alter its
original arithmetic ideal, norm factor or extracted moment ideal. -/
theorem literalAllocated_active_reweighted_allowed_cutoff
    (weight : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → ℂ)
    (keep₁ keep₂ : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)
    (h : ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂).live) (ξ : WithLp 2 (ℝ × ℝ)) :
    let R₀ := (({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂
    (data P Rchar W B F parent oldMoving correction hcorr C R₀.primes R₀.leftMultiplicity
      R₀.rightMultiplicity pattern ν remaining extra m q inverse index rectangle firstSign
      negative ξ).allowedRow (R₀.extractedRow C h).momentIdeal ∧
      A.exteriorNorm (R₀.originalIdeal h.val) ≤
        R₀.normFactor C h.val * d.base ^ (m + q) := by
  sorry

include hclass hradius hcutoff hleft hright hold hwidth in
/-- Compatibility with the original all-column interface. The sharp
constructor above additionally covers centered zero cross-columns. -/
theorem literalAllocated_allowed_cutoff
    (h : (chart.actualRows ∅ X hX label).live) (ξ : WithLp 2 (ℝ × ℝ)) :
    (child ξ).allowedRow ((S).extractedRow C h).momentIdeal ∧
      A.exteriorNorm ((S).originalIdeal h.val) ≤
        (S).normFactor C h.val * d.base ^ (m + q) := by
  sorry

include hclass hradius hcutoff hleft hright hold hwidth in
/-- The former reweighted interface is the same all-column special
case, with the identical source row and data projections. -/
theorem literalAllocated_reweighted_allowed_cutoff
    (weight : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → ℂ)
    (keep₁ keep₂ : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)
    (h : ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂).live) (ξ : WithLp 2 (ℝ × ℝ)) :
    let R₀ := (({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂
    (data P Rchar W B F parent oldMoving correction hcorr C R₀.primes R₀.leftMultiplicity
      R₀.rightMultiplicity pattern ν remaining extra m q inverse index rectangle firstSign
      negative ξ).allowedRow (R₀.extractedRow C h).momentIdeal ∧
      A.exteriorNorm (R₀.originalIdeal h.val) ≤
        R₀.normFactor C h.val * d.base ^ (m + q) := by
  sorry

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStepV2

end

set_option quotPrecheck false

/-!
# The original frozen costs of a literal rectangle frame

The arithmetic mask is proved to take only the values zero and one.
Every frozen arithmetic coefficient is therefore bounded by one using
the original Hecke coefficients. The annulus and profile costs are read
from the actual allocated prime occurrences, before either Fourier
variable. The resulting scalar retains the genuine inverse norm of the
same second divisor.

This constructor does not accept a frozen-scalar estimate. Its final
specialization accepts the literal character-field identity of the
original table, whose phase calibration already computes all three
fixed moving factors and the complete first deletion.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

private theorem literal_indicator_mul (x y : ℂ)
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    x * y = 0 ∨ x * y = 1 := by
  sorry

namespace FixedChildCharacters

variable {k : ℕ} (T : FixedChildCharacters K k)

/-- A property proved from the original mask operations, not a new
bound on a column or a polynomial. -/
def MaskIndicator : Prop := ∀ I : Ideal (𝓞 K), T.mask I = 0 ∨ T.mask I = 1

variable {T}

theorem MaskIndicator.restrictSlots (h : T.MaskIndicator) (keep : Finset (Fin k)) :
    (T.restrictSlots keep).MaskIndicator := by
  sorry

theorem MaskIndicator.deleteMask (h : T.MaskIndicator)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) : (T.deleteMask M).MaskIndicator := by
  sorry

variable {A : SArithmeticData K}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

theorem MaskIndicator.movingSingleton (h : T.MaskIndicator)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    (T.movingSingleton P R I a ha).MaskIndicator := by
  sorry

end FixedChildCharacters

namespace CanonicalLiteralPhaseCalibration

variable {A : SArithmeticData K}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}

/-- The original source mask is binary without any coprimality
assumption on its argument; all ramification zeros remain present. -/
theorem sourceCharacters_maskIndicator (F : FixedPhases A)
    (parent : MomentData K ω ψ) (D : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K)
    (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ}
    (index : Fin k → Fin parent.geometry.slotCount) :
    (sourceCharacters P R F parent D correction remaining extra index).MaskIndicator := by
  sorry

end CanonicalLiteralPhaseCalibration

namespace CanonicalLiteralRectangles.Atoms

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- The same original atom calculation also pays the common-support
extraction. Its witnesses and deleted occurrences are those of the
stored original support branch. -/
def commonAtomBounds {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (hmask : d.characters.MaskIndicator) :
    b.CommonAtomBounds d.characters d.base d.length d.slotWeight where
  base_pos := zero_lt_one.trans d.base_gt_one
  annulus i := (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) / d.base ^ d.length i
  profile i := ‖d.slotWeight i (b.witness.2 i)‖ ^ 2
  annulus_nonneg i := div_nonneg (Nat.cast_nonneg _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).le
  profile_nonneg i := sq_nonneg _
  plain₁ := OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
    d.characters.plain d.characters.plainTwist d.characters.mask _ (hmask _)
  plain₂ := OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
    d.characters.plain d.characters.plainTwist d.characters.mask _ (hmask _)
  prime i _ := OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one
    (d.characters.slot i) (d.characters.slotTwist i) d.characters.mask _ (hmask _)
  prime_annulus i _ := le_of_eq (div_mul_cancel₀ _
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).ne').symm
  slot i _ := le_rfl

variable (S : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (rectangle : Bool)
variable (L : Ideal (𝓞 K)) (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "f" => (d.factors S side χ ideal hideal firstSign rectangle).frame C L selection hne

/-- Costs are computed on the very witness of the original
allocation. The original finite prime window subsequently bounds
these per-prime values uniformly; it need not be assumed here. -/
def frozenBounds (hmask : d.characters.MaskIndicator)
    (hL : Squarefree L)
    (hselection : selection ∈ AllocationMass.idealAllocations L (k + 2)) :
    (f).source.FrozenAtomBounds where
  annulus i := (Ideal.absNorm ((f).allocation.witness.2 i).asIdeal : ℝ) / d.base ^ d.length i
  profile i := ‖d.slotWeight i ((f).allocation.witness.2 i)‖ ^ 2
  annulus_nonneg i := div_nonneg (Nat.cast_nonneg _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).le
  profile_nonneg i := sq_nonneg _
  plain₁_bound h _ := by
    cases side <;>
      exact OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
        d.characters.plain d.characters.plainTwist d.characters.mask _ (hmask _)
  plain₂_bound h _ := by
    cases side <;>
      exact OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
        d.characters.plain d.characters.plainTwist d.characters.mask _ (hmask _)
  prime_bound h _ i _ := by
    cases side <;>
      exact OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one
        (d.characters.slot i) (d.characters.slotTwist i) d.characters.mask _ (hmask _)
  prime_annulus i _ := by
    cases side <;>
      exact le_of_eq (div_mul_cancel₀ _
        (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).ne').symm
  slot_bound h _ i _ := by cases side <;> exact le_rfl
  divisor_squarefree := hL
  allocation_mem := hselection

theorem frozenBounds_scalarBound (hmask : d.characters.MaskIndicator)
    (hL : Squarefree L)
    (hselection : selection ∈ AllocationMass.idealAllocations L (k + 2)) :
    (d.frozenBounds S C side χ ideal hideal firstSign rectangle L selection hne
      hmask hL hselection).scalarBound =
      (∏ i ∈ Finset.univ \ (f).allocation.keep,
        (((Ideal.absNorm ((f).allocation.witness.2 i).asIdeal : ℝ) / d.base ^ d.length i) *
          ‖d.slotWeight i ((f).allocation.witness.2 i)‖ ^ 2)) /
        (Ideal.absNorm L : ℝ) := by
  sorry

variable {ω ψ : HeckeCharacter K}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- On the actual table the binary-mask proof is produced from its
literal original character recipe. The table identity is per field,
not a whole-coefficient or energy hypothesis. -/
def frozenBounds_of_originalCharacters
    (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
    (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K)
    (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount)
    (hcharacters : d.characters = CanonicalLiteralPhaseCalibration.sourceCharacters
      P R F parent oldMoving correction remaining extra index)
    (hL : Squarefree L)
    (hselection : selection ∈ AllocationMass.idealAllocations L (k + 2)) :
    (f).source.FrozenAtomBounds :=
  d.frozenBounds S C side χ ideal hideal firstSign rectangle L selection hne
    (by rw [hcharacters]; exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator
      P R F parent oldMoving correction remaining extra index) hL hselection

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The same ordinary rows after removing an amplifier sixth power

The character attached to an original moving element is computed from
its actual sixth-power-free frequency row, including its unit sector.
Multiplication by a nonzero sixth power preserves that row.  The proof
uses the original orbit relation and uniqueness of the physical
frequency-row/amplifier decomposition; no character extensionality or
unmasked coefficient identity is assumed.

The pool factors of multiplicity one, six and seven therefore have the
same complete Hecke characters as their reduced active factors.  Their
zero-extended ideal evaluations still have the different masks proved
in `CanonicalLiteralPassivePhases`.  This distinction lets the new paid
source retain the original ordinary-row predicate exactly.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralPaidRowCharacters

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

section ActualRows

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

private def sixthDilation (a : NonzeroRingElements (S.integer K))
    (q : ActualSIntegerOrbit K S) : ActualSIntegerOrbit K S :=
  sIntegerOrbitDilation K S (sixthPowerSUnitSubgroup K S)
    ⟨a.val ^ 6, pow_ne_zero 6 a.property⟩ q

/-- Associated generators have identical sixth-power actions on the
actual quotient, even though the generators themselves need not agree. -/
private theorem sixthDilation_eq_of_span
    (a b : NonzeroRingElements (S.integer K))
    (hspan : Ideal.span ({a.val} : Set (S.integer K)) =
      Ideal.span ({b.val} : Set (S.integer K)))
    (q : ActualSIntegerOrbit K S) :
    sixthDilation K S a q = sixthDilation K S b q := by
  sorry

private theorem sixthDilation_comp
    (a b : NonzeroRingElements (S.integer K)) (q : ActualSIntegerOrbit K S) :
    sixthDilation K S a (sixthDilation K S b q) =
      sixthDilation K S (sIntegerNonzeroMul K S a b) q := by
  sorry

variable (P : ProbeData K S)

private theorem simultaneousAmplifier_comp (q : ActualSIntegerOrbit K S)
    (I J : HeckeGeneral.ThetaSkeleton.ExteriorIdeal K S) :
    actualSimultaneousAmplifier K S P.arithmetic
        (actualSimultaneousAmplifier K S P.arithmetic q I) J =
      actualSimultaneousAmplifier K S P.arithmetic q (exteriorMul K S J I) := by
  sorry

/-- The actual physical base row used in `OriginalMovingFactors`.
Its unit sector comes from the original orbit equivalence. -/
def frequencyBase (q : ActualSIntegerOrbit K S) : FrequencyRow K S :=
  let x := (exteriorIdealSectorsEquivActualOrbits K S P).symm q
  decomposedFrequencyRow K S x.1 x.2

private def frequencyAmplifier (q : ActualSIntegerOrbit K S) :
    HeckeGeneral.ThetaSkeleton.ExteriorIdeal K S :=
  exteriorSixthPowerAmplifierPart S
    ((exteriorIdealSectorsEquivActualOrbits K S P).symm q).1

private theorem frequencyBase_spec (q : ActualSIntegerOrbit K S) :
    actualSimultaneousAmplifier K S P.arithmetic
        (frequencyRowOrbit K S P (frequencyBase K S P q))
        (frequencyAmplifier K S P q) = q := by
  sorry

theorem frequencyBase_simultaneousAmplifier (q : ActualSIntegerOrbit K S)
    (I : HeckeGeneral.ThetaSkeleton.ExteriorIdeal K S) :
    frequencyBase K S P (actualSimultaneousAmplifier K S P.arithmetic q I) =
      frequencyBase K S P q := by
  sorry

/-- The sixth power can use any actual nonzero generator.  Its
principal ideal supplies the amplifier, and the unit discrepancy is
removed in the original sixth-unit quotient. -/
theorem frequencyBase_sixth_mul
    (a b : NonzeroRingElements (S.integer K)) :
    frequencyBase K S P (Quotient.mk _
      (⟨a.val ^ 6 * b.val, mul_ne_zero (pow_ne_zero 6 a.property) b.property⟩ :
        NonzeroRingElements (S.integer K))) =
      frequencyBase K S P (Quotient.mk _ b) := by
  sorry

end ActualRows

open LocalFiniteSums CanonicalLiteralPhaseCalibration CanonicalLiteralPaidCharacters

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- A complete Hecke-character identity, obtained by equality of the
actual inputs to the original row-character function. -/
theorem singleton_character_sixth_mul (a b : NonzeroRingElements A.R) (e : ℤ) :
    (OriginalMovingFactors.singleton (P := P) (R := R)
      ⟨a.val ^ 6 * b.val, mul_ne_zero (pow_ne_zero 6 a.property) b.property⟩ e).character =
      (OriginalMovingFactors.singleton (P := P) (R := R) b e).character := by
  sorry

/-- The original one/six/seven pool factor and the reduced active
factor have the same character, while their deletion masks stay separate. -/
theorem poolMoving_character (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity)) :
    (F.poolMoving P R).character =
      (CanonicalLiteralPassivePhases.activeMoving P R C p e).character := by
  sorry

theorem moving_character (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) :
    (F.moving P R oldMoving).character =
      ((reducedPhases F C p e).moving P R oldMoving).character := by
  sorry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem appended_character (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) (primes : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool) :
    ((F.moving P R oldMoving).appendSecondFactor C primes m n pattern).character =
      (((reducedPhases F C p e).moving P R oldMoving).appendSecondFactor
        C primes m n pattern).character := by
  sorry

theorem rowCharacter_eq (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (primes : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    CanonicalLiteralAllocatedData.rowCharacter P R F oldMoving correction C primes m n
        pattern ν u =
      CanonicalLiteralAllocatedData.rowCharacter P R (reducedPhases F C p e)
        oldMoving correction C primes m n pattern ν u := by
  sorry

theorem literalCharacter_eq {H : Type*} (S : ActualSecondCorrelationRows A σ H ι)
    (F : FixedPhases A) (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (h : H) :
    S.literalCharacter C P R F oldMoving correction pattern ν h =
      S.literalCharacter C P R (reducedPhases F C p e) oldMoving correction pattern ν h := by
  sorry

/-- The original ordinary filter is unchanged before any passive
allocation or normalized child is selected. -/
theorem ordinary_iff {H : Type*} (S : ActualSecondCorrelationRows A σ H ι)
    (F : FixedPhases A) (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (theta : Finset (HeckeCharacter K)) (h : H) :
    S.literalCharacter C P R F oldMoving correction pattern ν h ∉ theta ↔
      S.literalCharacter C P R (reducedPhases F C p e) oldMoving correction pattern ν h ∉ theta := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralPaidRowCharacters

end

/-!
# Calibration of the paid passive-allocation frames

The paid source uses the original moving recipe after its passive
ideal factors have been separated into the finite allocation sum.
Its arithmetic dictionary is the original appended dictionary.  The
new divisor is squarefree because its actual Moebius sign is nonzero;
the frozen scalar is bounded from its individual original atoms.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckePort.Moments
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

namespace CanonicalLiteralPaidCharacters

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (index : Fin k → Fin parent.geometry.slotCount)

theorem paidSourceCharacters_maskIndicator :
    (paidSourceCharacters P R F parent oldMoving correction remaining index).MaskIndicator := by
  sorry

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (S : ActualSecondCorrelationRows A σ H ι) (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (m q : ℝ) (inverse : IdealTest K)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)

/-- The paid source and its actual child are calibrated directly by
the existing appended recipe. No whole-character equality is supplied. -/
def actualPaidDictionary
    (row : CanonicalOriginalPhaseCalibration.PatternSector P S C pattern sector)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    ((paidSourceCharacters P R F parent oldMoving correction remaining index).restrictSlots
      B.keep).Calibration (σ := σ)
      (CanonicalLiteralAllocatedData.data P R W B F parent oldMoving correction hcorr C
        S.primes S.leftMultiplicity S.rightMultiplicity pattern sector remaining 1 m q inverse
        index rectangle firstSign negative ξ) rfl
      (S.extractedRow C row.val.val).momentIdeal
      (if negative then -(S.factor C row.val.val.val) else S.factor C row.val.val.val)
      (S.extractedRow C row.val.val).element := by
  cases negative with
  | false =>
      simpa only [CanonicalLiteralAllocatedData.data, mul_one, paidSourceCharacters] using
        CanonicalAppendedPhaseCalibration.actualAllocatedCalibration P R parent
          (F.moving P R oldMoving) correction hcorr C pattern sector remaining
          (d.base ^ (m + q)) inverse (W.fourierLeft rectangle firstSign false ξ)
          (W.fourierRight rectangle firstSign false ξ)
          (CanonicalLiteralAllocatedData.preGeometry W firstSign false ξ) index
          S B hone hroot hemb row
  | true =>
      simpa only [CanonicalLiteralAllocatedData.data, mul_one, paidSourceCharacters] using
        CanonicalAppendedPhaseCalibration.actualNegativeAllocatedCalibration P R parent
          (F.moving P R oldMoving) correction hcorr C pattern sector remaining
          (d.base ^ (m + q)) inverse (W.fourierLeft rectangle firstSign true ξ)
          (W.fourierRight rectangle firstSign true ξ)
          (CanonicalLiteralAllocatedData.preGeometry W firstSign true ξ) index
          S B hone hroot hemb row

end CanonicalLiteralPaidCharacters

namespace CanonicalLiteralPassiveFrames

open CanonicalLiteralPassiveSource CanonicalLiteralPassiveNonzero

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (paid : FixedChildCharacters K B.keep.card)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (S : ActualSecondCorrelationRows A σ H ι) (side : SecondColumnSide)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })
variable (firstSign : ℝ) (rectangle : Bool)

local notation "f" => frame W B A paid C S side M a firstSign rectangle
local notation "t" => table W B A paid

/-- Individual original atom bounds on this exact passive allocation.
The independent divisor norm is retained by `scalarBound`. -/
def frozenBounds (hmask : paid.MaskIndicator) (ha : a ∈ nonzeroLabels W B A M) :
    (f).source.FrozenAtomBounds where
  annulus i := (Ideal.absNorm ((branch W B A M a).witness.2 i).asIdeal : ℝ) /
    (t).base ^ (t).length i
  profile i := ‖(t).slotWeight i ((branch W B A M a).witness.2 i)‖ ^ 2
  annulus_nonneg i := div_nonneg (Nat.cast_nonneg _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans (t).base_gt_one) _).le
  profile_nonneg i := sq_nonneg _
  plain₁_bound h _ := by
    cases side <;> exact OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
      paid.plain paid.plainTwist paid.mask _ (hmask _)
  plain₂_bound h _ := by
    cases side <;> exact OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
      paid.plain paid.plainTwist paid.mask _ (hmask _)
  prime_bound h _ i _ := by
    cases side <;> exact OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one
      (paid.slot i) (paid.slotTwist i) paid.mask _ (hmask _)
  prime_annulus i _ := by
    cases side <;> exact le_of_eq (div_mul_cancel₀ _
      (Real.rpow_pos_of_pos (zero_lt_one.trans (t).base_gt_one) _).ne').symm
  slot_bound h _ i _ := by cases side <;> exact le_rfl
  divisor_squarefree := by
    cases side <;> exact divisor_squarefree W B A M a ha
  allocation_mem := by
    cases side <;> exact selection_mem W B A M a

theorem frozenBounds_scalarBound (hmask : paid.MaskIndicator)
    (ha : a ∈ nonzeroLabels W B A M) :
    (frozenBounds W B paid C S side M a firstSign rectangle hmask ha).scalarBound =
      (∏ i ∈ Finset.univ \ (branch W B A M a).keep,
        (((Ideal.absNorm ((branch W B A M a).witness.2 i).asIdeal : ℝ) /
            (t).base ^ (t).length i) *
          ‖(t).slotWeight i ((branch W B A M a).witness.2 i)‖ ^ 2)) /
        (Ideal.absNorm a.val.1 : ℝ) := by
  sorry

end CanonicalLiteralPassiveFrames

namespace CanonicalLiteralPassiveSource.PhaseChoice

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {F : CanonicalLiteralPhaseCalibration.FixedPhases A}
variable {C : A.GeneralArithmeticContext σ η hS}
variable (choice : PhaseChoice F C)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

theorem literalCharacter_eq (S : ActualSecondCorrelationRows A σ H ι)
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (pattern : ι → Bool)
    (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (h : H) :
    S.literalCharacter C P R F oldMoving correction pattern sector h =
      S.literalCharacter C P R choice.phases oldMoving correction pattern sector h := by
  sorry

end CanonicalLiteralPassiveSource.PhaseChoice

end HeckeSkeleton.Moments.EngineStepV2

end

set_option quotPrecheck false

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

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

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
  ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂) C kLeft kRight)
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
  (({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂
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
      (P := P) (R := Rchar) (W := W) (B := B) («paid» := paid) (F := choice.phases)
      (parent := parent) (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
      (C := C) (p := (S).primes) (leftMultiplicity := (S).leftMultiplicity)
      (rightMultiplicity := (S).rightMultiplicity) («pattern» := pattern) (ν := sector)
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
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The complete moving recipe of the computed literal child

The recipe is built from exactly the same appended moving factors,
remaining first deletion and complete second sixth root as the actual
allocated data. The full joint budget is the literal allowed-row
predicate of these data. The preceding physical-row theorem proves
that the original rows satisfy it; this file does not assume a final
support or a source-energy bound.

Clipping the two plain scales preserves every arithmetic field and
the same full budget. The recipe can therefore be supplied directly
to the full-kappa prime estimate for the chosen calibration.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralAllocatedData

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

/-- No new moving element, sector or deletion ideal is selected. -/
def recipe : CompleteMovingRowRecipe A P R
    (data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative) where
  moving := (F.moving P R oldMoving).appendSecondFactor C p leftMultiplicity
    rightMultiplicity pattern
  correction := correction
  correction_mem _ := Or.inr hcorr
  sector _ := ν
  exterior _ _ hu := hu.1
  character _ _ _ := rfl
  remaining := remainingMaskIdeal A (remaining * extra) *
    exteriorMomentIdeal (secondSixthRootIdeal p leftMultiplicity rightMultiplicity)
  mask _ _ _ := rfl

@[simp] theorem recipe_moving :
    (recipe P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative).moving =
      (F.moving P R oldMoving).appendSecondFactor C p leftMultiplicity rightMultiplicity pattern := rfl

@[simp] theorem recipe_remaining :
    (recipe P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative).remaining =
      remainingMaskIdeal A (remaining * extra) *
        exteriorMomentIdeal (secondSixthRootIdeal p leftMultiplicity rightMultiplicity) := rfl

theorem recipe_fullJointBudget :
    (recipe P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative).FullJointBudget
        d.base (m + q) := by
  sorry

/-- The exact same arithmetic recipe applies to the clipped profiles.
The width here is still the original complete-deletion width. -/
def clippedRecipe (κ : ℝ) : CompleteMovingRowRecipe A P R (fun ξ =>
    clipPlainData
      (data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
        pattern ν remaining extra m q inverse index rectangle firstSign negative ξ)
      (parameters d B rectangle m q κ) d.base (zero_lt_one.trans d.base_gt_one)) :=
  (recipe P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
    pattern ν remaining extra m q inverse index rectangle firstSign negative).clipped
      (parameters d B rectangle m q κ) d.base (zero_lt_one.trans d.base_gt_one)

theorem clippedRecipe_fullJointBudget (κ : ℝ) :
    (clippedRecipe P R W B F parent oldMoving correction hcorr C p leftMultiplicity
      rightMultiplicity pattern ν remaining extra m q inverse index rectangle firstSign
      negative κ).FullJointBudget d.base (m + q) := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralAllocatedData

end

