import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EmptyGaussMask
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondRowWindows

/-!
# The actual empty-mask second frequencies enter the canonical child

The original Gauss source is majorized with the empty additional row
mask. Its only divisor is still the actual chosen unit: neither that
unit nor its character phases are replaced. The complete column masks
and the fixed full moving support of the child remain unchanged.

The empty-divisor norm is proved to be one, so its exponent is zero in
the physical frequency window. The original cutoff exponent remains.
The same full correlation row, its genuine extraction, and the
individual original support formulas then prove membership in the
canonical child's allowed-row predicate. No completed frequency,
joint-support, or allowed-row bound is an input.
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

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [IsPrincipalIdealRing A.R] [Γ.FiniteIndex]
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
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)

/-- The original physical rows pay the cutoff and both full-column
norms. The empty row-mask divisor contributes exactly exponent zero. -/
theorem actualRows_empty_originalNorm_le
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (hq : q ∈ (chart.actualRows ∅ X hX label).rows) :
    A.exteriorNorm ((chart.actualRows ∅ X hX label).originalIdeal q) ≤
      Z ^ (2 * a₀ - Real.log retainedScale / Real.log Z - g + cutoffExponent) := by
  simpa only [add_zero] using
    chart.actualRows_originalNorm_le_canonical_windows ∅ X hX label
      retainedScale Z g a₀ cutoffExponent 0 hscale hZ hradius hcutoff
      (emptyMask_norm_window K A.Sf Z) hleft hright q hq

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- The complete moving support includes every original factor and
the remaining ideal. Its joint window is derived on the same extracted
row of the nonzero complete correlation, including all original sectors. -/
theorem actualRows_empty_extracted_fullJoint_window
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (moving : OriginalMovingFactors A P Rchar)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
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
  simpa only [add_zero] using
    chart.actualRows_extracted_fullJoint_window ∅ X hX label
      retainedScale Z g a₀ q wo cutoffExponent 0 hscale hZ hradius hcutoff
      (emptyMask_norm_window K A.Sf Z) hleft hright moving remaining old hold h W

/-- The same canonical child's allowed-row predicate follows directly
from its original physical source and individual support formulas. All
parent backgrounds, moving elements, correction, sectors, remaining
ideal, tests and selected slot identities are retained literally. -/
theorem canonicalOriginalChild_allowed_of_empty_second_windows
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    {ω ψ : HeckeCharacter K} (parent : MomentData K ω ψ)
    (moving : OriginalMovingFactors A P Rchar)
    (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
    (sector : HeckeGeneral.Analysis.NonzeroIdeal K →
      SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (old : A.Exterior) (hold : A.exteriorNorm old ≤ Z ^ (q + wo))
    (h : (chart.actualRows ∅ X hX label).live)
    (W : moving.SupportAtoms old
      (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val))
      (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val))
      remaining)
    (inverseTest leftTest rightTest : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount) :
    (CanonicalOriginalChildData.data parent moving correction hcorr sector remaining
      (Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val
        (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val +
        cutoffExponent))
      inverseTest leftTest rightTest geometry index).allowedRow
        ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal := by
  refine ⟨(HeckeAxiom.exteriorEquiv A
    ((chart.actualRows ∅ X hX label).extractedRow C h).ideal).property, ?_⟩
  exact chart.actualRows_empty_extracted_fullJoint_window X hX label
    retainedScale Z g a₀ q wo cutoffExponent hscale hZ hradius hcutoff
    hleft hright moving remaining old hold h W

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_empty_originalNorm_le
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_empty_extracted_fullJoint_window
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.canonicalOriginalChild_allowed_of_empty_second_windows
