import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FullSecondDeletionSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalEmptySecondWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFrequencyClassStability

/-!
# Actual second windows with the complete sixth-root deletion

Fix an actual nonunit-pattern class of the original second correlation
rows. The moving list is its original active singleton, fixed throughout
that class. The original remaining ideal is multiplied by the complete
sixth-root ideal, retaining the sixth-power factor's genuine zeros.

The support certificate is constructed internally from the actual live
correlation and the original remaining-divisor identity. Its old-support
window is enlarged by the complete sixth root's literal logarithmic
length. The original physical cutoff and full-column windows then give
the joint bound on the same extracted row. Both the sixth-root length
and the cutoff exponent remain visible in the canonical child's budget.
No final support, joint-row or allowed-row estimate is an input.
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

private theorem fullDeletion_width_shift
    (Z a₀ q wo krow g r : ℝ) (I J T V : Ideal (𝓞 K)) :
    secondCommonChildWidth Z a₀ (q + r) wo krow g I J T V =
      secondCommonChildWidth Z a₀ q wo krow g I J T V + r := by
  unfold secondCommonChildWidth
  ring

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

namespace ActualSecondCorrelationRows

/-- Equality of the actual finite nonunit patterns fixes both radical
ideals on the live source. The unit complement is justified by the
original correlation, not imposed as a new classifier hypothesis. -/
theorem nonunitClass_radicals_eq
    {H ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ActualSecondCorrelationRows A σ H ι)
    (C : A.GeneralArithmeticContext σ η hS) {pattern : ι → Bool}
    (h h' : S.NonunitClass C pattern) :
    unitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val.val) =
        unitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h'.val.val) ∧
      nonunitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val.val) =
        nonunitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h'.val.val) := by
  apply S.frequencyRadicals_eq_of_nonunitClassification C h.val h'.val
  intro i
  exact decide_eq_decide.mp (congrFun (h.property.trans h'.property.symm) i)

end ActualSecondCorrelationRows

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

/-- The full support includes the original remaining deletion and
the complete sixth root. All row classifications, generated ideals and
support divisibilities are derived inside the proof on the actual class. -/
theorem actualRows_fullDeletion_joint_window
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (old : A.Exterior) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hremaining : remaining.val ∣ old.val)
    (hold : A.exteriorNorm old ≤ Z ^ (q + wo))
    (pattern : Fin b.primeCount → Bool)
    (h : (chart.actualRows ∅ X hX label).NonunitClass C pattern) :
    idealNorm K ((chart.actualRows ∅ X hX label).extractedRow C h.val).momentIdeal *
        idealNorm K
          ((secondOriginalMovingFactors P Rchar C b.primes b.leftMultiplicity
            b.rightMultiplicity pattern).fullMaskSupport
              (remaining * secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ≤
      Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.val.out.val)).val
        (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.val.out.val)).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent) := by
  let r₆ : ℝ := idealLogLength Z
    (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val
  have holdRoot := secondOldWithSixthRoot_norm_window
    b.primes b.leftMultiplicity b.rightMultiplicity old Z (q + wo) hZ hold
  change A.exteriorNorm
    (ExteriorIdealEuler.mul old (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ≤
      Z ^ ((q + wo) + r₆) at holdRoot
  rw [show (q + wo) + r₆ = (q + r₆) + wo by ring] at holdRoot
  let S := chart.actualRows ∅ X hX label
  let W := S.nonunitClassFullDeletionSupportAtoms P Rchar C
    b.left_positive b.right_positive old remaining hremaining pattern h
  have hjoint := chart.actualRows_empty_extracted_fullJoint_window X hX label
    retainedScale Z g a₀ (q + r₆) wo cutoffExponent hscale hZ hradius hcutoff hleft hright
    (secondOriginalMovingFactors P Rchar C b.primes b.leftMultiplicity b.rightMultiplicity pattern)
    (remaining * secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
    (ExteriorIdealEuler.mul old (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity))
    holdRoot h.val W
  simpa only [fullDeletion_width_shift, r₆] using hjoint

/-- The same canonical data retain all original backgrounds, sectors,
tests and selected slots. Their allowed row follows from the actual
physical source with full sixth-root deletion, without an allowed-row
or support certificate supplied by the caller. -/
theorem canonicalOriginalChild_allowed_of_fullDeletion_windows
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (old : A.Exterior) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hremaining : remaining.val ∣ old.val)
    (hold : A.exteriorNorm old ≤ Z ^ (q + wo))
    (pattern : Fin b.primeCount → Bool)
    (h : (chart.actualRows ∅ X hX label).NonunitClass C pattern)
    {ω ψ : HeckeCharacter K} (parent : MomentData K ω ψ)
    (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
    (sector : HeckeGeneral.Analysis.NonzeroIdeal K →
      SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (inverseTest leftTest rightTest : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount) :
    (CanonicalOriginalChildData.data parent
      (secondOriginalMovingFactors P Rchar C b.primes b.leftMultiplicity b.rightMultiplicity pattern)
      correction hcorr sector
      (remaining * secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
      (Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.val.out.val)).val
        (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.val.out.val)).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent))
      inverseTest leftTest rightTest geometry index).allowedRow
        ((chart.actualRows ∅ X hX label).extractedRow C h.val).momentIdeal := by
  refine ⟨(HeckeAxiom.exteriorEquiv A
    ((chart.actualRows ∅ X hX label).extractedRow C h.val).ideal).property, ?_⟩
  exact chart.actualRows_fullDeletion_joint_window P Rchar X hX label
    retainedScale Z g a₀ q wo cutoffExponent hscale hZ hradius hcutoff hleft hright
    old remaining hremaining hold pattern h

/-- A single actual anchor fixes the canonical child's budget for the
entire nonunit-pattern class. Every other original row enters that same
data object, with unchanged moving list, deletion, sector and profiles.
No anchor is needed for an empty class. -/
theorem canonicalOriginalChild_allowed_on_fullDeletion_class
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (old : A.Exterior) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hremaining : remaining.val ∣ old.val)
    (hold : A.exteriorNorm old ≤ Z ^ (q + wo))
    (pattern : Fin b.primeCount → Bool)
    (anchor h : (chart.actualRows ∅ X hX label).NonunitClass C pattern)
    {ω ψ : HeckeCharacter K} (parent : MomentData K ω ψ)
    (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
    (sector : HeckeGeneral.Analysis.NonzeroIdeal K →
      SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (inverseTest leftTest rightTest : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount) :
    (CanonicalOriginalChildData.data parent
      (secondOriginalMovingFactors P Rchar C b.primes b.leftMultiplicity b.rightMultiplicity pattern)
      correction hcorr sector
      (remaining * secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
      (Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-anchor.val.val.out.val)).val
        (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-anchor.val.val.out.val)).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent))
      inverseTest leftTest rightTest geometry index).allowedRow
        ((chart.actualRows ∅ X hX label).extractedRow C h.val).momentIdeal := by
  have hjoint := chart.actualRows_fullDeletion_joint_window P Rchar X hX label
    retainedScale Z g a₀ q wo cutoffExponent hscale hZ hradius hcutoff hleft hright
    old remaining hremaining hold pattern h
  obtain ⟨hunit, hnonunit⟩ :=
    (chart.actualRows ∅ X hX label).nonunitClass_radicals_eq C h anchor
  change unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.val.out.val) =
    unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-anchor.val.val.out.val) at hunit
  change nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.val.out.val) =
    nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-anchor.val.val.out.val) at hnonunit
  rw [hunit, hnonunit] at hjoint
  exact ⟨(HeckeAxiom.exteriorEquiv A
    ((chart.actualRows ∅ X hX label).extractedRow C h.val).ideal).property, hjoint⟩

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.nonunitClass_radicals_eq
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_fullDeletion_joint_window
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.canonicalOriginalChild_allowed_of_fullDeletion_windows
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.canonicalOriginalChild_allowed_on_fullDeletion_class
