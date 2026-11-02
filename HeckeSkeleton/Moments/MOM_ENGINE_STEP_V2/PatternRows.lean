import HeckeSkeleton.Moments.MOM_ENGINE_STEP.UnrestrictedSixthCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RowClasses

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A fixed original pattern before ordinary-row normalization

The canonical finite row classifier fixes the nonunit pattern on every
original row of its label. The pattern is chosen from those rows before
the exceptional partition or the construction of normalization data; an
empty label has the all-false pattern.

Its computed unit and nonunit ideals give one fixed child budget. Each
actual live row satisfies that budget by the original physical cutoff
and the complete sixth-root support theorem. No ordinary-row witness,
finished joint-row bound, or allowed-row assumption is supplied.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments CommonSupportMass

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
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}

namespace SecondBlockProfileChart

section OriginalPattern

variable {D : Finset (HeightOneSpectrum A.R)}
variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)

theorem actualRows_original_rowLabel
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (h : (chart.actualRows M X hX label).rows) : chart.rowLabel h.val = label :=
  (Finset.mem_filter.mp h.property).2

/-- The choice precedes normalization and needs no live or ordinary
row. The empty original label has one fixed harmless pattern. -/
def originalNonunitPattern
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1)) : Fin b.primeCount → Bool :=
  if hrows : (chart.actualRows M X hX label).rows.Nonempty then
    actualNonunitPattern C b.primes b.leftMultiplicity b.rightMultiplicity
      (-hrows.choose.out.val)
  else fun _ => false

theorem actualRows_originalNonunitPattern
    (hclass : (SecondBlockProfileChart.NonunitLabelStable (chart := chart)))
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (h : (chart.actualRows M X hX label).rows) :
    actualNonunitPattern C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val) =
      (SecondBlockProfileChart.originalNonunitPattern (chart := chart)) M X hX label := by
  have hrows : (chart.actualRows M X hX label).rows.Nonempty := ⟨h.val, h.property⟩
  rw [originalNonunitPattern, dif_pos hrows]
  funext i
  apply decide_eq_decide.mpr
  exact hclass h.val hrows.choose
    (((SecondBlockProfileChart.actualRows_original_rowLabel (chart := chart)) M X hX label h).trans
      ((SecondBlockProfileChart.actualRows_original_rowLabel (chart := chart)) M X hX label
        ⟨hrows.choose, hrows.choose_spec⟩).symm) i

/-- Every original live row is placed in the same already chosen
class, without asking the caller for an ordinary-row witness. -/
def originalNonunitClass
    (hclass : (SecondBlockProfileChart.NonunitLabelStable (chart := chart)))
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (h : (chart.actualRows M X hX label).live) :
    (chart.actualRows M X hX label).NonunitClass C
      ((SecondBlockProfileChart.originalNonunitPattern (chart := chart)) M X hX label) :=
  ⟨h, (SecondBlockProfileChart.actualRows_originalNonunitPattern (chart := chart)) hclass M X hX label
    ⟨h.val, (Finset.mem_filter.mp h.property).1⟩⟩

@[simp] theorem originalNonunitClass_val
    (hclass : (SecondBlockProfileChart.NonunitLabelStable (chart := chart)))
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (h : (chart.actualRows M X hX label).live) :
    ((SecondBlockProfileChart.originalNonunitClass (chart := chart)) hclass M X hX label h).val = h := rfl

end OriginalPattern

section FullDeletion

variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}
variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)

/-- The original physical cutoff bounds the full retained mask on
one fixed pattern budget. Its two radical ideals do not depend on h. -/
theorem actualRows_pattern_fullDeletion_joint_window
    (hclass : (SecondBlockProfileChart.NonunitLabelStable (chart := chart)))
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
    (h : (chart.actualRows ∅ X hX label).live) :
    let pattern := (SecondBlockProfileChart.originalNonunitPattern (chart := chart)) ∅ X hX label
    idealNorm K ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal *
        idealNorm K
          ((secondOriginalMovingFactors P Rchar C b.primes b.leftMultiplicity
            b.rightMultiplicity pattern).fullMaskSupport
              (remaining * secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ≤
      Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
        (secondPatternNonunitIdeal b.primes pattern).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent) := by
  sorry

/-- The same canonical moment data admit all actual extracted live
rows. In particular this universal claim is available on an empty
ordinary class before its normalization data are constructed. -/
theorem canonicalOriginalChild_allowed_of_pattern_fullDeletion
    (hclass : (SecondBlockProfileChart.NonunitLabelStable (chart := chart)))
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
    {ω ψ : HeckeCharacter K} (parent : MomentData K ω ψ)
    (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
    (sector : HeckeGeneral.Analysis.NonzeroIdeal K →
      SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (inverseTest leftTest rightTest : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)
    (h : (chart.actualRows ∅ X hX label).live) :
    let pattern := (SecondBlockProfileChart.originalNonunitPattern (chart := chart)) ∅ X hX label
    (CanonicalOriginalChildData.data parent
      (secondOriginalMovingFactors P Rchar C b.primes b.leftMultiplicity b.rightMultiplicity pattern)
      correction hcorr sector
      (remaining * secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
      (Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
        (secondPatternNonunitIdeal b.primes pattern).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent))
      inverseTest leftTest rightTest geometry index).allowedRow
        ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal := by
  sorry

end FullDeletion
end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStepV2

#print axioms HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.actualRows_originalNonunitPattern
#print axioms HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitClass
#print axioms HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.actualRows_pattern_fullDeletion_joint_window
#print axioms HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.canonicalOriginalChild_allowed_of_pattern_fullDeletion

