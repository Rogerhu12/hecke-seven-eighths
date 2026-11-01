import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPatternChildWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonScalarReweight
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalThetaRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridZeroRowSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalOrbitFibre

/-!
# Actual row mass on the original nonzero correlation support

The original row classifier fixes the divided nonunit pattern. The unit
radical is its complement only on nonzero correlations; zero correlations
must therefore be removed before populating `ActualSecondRowMass`.

The row restriction here is exactly the zero-removal identity proved in
`HybridZeroRowSupport`. No row bound or aggregate source identity is a
premise. The canonical constructor uses the original chart, its original
common atoms and its individual profile window, computes both radical
ideals from the already fixed pattern, and proves the original fibre
bound with `Γ.index`. Neither a live nor an ordinary row is required.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]

namespace ActualSecondRowMass

/-- Build the original mass dictionary after deleting only genuine
correlation-zero rows. The unit/nonunit fields follow from the original
local classification; the caller supplies neither radical identity. -/
def ofCorrelationSupportedPattern
    {H ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ActualSecondCorrelationRows A σ H ι)
    (C : A.GeneralArithmeticContext σ η hS) {kLeft kRight : ℕ}
    (left : FrozenSourceAtoms A σ H R.rows kLeft)
    (right : FrozenSourceAtoms A σ H R.rows kRight)
    (hleft : left.ideal = (primePowerProduct R.primes R.leftMultiplicity).val)
    (hright : right.ideal = (primePowerProduct R.primes R.rightMultiplicity).val)
    (pattern : ι → Bool)
    (hpattern : ∀ h ∈ R.rows, actualNonunitPattern C R.primes
      R.leftMultiplicity R.rightMultiplicity (R.frequency h) = pattern)
    (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (profile : H → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hprofile : ∀ h ∈ R.rows, ‖profile h‖ ≤ B)
    (hweight : ∀ h ∈ R.rows,
      R.weight h = secondOrbitalScalar (K := K) (S := A.Sf) radius mask * profile h)
    (hpositive : ∀ i, 0 < R.leftMultiplicity i)
    (fiber : ℕ) (hfiber : ∀ I : Ideal (𝓞 K),
      (R.rows.filter (fun h => (R.originalIdeal h).val = I)).card ≤ fiber) :
    ActualSecondRowMass
      ((R.withCommonAtoms left right).restrictRows (fun h => R.correlation h ≠ 0))
      C kLeft kRight := by
  let left' := left.onRows R.live (Finset.filter_subset _ _)
  let right' := right.onRows R.live (Finset.filter_subset _ _)
  refine ofCommonAtoms (R.restrictRows (fun h => R.correlation h ≠ 0)) C
    left' right' hleft hright radius mask profile B hB
    (fun h hh => hprofile h (Finset.mem_filter.mp hh).1)
    (fun h hh => hweight h (Finset.mem_filter.mp hh).1)
    (secondPatternUnitIdeal R.primes R.leftMultiplicity R.rightMultiplicity pattern)
    (secondPatternNonunitIdeal R.primes pattern) ?_ ?_ hpositive fiber ?_
  · intro h hh
    exact (R.secondPatternUnitIdeal_eq_live C pattern ⟨h, hh⟩
      (hpattern h (Finset.mem_filter.mp hh).1)).symm
  · intro h hh
    exact (R.secondPatternNonunitIdeal_eq C pattern h
      (hpattern h (Finset.mem_filter.mp hh).1)).symm
  · intro I
    apply le_trans (Finset.card_le_card ?_) (hfiber I)
    intro h hh
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1,
        (Finset.mem_filter.mp hh).2⟩

end ActualSecondRowMass

variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
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
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)
variable (hclass : chart.NonunitLabelStable)
variable (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
variable (label : Fin (chart.rowLabelCount + 1))
variable {kLeft kRight : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
  (chart.actualRows M X hX label).rows kLeft)
variable (rightAtoms : FrozenSourceAtoms A σ
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
  (chart.actualRows M X hX label).rows kRight)
variable (hleft : leftAtoms.ideal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hright : rightAtoms.ideal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (bound : ℝ) (hbound : 0 ≤ bound)
variable (hprofile : ∀ q ∈ (chart.actualRows M X hX label).rows, ‖chart.weight q‖ ≤ bound)

/-- This is the actual chart calibration, including empty original or
ordinary classes. Both ideal radicals and the fibre bound are proved
from the original classifier and original orbit map, before children
are normalized or selected. -/
def actualRowsSupportedMass :
    ActualSecondRowMass
      (((chart.actualRows M X hX label).withCommonAtoms leftAtoms rightAtoms).restrictRows
        (fun q => (chart.actualRows M X hX label).correlation q ≠ 0))
      C kLeft kRight :=
  ActualSecondRowMass.ofCorrelationSupportedPattern
    (chart.actualRows M X hX label) C leftAtoms rightAtoms hleft hright
    (chart.originalNonunitPattern M X hX label)
    (fun q hq => chart.actualRows_originalNonunitPattern hclass M X hX label ⟨q, hq⟩)
    radius D chart.weight bound hbound hprofile (fun _ _ => rfl)
    b.left_positive Γ.index (chart.actualRows_original_fibers M X hX label)

@[simp] theorem actualRowsSupportedMass_unitIdeal :
    (chart.actualRowsSupportedMass hclass M X hX label leftAtoms rightAtoms hleft hright
      bound hbound hprofile).unitIdeal =
      secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity
        (chart.originalNonunitPattern M X hX label) := rfl

@[simp] theorem actualRowsSupportedMass_nonunitIdeal :
    (chart.actualRowsSupportedMass hclass M X hX label leftAtoms rightAtoms hleft hright
      bound hbound hprofile).nonunitIdeal =
      secondPatternNonunitIdeal b.primes (chart.originalNonunitPattern M X hX label) := rfl

@[simp] theorem actualRowsSupportedMass_originalFiber :
    (chart.actualRowsSupportedMass hclass M X hX label leftAtoms rightAtoms hleft hright
      bound hbound hprofile).originalFiber = Γ.index := rfl

@[simp] theorem actualRowsSupportedMass_commonEnvelope :
    (chart.actualRowsSupportedMass hclass M X hX label leftAtoms rightAtoms hleft hright
      bound hbound hprofile).commonEnvelope =
      bound * Real.sqrt leftAtoms.envelope * Real.sqrt rightAtoms.envelope := rfl

/-- The later ordinary predicate changes only the original finite row
proofs. Its computed pattern ideals and fixed orbit fibre are retained. -/
theorem actualRowsSupportedMass_ordinary_fields
    (exceptional : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop) :
    let W := (chart.actualRowsSupportedMass hclass M X hX label leftAtoms rightAtoms
      hleft hright bound hbound hprofile).restrictRows (fun q => ¬exceptional q)
    W.unitIdeal = secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity
        (chart.originalNonunitPattern M X hX label) ∧
      W.nonunitIdeal = secondPatternNonunitIdeal b.primes
        (chart.originalNonunitPattern M X hX label) ∧
      W.originalFiber = Γ.index := ⟨rfl, rfl, rfl⟩

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.ofCorrelationSupportedPattern
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRowsSupportedMass
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRowsSupportedMass_ordinary_fields
