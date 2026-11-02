import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualGaussStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstRowWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMovingSupportWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualJointRowWindows
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option linter.unusedSectionVars false

/-!
# Actual second frequencies and full joint support windows

The second modulus has the norm of the two original full columns.
Their individual windows and the original radius bound its common
physical cutoff. The cutoff exponent and every actual mask divisor
remain visible; neither can be discarded when forming the child width.

The retained rows are the literal negative orbit representatives used
by the complete correlation. After its genuine gcd/nonunit extraction,
the fixed full moving support is supplied by the original individual
factor formulas. Thus the joint window is proved from one physical
source and its original support atoms, without a final frequency or
joint-budget hypothesis. All complete masks remain unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments HeckePort.Moments.Support CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U}

/-- The radius uses the actual retained scale, even when its logarithmic
length is negative. No replacement by a nominal power is assumed. -/
theorem CanonicalRowBall.gaussRadius_eq_rpow
    (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 1 < Z) :
    (CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ)).val =
        Z ^ (-Real.log retainedScale / Real.log Z - g) := by
  sorry

section OriginalModulus

variable [IsPrincipalIdealRing A.R]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

/-- The full original column ideals determine every retained second
modulus. The maximum in the physical cutoff adds no column-count cost. -/
theorem FirstCommonCharacterBlock.secondPhysicalCutoff_le_original_windows
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (M : Finset (HeightOneSpectrum A.R)) (radius : {r : ℝ // 0 < r})
    (X : ℝ) (hX : 1 ≤ X)
    (Z cutoffExponent radiusExponent maskExponent leftExponent rightExponent : ℝ)
    (hZ : 0 < Z) (hcutoff : X ≤ Z ^ cutoffExponent)
    (hradius : radius.val ≤ Z ^ radiusExponent)
    (hmask : ∀ D ∈ M.powerset,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤
          Z ^ maskExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ leftExponent)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ rightExponent) :
    (b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX).physicalCutoff ≤
      Z ^ (cutoffExponent + radiusExponent + maskExponent +
        (leftExponent + rightExponent)) := by
  sorry

end OriginalModulus

section ActualRows

variable [IsPrincipalIdealRing A.R] [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {hΓ μv hDiff}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)

/-- The actual correlation uses -q.out, whose principal ideal has the
same norm as the original orbit. The label filter only restricts rows. -/
theorem actualRows_originalNorm_le_physicalCutoff
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (hq : q ∈ (chart.actualRows M X hX label).rows) :
    A.exteriorNorm ((chart.actualRows M X hX label).originalIdeal q) ≤
      (b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX).physicalCutoff := by
  sorry

/-- This frequency window is derived from the original source, its
literal canonical radius and individual full-column norm windows.
The cutoff and mask contributions remain in the displayed exponent. -/
theorem actualRows_originalNorm_le_canonical_windows
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ cutoffExponent maskExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hmask : ∀ M' ∈ M.powerset,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) M')).val ≤
          Z ^ maskExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (hq : q ∈ (chart.actualRows M X hX label).rows) :
    A.exteriorNorm ((chart.actualRows M X hX label).originalIdeal q) ≤
      Z ^ (2 * a₀ - Real.log retainedScale / Real.log Z - g +
        cutoffExponent + maskExponent) := by
  sorry

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- The same retained physical row and the full fixed moving support
produce the joint bound after the genuine correlation extraction.
Only individual original support formulas are accepted as arithmetic
inputs. In particular remaining support is paid together with D. -/
theorem actualRows_extracted_fullJoint_window
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent maskExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hmask : ∀ M' ∈ M.powerset,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) M')).val ≤
          Z ^ maskExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (moving : OriginalMovingFactors A P Rchar) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (old : A.Exterior) (hold : A.exteriorNorm old ≤ Z ^ (q + wo))
    (h : (chart.actualRows M X hX label).live)
    (W : moving.SupportAtoms old
      (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val))
      (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val))
      remaining) :
    idealNorm K ((chart.actualRows M X hX label).extractedRow C h).momentIdeal *
        idealNorm K (moving.fullMaskSupport remaining) ≤
      Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val
        (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val +
        cutoffExponent + maskExponent) := by
  sorry

end SecondBlockProfileChart
end ActualRows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalRowBall.gaussRadius_eq_rpow
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.secondPhysicalCutoff_le_original_windows
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_originalNorm_le_canonical_windows
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_extracted_fullJoint_window
