import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalParentWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalIndexMass

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# Compose actual first and second exceptional estimates at their original index

The first profile is paid together with its actual scalar pair. The
second magnitude is divided by the exact first allowance of the same
stored parent leaf. Both original divisor coefficients and both phase
coefficients enter the original dependent arithmetic index.

The two estimates consumed here are internal conclusions of the actual
literal-source constructors. This algebraic composition introduces no
new primitive hypothesis for the final engine theorem.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LocalFiniteSums (ExteriorPrime)
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local instance canonicalExceptionalOriginalPointwiseCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}


namespace ActualDirectFirstSource.SecondStages

variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)
variable {cap : ℕ} (hcap : L.slotCount ≤ cap) (hZ : 1 < Z)
variable (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)
variable (exceptional : R.CoverHybridPredicates L)

local notation "normalization" => s.canonicalNormalization hZ total
variable (i : R.liveLeaves L exceptional normalization)
local notation "leaf" => R.parentLeaf L exceptional normalization i.val
local notation "labels" => R.arithmeticLabels L hcap exceptional normalization
local notation "j" => R.originalIndex L hcap exceptional normalization i

variable (extract : (leaf).ConstantAtomExtraction)
variable (leftScalar rightScalar : ℂ) (hleftScalar : leftScalar ≠ 0)
variable (hrightScalar : rightScalar ≠ 0)
local notation "outerLeaf" => extract.stripOuter leftScalar rightScalar hleftScalar hrightScalar
variable {theta : Finset (HeckeCharacter K)}
variable (characters : PairedFiniteCharacters theta
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ))
variable (thetaPair : theta × theta) (z : W × E)
local notation "magnitude" => ((outerLeaf).thetaClassLeaf characters thetaPair).exceptionalIntegrand z

/-- The actual canonical first allowance is positive in either of the
original Cauchy orientations. -/
theorem firstAllowanceAt_canonical_pos : 0 < R.firstAllowanceAt L total i.val := by
  sorry

/-- The actual original two orbital fibres and the first Cauchy half
form a nonnegative outer factor. -/
theorem originalScalarAt_nonneg (key : R.CoveredLeafKey L) :
    0 ≤ R.originalScalarAt L key := by
  sorry

/-- The exact denominator is retained until the already proved
second-source estimate is used. No natural-width substitution occurs. -/
theorem stripOuter_theta_pointwise
    (parentWidth firstCost secondCost remaining lower tilt : ℝ)
    (hfirstCost : 0 ≤ firstCost)
    (hfirst : (s.pieces i.val.1 i.val.2.1).weightBound *
        (‖leftScalar‖ * ‖rightScalar‖) ≤
      firstCost * Z ^ (parentWidth - total i.val.1 i.val.2.1 + tilt))
    (hsecond : magnitude / R.firstAllowanceAt L total i.val ≤
      secondCost * Z ^ remaining /
        (Ideal.absNorm (commonRadical (R.commonLabel L i.val).1
          (R.commonLabel L i.val).2) : ℝ) * Z ^ (-lower)) :
    ((outerLeaf).weight / Z ^ parentWidth) * magnitude ≤
      R.originalScalarAt L i.val *
        (firstCost * secondCost * Z ^ (remaining + tilt) *
          (labels).carrier.exceptionalDyadWeight Z lower j) := by
  sorry

end ActualDirectFirstSource.SecondStages
namespace ActualFirstSource.SecondStages

variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)
variable {cap : ℕ} (hcap : L.slotCount ≤ cap) (hZ : 1 < Z)
variable (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)
variable (exceptional : R.CoverHybridPredicates L)

local notation "normalization" => s.canonicalNormalization hZ total
variable (i : R.liveLeaves L exceptional normalization)
local notation "leaf" => R.parentLeaf L exceptional normalization i.val
local notation "labels" => R.arithmeticLabels L hcap exceptional normalization
local notation "j" => (labels).index i

variable (extract : (leaf).ConstantAtomExtraction)
variable (leftScalar rightScalar : ℂ) (hleftScalar : leftScalar ≠ 0)
variable (hrightScalar : rightScalar ≠ 0)
local notation "outerLeaf" => extract.stripOuter leftScalar rightScalar hleftScalar hrightScalar
variable {theta : Finset (HeckeCharacter K)}
variable (characters : PairedFiniteCharacters theta
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ))
variable (thetaPair : theta × theta) (z : W × E)
local notation "magnitude" => ((outerLeaf).thetaClassLeaf characters thetaPair).exceptionalIntegrand z

/-- The actual canonical first allowance is positive in either of the
original Cauchy orientations. -/
theorem firstAllowanceAt_canonical_pos : 0 < R.firstAllowanceAt L total i.val := by
  sorry

/-- The actual original two orbital fibres and the first Cauchy half
form a nonnegative outer factor. -/
theorem originalScalarAt_nonneg (key : R.CoveredLeafKey L) :
    0 ≤ R.originalScalarAt L key := by
  sorry

/-- The exact denominator is retained until the already proved
second-source estimate is used. No natural-width substitution occurs. -/
theorem stripOuter_theta_pointwise
    (parentWidth firstCost secondCost remaining lower tilt : ℝ)
    (hfirstCost : 0 ≤ firstCost)
    (hfirst : (s.pools i.val.1 i.val.2.1).weightBound *
        (‖leftScalar‖ * ‖rightScalar‖) ≤
      firstCost * Z ^ (parentWidth - total i.val.1 i.val.2.1 + tilt))
    (hsecond : magnitude / R.firstAllowanceAt L total i.val ≤
      secondCost * Z ^ remaining /
        (Ideal.absNorm (commonRadical (R.commonLabel L i.val).1
          (R.commonLabel L i.val).2) : ℝ) * Z ^ (-lower)) :
    ((outerLeaf).weight / Z ^ parentWidth) * magnitude ≤
      R.originalScalarAt L i.val *
        (firstCost * secondCost * Z ^ (remaining + tilt) *
          (labels).carrier.exceptionalDyadWeight Z lower j) := by
  sorry

end ActualFirstSource.SecondStages


namespace OriginalArithmeticLabels

variable {I : Type*} [Fintype I] {cap : ℕ}
variable (labels : OriginalArithmeticLabels K I cap)
variable (tag : I → Option (ℕ × ExteriorPrime A))
variable (tag_mem : ∀ i n p, tag i = some (n, p) →
  n ∈ ({1, 6, 7} : Finset ℕ) ∧ p ∈ P.primes)

/-- The actual tag partition retains every original coordinate in its
exceptional dyad weight, including the full padded allocation label. -/
theorem amplified_exceptionalDyadWeight_eq (lower : ℝ) (i : I) :
    AmplifiedCommonIndex.dyadWeight P (labels.mainCarrier tag) (labels.errorCarrier tag)
      lower (labels.amplifiedIndex tag P tag_mem i) =
        labels.carrier.exceptionalDyadWeight Z lower (labels.index i) := by
  sorry

end OriginalArithmeticLabels

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.firstAllowanceAt_canonical_pos
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.originalScalarAt_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.stripOuter_theta_pointwise

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.firstAllowanceAt_canonical_pos
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.originalScalarAt_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.stripOuter_theta_pointwise
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.amplified_exceptionalDyadWeight_eq
