import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalParentWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalIndexMass

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
  unfold firstAllowanceAt FirstBlockDirectData.SecondStages.firstAllowanceAt
  split
  · exact firstLeftAllowance_pos Z _ (zero_lt_one.trans hZ) _ _
  · exact firstRightAllowance_pos Z _ (zero_lt_one.trans hZ) _ _

/-- The actual original two orbital fibres and the first Cauchy half
form a nonnegative outer factor. -/
theorem originalScalarAt_nonneg (key : R.CoveredLeafKey L) :
    0 ≤ R.originalScalarAt L key := by
  unfold originalScalarAt FirstBlockDirectData.SecondStages.directScalarAt
  split <;> positivity

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
  have hnorm := R.firstAllowanceAt_canonical_pos L hZ total exceptional i
  have hmag : 0 ≤ magnitude / R.firstAllowanceAt L total i.val :=
    div_nonneg (((outerLeaf).thetaClassLeaf characters thetaPair).exceptionalIntegrand_nonneg z)
      hnorm.le
  have hfirstPair := actual_common_pair_properties _ _ _ _ i.val.1
  have hsecond' : (magnitude / R.firstAllowanceAt L total i.val) / Z ^ (0 : ℝ) ≤
      secondCost * Z ^ remaining /
        (Ideal.absNorm (commonRadical j.2.2.1.val.1.1 j.2.2.1.val.1.2) : ℝ) * Z ^ (-lower) := by
    simpa only [Real.rpow_zero, div_one] using hsecond
  have hb := original_exceptional_combined_label_scalar j
    (fun _ : PUnit.{1} × PUnit.{1} => (1 : Circle)) i.val.2.2.2.1
    (fun _ : PUnit.{1} × PUnit.{1} => (1 : Circle)) (R.secondPhaseAt L i.val)
    Z (s.pieces i.val.1 i.val.2.1).weightBound (‖leftScalar‖ * ‖rightScalar‖)
    firstCost secondCost (total i.val.1 i.val.2.1) parentWidth
    (magnitude / R.firstAllowanceAt L total i.val) 0 remaining lower tilt
    hZ hmag hfirstCost hfirst hfirstPair.1 hfirstPair.2.1 hfirstPair.2.2 hsecond'
  simp only [Real.rpow_zero, div_one] at hb
  have hinner := R.originalIndex_innerDivisor L hcap exceptional normalization i
  rw [hinner] at hb
  have hs := mul_le_mul_of_nonneg_left hb (R.originalScalarAt_nonneg L i.val)
  rw [R.stripOuter_parentLeaf_weight_original_relative L hZ total exceptional parentWidth
    i.val extract leftScalar rightScalar hleftScalar hrightScalar]
  convert hs using 1 <;> ring

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
  unfold firstAllowanceAt FirstBlockPoolData.SecondStages.firstAllowanceAt
  split
  · exact firstLeftAllowance_pos Z _ (zero_lt_one.trans hZ) _ _
  · exact firstRightAllowance_pos Z _ (zero_lt_one.trans hZ) _ _

/-- The actual original two orbital fibres and the first Cauchy half
form a nonnegative outer factor. -/
theorem originalScalarAt_nonneg (key : R.CoveredLeafKey L) :
    0 ≤ R.originalScalarAt L key := by
  rcases key with ⟨v, D, S, χ, key | key⟩
  · dsimp only [originalScalarAt, FirstBlockPoolData.SecondStages.poolScalarAt]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg
        (div_nonneg (by norm_num) ((s.pools v D).divisorPools.leftData S).density_pos.le)
        (((s.pools v D).divisorPools.leftData S).tagWeight_nonneg _))
        (Nat.cast_nonneg _))) (by norm_num)
  · dsimp only [originalScalarAt, FirstBlockPoolData.SecondStages.poolScalarAt]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg
        (div_nonneg (by norm_num) ((s.pools v D).divisorPools.rightData S).density_pos.le)
        (((s.pools v D).divisorPools.rightData S).tagWeight_nonneg _))
        (Nat.cast_nonneg _))) (by norm_num)

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
  have hnorm := R.firstAllowanceAt_canonical_pos L hZ total exceptional i
  have hmag : 0 ≤ magnitude / R.firstAllowanceAt L total i.val :=
    div_nonneg (((outerLeaf).thetaClassLeaf characters thetaPair).exceptionalIntegrand_nonneg z)
      hnorm.le
  have hfirstPair := actual_common_pair_properties _ _ _ _ i.val.1
  have hsecond' : (magnitude / R.firstAllowanceAt L total i.val) / Z ^ (0 : ℝ) ≤
      secondCost * Z ^ remaining /
        (Ideal.absNorm (commonRadical j.2.2.1.val.1.1 j.2.2.1.val.1.2) : ℝ) * Z ^ (-lower) := by
    simpa only [Real.rpow_zero, div_one] using hsecond
  have hb := original_exceptional_combined_label_scalar j
    (fun _ : PUnit.{1} × PUnit.{1} => (1 : Circle)) i.val.2.2.2.1
    (fun _ : PUnit.{1} × PUnit.{1} => (1 : Circle)) (R.secondPhaseAt L i.val)
    Z (s.pools i.val.1 i.val.2.1).weightBound (‖leftScalar‖ * ‖rightScalar‖)
    firstCost secondCost (total i.val.1 i.val.2.1) parentWidth
    (magnitude / R.firstAllowanceAt L total i.val) 0 remaining lower tilt
    hZ hmag hfirstCost hfirst hfirstPair.1 hfirstPair.2.1 hfirstPair.2.2 hsecond'
  simp only [Real.rpow_zero, div_one] at hb
  have hinner : j.2.2.2.1.val = R.innerDivisor L i.val :=
    R.arithmeticLabels_secondDivisor L hcap exceptional normalization i
  rw [hinner] at hb
  have hs := mul_le_mul_of_nonneg_left hb (R.originalScalarAt_nonneg L i.val)
  rw [R.stripOuter_parentLeaf_weight_original_relative L hZ total exceptional parentWidth
    i.val extract leftScalar rightScalar hleftScalar hrightScalar]
  convert hs using 1 <;> ring

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
  unfold amplifiedIndex
  split <;> rfl

end OriginalArithmeticLabels

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.firstAllowanceAt_canonical_pos
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.originalScalarAt_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.stripOuter_theta_pointwise

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.firstAllowanceAt_canonical_pos
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.originalScalarAt_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.stripOuter_theta_pointwise
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.amplified_exceptionalDyadWeight_eq
