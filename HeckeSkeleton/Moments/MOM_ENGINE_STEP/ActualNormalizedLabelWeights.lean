import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedCapacityMassBridge
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedOriginalLabelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOrdinaryWeights

/-!
# Original arithmetic label bounds for the same selected rectangle

The two children are the literal projections of the existing family
after the original arithmetic costs are chosen. The original length
and atom windows, the actual ideal-index identities and the original
first-profile bound instantiate the pointwise arithmetic theorem.

The outer-weight theorem additionally uses the exact scalar identity
computed by CanonicalOrdinaryWeights. It does not assume an outer
weight estimate, an energy comparison or a total mass bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {H : Type} {ι U E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ω ψ : HeckeCharacter K}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {Z : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}

namespace ActualHybridLeaf.NormalizationData

variable {leaf : ActualHybridLeaf K H U E}
variable (N : leaf.NormalizationData (ι := ι) C Ray ω ψ Z
  rowDomain heightDomain window seminorms)
variable {kLeft kRight : ℕ}
variable (W : ActualSecondRowMass (N.rows.restrictRows (fun h => ¬leaf.exceptional h))
  C kLeft kRight)
variable (BL : ∀ r, (N.rectangles.leftFrame C r).source.FrozenAtomBounds)
variable (BR : ∀ r, (N.rectangles.rightFrame C r).source.FrozenAtomBounds)
variable (b : (N.withArithmeticCosts W BL BR).family.active Finset.univ)
variable {firstNormalization remaining : ℝ}
variable (L : OriginalPairAllowanceWindow
  (N.rectangles.leftFrame C b.val.1) (N.rectangles.rightFrame C b.val.2)
  (N.left b.val.1).calibration (N.right b.val.2).calibration W
  (BL b.val.1) (BR b.val.2)
  ((N.withArithmeticCosts W BL BR).left b.val.1).capacity
  ((N.withArithmeticCosts W BL BR).right b.val.2).capacity
  Z firstNormalization remaining)
variable {branch : TwoDivisorCommonBranch (K := K)}
variable {Ray₁ Ray₂ : Type*}
  [CommGroup Ray₁] [Fintype Ray₁] [CommGroup Ray₂] [Fintype Ray₂]

/-- Both children and the zero-parent-width pair weight are projections
of the same actual family. All hypotheses concern original scalar
windows or the literal arithmetic coordinates. -/
theorem arithmeticCosts_family_original_index_weight
    (hZ : 1 < Z) (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (atoms : CanonicalCapacityKernelMass.OriginalAtomWindow
      (N.rectangles.leftFrame C b.val.1) (N.rectangles.rightFrame C b.val.2)
      W (BL b.val.1) (BR b.val.2) (N.left b.val.1).bounds (N.right b.val.2).bounds cap B)
    (j : branch.Index)
    (hleft : W.leftIdeal = j.2.2.1.val.1.1)
    (hright : W.rightIdeal = j.2.2.1.val.1.2)
    (hdivisor : (N.rectangles.leftFrame C b.val.1).source.allocation.divisor = j.2.2.2.1.val)
    (parentWidth total rawProfile firstCost : ℝ)
    (hfirst : 0 ≤ firstCost)
    (hprofile : rawProfile ≤ firstCost * Z ^ (parentWidth - total))
    (hD : j.1.val.1.1 ≠ 0) (hE : j.1.val.1.2 ≠ 0)
    (hsupport : primeSupport j.1.val.1.1 = primeSupport j.1.val.1.2)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle) :
    (firstOriginalAllowanceWeight Z parentWidth total rawProfile j.1.val.1.1 j.1.val.1.2 *
      ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
      ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖) *
      ((N.withArithmeticCosts W BL BR).family.weight Finset.univ 0 b / firstNormalization) ≤
      firstCost * ((W.originalFiber : ℝ) * B ^ (3 * cap + 1) * orbitalFieldFactor K) *
        Z ^ remaining * branch.indexWeight j :=
  normalized_pair_original_index_weight
    (N.rectangles.leftFrame C b.val.1) (N.rectangles.rightFrame C b.val.2)
    (N.left b.val.1).calibration (N.right b.val.2).calibration W
    (BL b.val.1) (BR b.val.2)
    ((N.withArithmeticCosts W BL BR).left b.val.1).capacity
    ((N.withArithmeticCosts W BL BR).right b.val.2).capacity
    (N.left b.val.1).amplitude (N.right b.val.2).amplitude
    (N.left b.val.1).amplitude_pos (N.right b.val.2).amplitude_pos
    (N.left b.val.1).bounds (N.right b.val.2).bounds
    (N.left b.val.1).bounds_nonneg (N.right b.val.2).bounds_nonneg
    (N.left b.val.1).factor (N.right b.val.2).factor
    ((N.withArithmeticCosts W BL BR).family.leftChild Finset.univ b)
    ((N.withArithmeticCosts W BL BR).family.rightChild Finset.univ b)
    L hZ cap B hB atoms j hleft hright hdivisor
    parentWidth total rawProfile firstCost hfirst hprofile hD hE hsupport phase₁ χ₁ phase₂ χ₂

/-- The actual original leaf scalar is inserted by equality. The
nonnegative remaining scalar can be its original pool/tag/fibre factor;
no pointwise label-weight upper bound is supplied as a premise. -/
theorem arithmeticCosts_family_outer_index_weight
    (hZ : 1 < Z) (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (atoms : CanonicalCapacityKernelMass.OriginalAtomWindow
      (N.rectangles.leftFrame C b.val.1) (N.rectangles.rightFrame C b.val.2)
      W (BL b.val.1) (BR b.val.2) (N.left b.val.1).bounds (N.right b.val.2).bounds cap B)
    (j : branch.Index)
    (hleft : W.leftIdeal = j.2.2.1.val.1.1)
    (hright : W.rightIdeal = j.2.2.1.val.1.2)
    (hdivisor : (N.rectangles.leftFrame C b.val.1).source.allocation.divisor = j.2.2.2.1.val)
    (parentWidth total rawProfile firstCost : ℝ)
    (hfirst : 0 ≤ firstCost)
    (hprofile : rawProfile ≤ firstCost * Z ^ (parentWidth - total))
    (hD : j.1.val.1.1 ≠ 0) (hE : j.1.val.1.2 ≠ 0)
    (hsupport : primeSupport j.1.val.1.1 = primeSupport j.1.val.1.2)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle)
    (factor : ℝ) (hfactor : 0 ≤ factor)
    (houter : leaf.weight / Z ^ parentWidth =
      factor *
        (firstOriginalAllowanceWeight Z parentWidth total rawProfile j.1.val.1.1 j.1.val.1.2 *
          ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
          ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖) /
        firstNormalization) :
    leaf.weight * (N.withArithmeticCosts W BL BR).family.weight Finset.univ parentWidth b ≤
      factor * (firstCost * ((W.originalFiber : ℝ) * B ^ (3 * cap + 1) * orbitalFieldFactor K) *
        Z ^ remaining * branch.indexWeight j) := by
  have h := N.arithmeticCosts_family_original_index_weight W BL BR b L
    hZ cap B hB atoms j hleft hright hdivisor parentWidth total rawProfile firstCost
    hfirst hprofile hD hE hsupport phase₁ χ₁ phase₂ χ₂
  calc
    _ = (leaf.weight / Z ^ parentWidth) *
        (N.withArithmeticCosts W BL BR).family.weight Finset.univ 0 b :=
      normalizedCapacityPairWeight_outer_parent_zero
        ((N.withArithmeticCosts W BL BR).family.leftChild Finset.univ b)
        ((N.withArithmeticCosts W BL BR).family.rightChild Finset.univ b)
        ((N.withArithmeticCosts W BL BR).family.leftNormalizer b.val)
        ((N.withArithmeticCosts W BL BR).family.rightNormalizer b.val)
        Z parentWidth leaf.weight
    _ = factor *
        ((firstOriginalAllowanceWeight Z parentWidth total rawProfile j.1.val.1.1 j.1.val.1.2 *
          ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
          ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖) *
            ((N.withArithmeticCosts W BL BR).family.weight Finset.univ 0 b /
              firstNormalization)) := by rw [houter]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hfactor

end ActualHybridLeaf.NormalizationData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.arithmeticCosts_family_original_index_weight
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.arithmeticCosts_family_outer_index_weight
