import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalPaidIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantRowWeightOuter
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstCombinedAllowance

/-!
# Pay only the first scalar pair outside the actual exceptional row

The first extraction retains the second common atoms in the original
row weight. Only the subsequent first-column scalar extraction moves
outside the row sum. This distinction preserves the actual row-mass
factory, and pays the first scalar pair together with the original first
Poisson profile. Both original Fourier kernels remain unchanged.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField MeasureTheory CommonSupportMass
open UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]
variable {H U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

namespace ActualHybridLeaf.ConstantAtomExtraction

variable {leaf : ActualHybridLeaf K H U V} (X : leaf.ConstantAtomExtraction)
variable (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)

/-- The second common extraction remains in the row. The additional
first scalar pair is paid once in the original outer weight. -/
def stripOuter : ActualHybridLeaf K H U V :=
  (X.leaf.stripColumnConstants a b ha hb).outerLeaf

theorem exceptionalCost_eq_stripOuter :
    leaf.exceptionalCost = (X.stripOuter a b ha hb).exceptionalCost :=
  X.exceptionalCost_eq.trans
    (X.leaf.stripColumnConstants a b ha hb).exceptionalCost_eq_outerLeaf

theorem ordinaryCost_eq_stripOuter :
    leaf.ordinaryCost = (X.stripOuter a b ha hb).ordinaryCost :=
  X.ordinaryCost_eq.trans
    (X.leaf.stripColumnConstants a b ha hb).ordinaryCost_eq_outerLeaf

theorem stripOuter_weight :
    (X.stripOuter a b ha hb).weight = (‖a‖ * ‖b‖) * leaf.weight :=
  (X.leaf.stripColumnConstants a b ha hb).outerLeaf_weight

@[simp] theorem stripOuter_rowWeight :
    (X.stripOuter a b ha hb).rowWeight = X.leaf.rowWeight := rfl

@[simp] theorem stripOuter_rows : (X.stripOuter a b ha hb).rows = leaf.rows := rfl

@[simp] theorem stripOuter_firstKernel :
    (X.stripOuter a b ha hb).firstKernel = leaf.firstKernel := rfl

@[simp] theorem stripOuter_secondKernel :
    (X.stripOuter a b ha hb).secondKernel = leaf.secondKernel := rfl

@[simp] theorem stripOuter_exceptional :
    (X.stripOuter a b ha hb).exceptional = leaf.exceptional := rfl

@[simp] theorem stripOuter_leftCoefficient (h : H) (i : AllocationColumn K leaf.leftSlots) :
    (X.stripOuter a b ha hb).leftCoefficient h i = a⁻¹ * X.leftResidual h i := rfl

@[simp] theorem stripOuter_rightCoefficient (h : H) (i : AllocationColumn K leaf.rightSlots) :
    (X.stripOuter a b ha hb).rightCoefficient h i = b⁻¹ * X.rightResidual h i := rfl

end ActualHybridLeaf.ConstantAtomExtraction

namespace CanonicalExceptionalPaidIntegral

/-- The integrand is that of the same stored leaf after its two exact
extractions. The original common row factors are still inside it. -/
theorem cost_le_of_strip_outer_majorant
    (J₁ J₂ : ℕ) (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient)
    (leaf : ActualHybridLeaf K H U V) (X : leaf.ConstantAtomExtraction)
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (Z parentWidth : ℝ)
    (hpoint : ∀ z : U × V,
      (((‖a‖ * ‖b‖) * leaf.weight) / Z ^ parentWidth) *
          (X.stripOuter a b ha hb).exceptionalIntegrand z ≤
        coefficient * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) :
    leaf.exceptionalCost / Z ^ parentWidth ≤
      coefficient * fourierFactor J₁ J₂ leaf.firstKernel leaf.secondKernel := by
  rw [X.exceptionalCost_eq_stripOuter a b ha hb]
  apply cost_le_of_polynomial_majorant J₁ J₂ coefficient hcoefficient
    (X.stripOuter a b ha hb) Z parentWidth
  intro z
  rw [X.stripOuter_weight a b ha hb]
  exact hpoint z

/-- Theta classes are taken after the exact extraction; they keep the
original predicate and both original kernels. -/
theorem theta_cost_le_of_strip_outer_majorant
    (J₁ J₂ : ℕ) (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient)
    (leaf : ActualHybridLeaf K H U V) (X : leaf.ConstantAtomExtraction)
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    {theta : Finset (HeckeCharacter K)} (Q : PairedFiniteCharacters theta H)
    (hpredicate : leaf.exceptional = Q.exceptional) (Z parentWidth : ℝ)
    (hpoint : ∀ χ : theta × theta, ∀ z : U × V,
      (((‖a‖ * ‖b‖) * leaf.weight) / Z ^ parentWidth) *
          ((X.stripOuter a b ha hb).thetaClassLeaf Q χ).exceptionalIntegrand z ≤
        coefficient * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) :
    leaf.exceptionalCost / Z ^ parentWidth ≤
      (theta.card : ℝ) ^ 2 *
        (coefficient * fourierFactor J₁ J₂ leaf.firstKernel leaf.secondKernel) := by
  rw [X.exceptionalCost_eq_stripOuter a b ha hb]
  apply theta_cost_le_of_polynomial_majorant J₁ J₂ coefficient hcoefficient
    (X.stripOuter a b ha hb) Q hpredicate Z parentWidth
  intro χ z
  rw [X.stripOuter_weight a b ha hb]
  exact hpoint χ z

end CanonicalExceptionalPaidIntegral

/-- The six actual combined-profile theorems supply `hprofile`. This
internal scalar composition never requires a false bound on the raw
first Poisson profile alone. Both actual divisor and phase labels are
the original arithmetic index. -/
theorem original_exceptional_combined_label_scalar
    {branch : TwoDivisorCommonBranch (K := K)} (j : branch.Index)
    {Ray₁ Ray₂ : Type*} [CommGroup Ray₁] [Fintype Ray₁] [CommGroup Ray₂] [Fintype Ray₂]
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle)
    (Z rawProfile scalarPair firstCost secondCost total parentWidth
      magnitude secondWidth remaining lower tilt : ℝ)
    (hZ : 1 < Z) (hmagnitude : 0 ≤ magnitude) (hfirstCost : 0 ≤ firstCost)
    (hprofile : rawProfile * scalarPair ≤
      firstCost * Z ^ (parentWidth - total + tilt))
    (hD : j.1.val.1.1 ≠ 0) (hE : j.1.val.1.2 ≠ 0)
    (hsupport : primeSupport j.1.val.1.1 = primeSupport j.1.val.1.2)
    (hsecond : magnitude / Z ^ secondWidth ≤ secondCost * Z ^ remaining /
      (Ideal.absNorm (commonRadical j.2.2.1.val.1.1 j.2.2.1.val.1.2) : ℝ) * Z ^ (-lower)) :
    (firstOriginalAllowanceWeight Z parentWidth total rawProfile
        j.1.val.1.1 j.1.val.1.2 * scalarPair) *
      ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
      ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖ *
      (magnitude / Z ^ secondWidth) ≤
        firstCost * secondCost * Z ^ (remaining + tilt) *
          branch.exceptionalDyadWeight Z lower j := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hfirst := firstOriginalAllowanceWeight_mul_le_radical
    Z parentWidth total rawProfile scalarPair firstCost tilt hZ hfirstCost hprofile
    j.1.val.1.1 j.1.val.1.2 hD hE hsupport
  have hb := original_exceptional_label_scalar j phase₁ χ₁ phase₂ χ₂
    Z (firstOriginalAllowanceWeight Z parentWidth total rawProfile
      j.1.val.1.1 j.1.val.1.2 * scalarPair)
    magnitude (firstCost * Z ^ tilt) secondCost secondWidth remaining lower
    hz hmagnitude (mul_nonneg hfirstCost (Real.rpow_nonneg hz.le _)) hfirst hsecond
  apply hb.trans_eq
  rw [Real.rpow_add hz]
  ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ConstantAtomExtraction.exceptionalCost_eq_stripOuter
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral.theta_cost_le_of_strip_outer_majorant
#print axioms HeckeSkeleton.Moments.EngineStep.original_exceptional_combined_label_scalar
