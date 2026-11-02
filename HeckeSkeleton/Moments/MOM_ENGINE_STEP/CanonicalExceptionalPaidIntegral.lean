import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafExceptionalBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalThetaPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalWindows

set_option linter.unusedSectionVars false

/-!
# Integrate the paid exceptional estimate on the original leaf

These are internal composition lemmas for the pointwise estimates
proved by the literal exceptional factories.  They are not analytic
inputs to the engine theorem.  The finite source proves integrability;
weighted Fourier L1 supplies its own fixed seminorms and constant.

Both original kernels, the original outer weight, and the original
parent normalization are retained.  Constant common-atom extraction
is transported by its exact identity.  The finite theta partition
costs only the square of the original theta cardinality, using one
uniform coefficient chosen before the moving profiles.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral

open NumberField DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The two kernels are evaluated at the seminorms fixed solely by
the two polynomial orders. No moving profile is hidden in a choice. -/
def fourierFactor (J₁ J₂ : ℕ) (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) : ℝ :=
  (exceptionalFourierControl (U := U) (E := E) J₁ J₂).constant *
    (exceptionalFourierControl (U := U) (E := E) J₁ J₂).leftSeminorms.sup
      (schwartzSeminormFamily ℝ U ℂ) F₁ *
    (exceptionalFourierControl (U := U) (E := E) J₁ J₂).rightSeminorms.sup
      (schwartzSeminormFamily ℝ E ℂ) F₂

theorem fourierFactor_nonneg (J₁ J₂ : ℕ) (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) :
    0 ≤ fourierFactor J₁ J₂ F₁ F₂ := by
  sorry

variable {K : Type} [Field K] [NumberField K] {H : Type*}

/-- Integrability is obtained from the original finite polynomial.
The premise is the pointwise conclusion of the actual source factory,
already including its outer scalar and its parent normalization. -/
theorem cost_le_of_polynomial_majorant
    (J₁ J₂ : ℕ) (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient)
    (leaf : ActualHybridLeaf K H U E) (Z parentWidth : ℝ)
    (hpoint : ∀ z : U × E,
      (leaf.weight / Z ^ parentWidth) * leaf.exceptionalIntegrand z ≤
        coefficient * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) :
    leaf.exceptionalCost / Z ^ parentWidth ≤
      coefficient * fourierFactor J₁ J₂ leaf.firstKernel leaf.secondKernel := by
  sorry

/-- The original theta classes have identical kernels and outer
weight. Their exact finite-sum identity is used before any bound. -/
theorem theta_cost_le_of_polynomial_majorant
    (J₁ J₂ : ℕ) (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient)
    (leaf : ActualHybridLeaf K H U E) {theta : Finset (HeckeCharacter K)}
    (Q : PairedFiniteCharacters theta H) (hpredicate : leaf.exceptional = Q.exceptional)
    (Z parentWidth : ℝ)
    (hpoint : ∀ χ : theta × theta, ∀ z : U × E,
      (leaf.weight / Z ^ parentWidth) * (leaf.thetaClassLeaf Q χ).exceptionalIntegrand z ≤
        coefficient * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) :
    leaf.exceptionalCost / Z ^ parentWidth ≤
      (theta.card : ℝ) ^ 2 *
        (coefficient * fourierFactor J₁ J₂ leaf.firstKernel leaf.secondKernel) := by
  sorry

/-- Explicit original seminorm controls pay the two kernel factors.
The three constants precede the moving profile amplitude and leaf. -/
theorem uniform_theta_cost_le
    (J₁ J₂ degree leftDegree rightDegree : ℕ)
    (coefficient leftConstant rightConstant : ℝ)
    (hcoefficient : 0 ≤ coefficient) (hleftConstant : 0 ≤ leftConstant)
    (hrightConstant : 0 ≤ rightConstant)
    (leaf : ActualHybridLeaf K H U E) {theta : Finset (HeckeCharacter K)}
    (Q : PairedFiniteCharacters theta H) (hpredicate : leaf.exceptional = Q.exceptional)
    (Z parentWidth loss P indexWeight : ℝ) (hZ : 1 < Z) (hP : 1 ≤ P)
    (hindex : 0 ≤ indexWeight)
    (hleft :
      (exceptionalFourierControl (U := U) (E := E) J₁ J₂).leftSeminorms.sup
        (schwartzSeminormFamily ℝ U ℂ) leaf.firstKernel ≤ leftConstant * P ^ leftDegree)
    (hright :
      (exceptionalFourierControl (U := U) (E := E) J₁ J₂).rightSeminorms.sup
        (schwartzSeminormFamily ℝ E ℂ) leaf.secondKernel ≤ rightConstant * P ^ rightDegree)
    (hpoint : ∀ χ : theta × theta, ∀ z : U × E,
      (leaf.weight / Z ^ parentWidth) * (leaf.thetaClassLeaf Q χ).exceptionalIntegrand z ≤
        (coefficient * P ^ degree * Z ^ loss * indexWeight) *
          ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) :
    leaf.exceptionalCost / Z ^ parentWidth ≤
      ((theta.card : ℝ) ^ 2 * coefficient *
        (exceptionalFourierControl (U := U) (E := E) J₁ J₂).constant *
          leftConstant * rightConstant) * P ^ (degree + leftDegree + rightDegree) *
        Z ^ loss * indexWeight := by
  sorry

section ActualFrames

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]

/-- The exact common-atom extraction and individual atom binding
transport a proved frame magnitude bound to the original leaf.  The
common scalars remain in the row mass, and are never charged again. -/
theorem cost_le_of_extracted_frame_majorant
    (J₁ J₂ : ℕ) (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient)
    (leaf : ActualHybridLeaf K H U E) (X : leaf.ConstantAtomExtraction)
    (left : SecondSideFrame (V := WithLp 2 (U × E)) C R Ray .left X.leaf.leftSlots)
    (right : SecondSideFrame (V := WithLp 2 (U × E)) C R Ray .right X.leaf.rightSlots)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    {theta : Finset (HeckeCharacter K)} (Q : PairedFiniteCharacters theta H)
    (binding : X.leaf.ExceptionalBinding left right EL ER Q)
    (Z parentWidth : ℝ)
    (hpoint : ∀ z : U × E,
      (leaf.weight / Z ^ parentWidth) *
          left.exceptionalMagnitude right EL ER Q (WithLp.toLp 2 z) ≤
        coefficient * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂)) :
    leaf.exceptionalCost / Z ^ parentWidth ≤
      coefficient * fourierFactor J₁ J₂ leaf.firstKernel leaf.secondKernel := by
  sorry

end ActualFrames

/-- The literal real Fourier height is paid by the two original
polynomial orders. The amplitude P remains an explicit power. -/
theorem theta_cost_le_of_profile_time_majorant
    (degree J₁ J₂ order : ℕ) (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient)
    (leaf : ActualHybridLeaf K H ℝ ℝ) {theta : Finset (HeckeCharacter K)}
    (Q : PairedFiniteCharacters theta H) (hpredicate : leaf.exceptional = Q.exceptional)
    (Z parentWidth P : ℝ) (hP : 0 ≤ P)
    (hpoint : ∀ χ : theta × theta, ∀ z : ℝ × ℝ,
      (leaf.weight / Z ^ parentWidth) * (leaf.thetaClassLeaf Q χ).exceptionalIntegrand z ≤
        coefficient * (P * (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂) ^ degree *
          (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ order) :
    leaf.exceptionalCost / Z ^ parentWidth ≤
      (theta.card : ℝ) ^ 2 *
        ((coefficient * (1 + 2 * Real.pi) ^ order * P ^ degree) *
          fourierFactor (J₁ * degree + order) (J₂ * degree + order)
            leaf.firstKernel leaf.secondKernel) := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral.cost_le_of_polynomial_majorant
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral.theta_cost_le_of_polynomial_majorant
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral.uniform_theta_cost_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral.cost_le_of_extracted_frame_majorant
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral.theta_cost_le_of_profile_time_majorant
