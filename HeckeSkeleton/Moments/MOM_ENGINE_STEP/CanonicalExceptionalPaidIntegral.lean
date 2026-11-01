import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafExceptionalBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalThetaPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalWindows

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
    0 ≤ fourierFactor J₁ J₂ F₁ F₂ :=
  mul_nonneg
    (mul_nonneg
      (exceptionalFourierControl (U := U) (E := E) J₁ J₂).constant_pos.le
      (apply_nonneg _ F₁)) (apply_nonneg _ F₂)

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
  have hsource := leaf.exceptionalIntegrand_integrable.const_mul
    (leaf.weight / Z ^ parentWidth)
  have hmajor :=
    (nestedFourierMeasure_mixed_polynomial_integrable
      leaf.firstKernel leaf.secondKernel J₁ J₂).const_mul coefficient
  calc
    _ = ∫ z : U × E,
        (leaf.weight / Z ^ parentWidth) * leaf.exceptionalIntegrand z ∂leaf.measure := by
      rw [integral_const_mul]
      unfold ActualHybridLeaf.exceptionalCost
      ring
    _ ≤ ∫ z : U × E,
        coefficient * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂) ∂leaf.measure :=
      integral_mono hsource hmajor hpoint
    _ = coefficient * ∫ z : U × E,
        (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂ ∂leaf.measure :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((exceptionalFourierControl (U := U) (E := E) J₁ J₂).bound
        leaf.firstKernel leaf.secondKernel) hcoefficient

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
  rw [leaf.exceptionalCost_eq_theta_sum Q hpredicate, Finset.sum_div]
  calc
    _ ≤ ∑ _χ : theta × theta,
        coefficient * fourierFactor J₁ J₂ leaf.firstKernel leaf.secondKernel := by
      apply Finset.sum_le_sum
      intro χ _
      exact cost_le_of_polynomial_majorant J₁ J₂ coefficient hcoefficient
        (leaf.thetaClassLeaf Q χ) Z parentWidth (hpoint χ)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_prod, Fintype.card_coe, Nat.cast_mul, pow_two]

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
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hC0 : 0 ≤ coefficient * P ^ degree * Z ^ loss * indexWeight :=
    mul_nonneg (mul_nonneg (mul_nonneg hcoefficient (pow_nonneg hP0 _))
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hindex
  have hf : fourierFactor J₁ J₂ leaf.firstKernel leaf.secondKernel ≤
      (exceptionalFourierControl (U := U) (E := E) J₁ J₂).constant *
        (leftConstant * P ^ leftDegree) * (rightConstant * P ^ rightDegree) := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hleft
        (exceptionalFourierControl (U := U) (E := E) J₁ J₂).constant_pos.le)
      hright (apply_nonneg _ leaf.secondKernel)
      (mul_nonneg
        (exceptionalFourierControl (U := U) (E := E) J₁ J₂).constant_pos.le
        (mul_nonneg hleftConstant (pow_nonneg hP0 _)))
  have hcost := theta_cost_le_of_polynomial_majorant J₁ J₂
    (coefficient * P ^ degree * Z ^ loss * indexWeight) hC0
    leaf Q hpredicate Z parentWidth hpoint
  apply hcost.trans
  calc
    _ ≤ (theta.card : ℝ) ^ 2 *
        ((coefficient * P ^ degree * Z ^ loss * indexWeight) *
          ((exceptionalFourierControl (U := U) (E := E) J₁ J₂).constant *
            (leftConstant * P ^ leftDegree) * (rightConstant * P ^ rightDegree))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf hC0) (sq_nonneg _)
    _ = _ := by simp only [pow_add]; ring

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
  rw [X.exceptionalCost_eq]
  apply cost_le_of_polynomial_majorant J₁ J₂ coefficient hcoefficient
    X.leaf Z parentWidth
  intro z
  rw [binding.exceptionalIntegrand_eq z]
  exact hpoint z

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
  have htime : 0 ≤ (1 + 2 * Real.pi) ^ order :=
    pow_nonneg (by positivity) _
  apply theta_cost_le_of_polynomial_majorant (J₁ * degree + order)
    (J₂ * degree + order) (coefficient * (1 + 2 * Real.pi) ^ order * P ^ degree)
    (mul_nonneg (mul_nonneg hcoefficient htime) (pow_nonneg hP _))
    leaf Q hpredicate Z parentWidth
  intro χ z
  have hp := CanonicalLiteralExceptionalWindows.profile_time_polynomial
    P hP degree J₁ J₂ order (WithLp.toLp 2 z)
  simp only [WithLp.ofLp_toLp] at hp
  calc
    _ ≤ coefficient * ((P * (1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂) ^ degree *
        (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ order) :=
      (hpoint χ z).trans_eq (by ring)
    _ ≤ coefficient * ((1 + 2 * Real.pi) ^ order * P ^ degree *
        (1 + ‖z.1‖) ^ (J₁ * degree + order) *
        (1 + ‖z.2‖) ^ (J₂ * degree + order)) :=
      mul_le_mul_of_nonneg_left hp hcoefficient
    _ = _ := by ring

end HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral.cost_le_of_polynomial_majorant
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral.theta_cost_le_of_polynomial_majorant
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral.uniform_theta_cost_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral.cost_le_of_extracted_frame_majorant
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalPaidIntegral.theta_cost_le_of_profile_time_majorant
