import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExistingJointRowBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointNormalizedLeaves

/-!
# The existing normalized family already satisfies its joint row budget

The original allowed rows below already obey the same joint budget.
Consequently the existing row-filter constructors preserve the complete
side normalization and the complete two-sided normalization. Capacity
inputs, profile representatives and the subsequently chosen children
are those of this same object.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ω ψ : HeckeCharacter K}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}

namespace SecondSideNormalization

variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [Fintype ι] [DecidableEq ι]
variable {rows : ActualSecondCorrelationRows A σ H ι}
variable {side : SecondColumnSide} {k : ℕ}
variable {f : SecondSideFrame (V := V) C rows Ray side k}
variable (N : SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms)

/-- The filter retains every original allowed row. Its capacity record
copies all computational fields, and its four Schwartz representatives
are the original representatives. Thus the entire side is unchanged. -/
theorem withJointRowBudget_eq_self
    (M : ActualMovingMaskRecipe A N.calibration.data)
    (hsource : ∀ h ∈ f.source.rows,
      A.exteriorNorm (f.source.originalIdeal h) *
        A.exteriorNorm (M.support (f.source.row h).momentIdeal) ≤
          f.source.normFactor h * f.source.base ^
            (N.calibration.parameters.m + N.calibration.parameters.q))
    (hbudget : ∀ ξ u, (N.calibration.data ξ).allowedRow u →
      idealNorm K u * A.exteriorNorm (M.support u) ≤
        f.source.base ^ (N.calibration.parameters.m + N.calibration.parameters.q)) :
    N.withJointRowBudget M hsource = N := by
  have hdata : (fun ξ => jointRowBudgetData (N.calibration.data ξ) M.support
      (f.source.base ^ (N.calibration.parameters.m + N.calibration.parameters.q))) =
      N.calibration.data := by
    funext ξ
    exact jointRowBudgetData_eq_self (N.calibration.data ξ) M.support _ (hbudget ξ)
  have hclipped (ξ : V) :
      jointRowBudgetData (N.calibration.clippedData ξ) M.support
        (f.source.base ^ (N.calibration.parameters.m + N.calibration.parameters.q)) =
      N.calibration.clippedData ξ :=
    jointRowBudgetData_eq_self (N.calibration.clippedData ξ) M.support _ (hbudget ξ)
  simp only [withJointRowBudget,
    ActualAllocatedSource.Calibration.CapacityInput.withJointRowBudget,
    ActualAllocatedSource.Calibration.withJointRowBudget,
    RawProfileWindow.withJointRowBudget, hdata, hclipped]

end SecondSideNormalization

namespace ActualHybridLeaf.NormalizationData

variable {H : Type} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {leaf : ActualHybridLeaf K H U E} {Z : ℝ}
variable (N : leaf.NormalizationData (ι := ι) C Ray ω ψ Z
  rowDomain heightDomain window seminorms)

/-- These are the same original allowed-row budgets on the two sides.
The complete normalization equality also preserves the actual family,
its selected capacity children and their two Fourier kernels. -/
theorem withJointRows_eq_self (J : N.JointRowInput)
    (hleft : ∀ r ξ u, ((N.left r).calibration.data ξ).allowedRow u →
      idealNorm K u * A.exteriorNorm ((J.leftMask r).support u) ≤
        (N.rectangles.leftFrame C r).source.base ^
          ((N.left r).calibration.parameters.m + (N.left r).calibration.parameters.q))
    (hright : ∀ r ξ u, ((N.right r).calibration.data ξ).allowedRow u →
      idealNorm K u * A.exteriorNorm ((J.rightMask r).support u) ≤
        (N.rectangles.rightFrame C r).source.base ^
          ((N.right r).calibration.parameters.m + (N.right r).calibration.parameters.q)) :
    N.withJointRows J = N := by
  have hl : (fun r => (N.left r).withJointRowBudget
      (J.leftMask r) (J.left_budget r)) = N.left := by
    funext r
    exact (N.left r).withJointRowBudget_eq_self (J.leftMask r) (J.left_budget r) (hleft r)
  have hr : (fun r => (N.right r).withJointRowBudget
      (J.rightMask r) (J.right_budget r)) = N.right := by
    funext r
    exact (N.right r).withJointRowBudget_eq_self (J.rightMask r) (J.right_budget r) (hright r)
  simp only [withJointRows, hl, hr]

end ActualHybridLeaf.NormalizationData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.withJointRowBudget_eq_self
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.withJointRows_eq_self
