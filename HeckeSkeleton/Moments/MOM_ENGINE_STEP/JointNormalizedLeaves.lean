import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointRowBudgetProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RowBudgetPreservation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedHybridGeometry

/-!
# The actual live leaves produce admissible filtered children

Each of the four raw ordinary side dictionaries is first filtered by
its original joint row/moving-support budget. The normalized capacity
producer is then run on that calibration. Its literal source, original
Fourier kernels, coefficients, fixed geometry and arithmetic costs are
retained. The resulting family satisfies both the fixed profile window
and the actual combined row/deletion budget.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H : Type} {U E : Type*}
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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {leaf : ActualHybridLeaf K H U E}
variable (N : leaf.NormalizationData (ι := ι) C Ray ω ψ Z
  rowDomain heightDomain window seminorms)

/-- Each budget is a statement about one original source row before
extraction. No property of a chosen child is requested. -/
structure JointRowInput where
  leftMask : ∀ r, ActualMovingMaskRecipe A (N.left r).calibration.data
  rightMask : ∀ r, ActualMovingMaskRecipe A (N.right r).calibration.data
  left_budget : ∀ r, ∀ h ∈ (N.rectangles.leftFrame C r).source.rows,
    A.exteriorNorm ((N.rectangles.leftFrame C r).source.originalIdeal h) *
      A.exteriorNorm ((leftMask r).support ((N.rectangles.leftFrame C r).source.row h).momentIdeal) ≤
        (N.rectangles.leftFrame C r).source.normFactor h *
          (N.rectangles.leftFrame C r).source.base ^
            ((N.left r).calibration.parameters.m + (N.left r).calibration.parameters.q)
  right_budget : ∀ r, ∀ h ∈ (N.rectangles.rightFrame C r).source.rows,
    A.exteriorNorm ((N.rectangles.rightFrame C r).source.originalIdeal h) *
      A.exteriorNorm ((rightMask r).support ((N.rectangles.rightFrame C r).source.row h).momentIdeal) ≤
        (N.rectangles.rightFrame C r).source.normFactor h *
          (N.rectangles.rightFrame C r).source.base ^
            ((N.right r).calibration.parameters.m + (N.right r).calibration.parameters.q)

variable (J : N.JointRowInput)

/-- The same finite source is now calibrated by the actual filtered
moment data. Capacity deletion is chosen only after this construction. -/
def withJointRows : leaf.NormalizationData (ι := ι) C Ray ω ψ Z
    rowDomain heightDomain window seminorms :=
  { N with
    left r := (N.left r).withJointRowBudget (J.leftMask r) (J.left_budget r)
    right r := (N.right r).withJointRowBudget (J.rightMask r) (J.right_budget r)
    left_height := N.left_height
    right_height := N.right_height }

theorem joint_family_admissible
    (b : (N.withJointRows J).family.active Finset.univ) (ξ : WithLp 2 (U × E)) :
    EngineChildAdmissible A rowDomain window seminorms Z
      ((N.withJointRows J).family.leftData Finset.univ b ξ)
      ((N.withJointRows J).family.leftParameters Finset.univ b) ∧
    EngineChildAdmissible A rowDomain window seminorms Z
      ((N.withJointRows J).family.rightData Finset.univ b ξ)
      ((N.withJointRows J).family.rightParameters Finset.univ b) := by
  have hw := (N.withJointRows J).in_fixed_window b ξ
  constructor
  · refine ⟨hw.1, ?_⟩
    have h := (N.left b.val.1).calibration.filtered_normalized_child_admissible
      (J.leftMask b.val.1) (J.left_budget b.val.1)
      ((N.withJointRows J).family.leftChild Finset.univ b) ξ
    rw [N.left_base b.val.1] at h
    exact h
  · refine ⟨hw.2, ?_⟩
    have h := (N.right b.val.2).calibration.filtered_normalized_child_admissible
      (J.rightMask b.val.2) (J.right_budget b.val.2)
      ((N.withJointRows J).family.rightChild Finset.univ b) ξ
    rw [N.right_base b.val.2] at h
    exact h

def ParentGeometry.withJointRows {d : MomentData K ω ψ} {a : RealParameters} {step : ℝ}
    (raw : N.ParentGeometry d a step) : (N.withJointRows J).ParentGeometry d a step where
  left_parent := raw.left_parent
  right_parent := raw.right_parent
  left_gap := raw.left_gap
  right_gap := raw.right_gap
  left_kappa := raw.left_kappa
  right_kappa := raw.right_kappa
  left_slots := raw.left_slots
  right_slots := raw.right_slots
  left_theta := raw.left_theta
  right_theta := raw.right_theta

end ActualHybridLeaf.NormalizationData

namespace ActualHybridFamily

variable {J : Type*} [Fintype J]
variable {I : J → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable (leaves : J → ActualHybridLeaf K H U E)
variable (N : ∀ j, (leaves j).NormalizationData (ι := I j)
  C Ray ω ψ Z rowDomain heightDomain window seminorms)
variable (raw : ∀ j, (N j).JointRowInput)

/-- These are precisely the normalizations used by the original
parent-to-child theorem, with the row budget installed internally. -/
def jointNormalizations (j : J) := (N j).withJointRows (raw j)

theorem joint_family_admissible
    (b : (normalizedFamily leaves (jointNormalizations leaves N raw)).active Finset.univ)
    (ξ : WithLp 2 (U × E)) :
    let family := normalizedFamily leaves (jointNormalizations leaves N raw)
    EngineChildAdmissible A rowDomain window seminorms Z
      (family.leftData Finset.univ b ξ) (family.leftParameters Finset.univ b) ∧
    EngineChildAdmissible A rowDomain window seminorms Z
      (family.rightData Finset.univ b ξ) (family.rightParameters Finset.univ b) := by
  exact (N b.val.1).joint_family_admissible (raw b.val.1)
    (activeRectangle leaves (jointNormalizations leaves N raw) b) ξ

def joint_parentGeometry (d : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
    (geometry : ∀ j, (N j).ParentGeometry d a step) :
    (normalizedFamily leaves (jointNormalizations leaves N raw)).ParentGeometry
      Finset.univ d a step :=
  parentGeometry leaves (jointNormalizations leaves N raw) d a step
    (fun j => ActualHybridLeaf.NormalizationData.ParentGeometry.withJointRows
      (N j) (raw j) (geometry j))

end ActualHybridFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.joint_family_admissible
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridFamily.joint_family_admissible
