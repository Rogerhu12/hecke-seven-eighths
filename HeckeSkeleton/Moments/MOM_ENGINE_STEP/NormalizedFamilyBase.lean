import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedChildren

/-!
# An exact base identity for the same normalized family

Only the two proofs recording the common base change. All sources,
calibrations, capacity inputs, active labels and chosen children are
the original objects.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree HeckeGeneral.Characters

namespace ActualNormalizedPairFamily

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter K} {Z : ℝ}
variable (s : ActualNormalizedPairFamily A σ V Λ ω ψ Z)

def atBase (base : ℝ) (sameBase : Z = base) :
    ActualNormalizedPairFamily A σ V Λ ω ψ base where
  LeftRow := s.LeftRow
  RightRow := s.RightRow
  leftSlots := s.leftSlots
  rightSlots := s.rightSlots
  leftSource := s.leftSource
  rightSource := s.rightSource
  leftCalibration := s.leftCalibration
  rightCalibration := s.rightCalibration
  leftCapacity := s.leftCapacity
  rightCapacity := s.rightCapacity
  left_base b := (s.left_base b).trans sameBase
  right_base b := (s.right_base b).trans sameBase
  leftNormalizer := s.leftNormalizer
  rightNormalizer := s.rightNormalizer

variable (base : ℝ) (sameBase : Z = base) (labels : Finset Λ)

@[simp] theorem atBase_active : (s.atBase base sameBase).active labels = s.active labels := rfl

@[simp] theorem atBase_leftChild (b : s.active labels) :
    (s.atBase base sameBase).leftChild labels b = s.leftChild labels b := rfl

@[simp] theorem atBase_rightChild (b : s.active labels) :
    (s.atBase base sameBase).rightChild labels b = s.rightChild labels b := rfl

@[simp] theorem atBase_leftData (b : s.active labels) (ξ : V) :
    (s.atBase base sameBase).leftData labels b ξ = s.leftData labels b ξ := rfl

@[simp] theorem atBase_rightData (b : s.active labels) (ξ : V) :
    (s.atBase base sameBase).rightData labels b ξ = s.rightData labels b ξ := rfl

theorem atBase_weight (parentWidth : ℝ) (b : s.active labels) :
    (s.atBase base sameBase).weight labels parentWidth b = s.weight labels parentWidth b := by
  subst base
  rfl

end ActualNormalizedPairFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.atBase
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.atBase_leftChild
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.atBase_weight
