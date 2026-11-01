import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedHybridLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantCommonLeaf

/-!
# The same normalization through the actual outer scalar factors

The original physical fibre, pool density and first divisor weights
multiply only a leaf's outer weight. All rows, coefficients, Fourier
locations, kernels and exceptional predicates are unchanged. Constant
extraction therefore commutes with this operation, and its actual
normalization keeps the same arithmetic frames and normalized family.

These operations do not construct another capacity child. The family,
its chosen children, its weights and both Fourier measures are the
original values. The scalar is paid once in the outer weight.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {H : Type} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace ActualHybridLeaf

variable (leaf : ActualHybridLeaf K H U E)

@[simp] theorem scale_firstKernel (a : ℝ) (ha : 0 ≤ a) :
    (leaf.scale a ha).firstKernel = leaf.firstKernel := rfl

@[simp] theorem scale_secondKernel (a : ℝ) (ha : 0 ≤ a) :
    (leaf.scale a ha).secondKernel = leaf.secondKernel := rfl

@[simp] theorem scale_measure (a : ℝ) (ha : 0 ≤ a) :
    (leaf.scale a ha).measure = leaf.measure := rfl

namespace ConstantAtomExtraction

variable {leaf} (X : leaf.ConstantAtomExtraction)

/-- Extract the same two literal constants after multiplying the
original outer weight. All individual coefficient identities persist. -/
def scale (a : ℝ) (ha : 0 ≤ a) : (leaf.scale a ha).ConstantAtomExtraction where
  leftScalar := X.leftScalar
  rightScalar := X.rightScalar
  leftResidual := X.leftResidual
  rightResidual := X.rightResidual
  left := X.left
  right := X.right

@[simp] theorem scale_leaf (a : ℝ) (ha : 0 ≤ a) :
    (X.scale a ha).leaf = X.leaf.scale a ha := rfl

end ConstantAtomExtraction

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {ω ψ : HeckeCharacter K} {Z : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}

namespace NormalizationData

variable {leaf}
variable (N : leaf.NormalizationData (ι := ι) C Ray ω ψ Z
  rowDomain heightDomain window seminorms)

/-- Only the leaf parameter changes its outer weight. Every field
which constructs the normalized family is copied literally. -/
def scale (a : ℝ) (ha : 0 ≤ a) :
    (leaf.scale a ha).NormalizationData (ι := ι) C Ray ω ψ Z
      rowDomain heightDomain window seminorms where
  rows := N.rows
  leftPlain₁ := N.leftPlain₁
  leftPlain₂ := N.leftPlain₂
  leftPrimes := N.leftPrimes
  rightPlain₁ := N.rightPlain₁
  rightPlain₂ := N.rightPlain₂
  rightPrimes := N.rightPrimes
  leftIdeal := N.leftIdeal
  rightIdeal := N.rightIdeal
  leftRay := N.leftRay
  rightRay := N.rightRay
  leftWhole := N.leftWhole
  rightWhole := N.rightWhole
  leftPoint := N.leftPoint
  rightPoint := N.rightPoint
  branch := N.branch
  rectangles := N.rectangles
  binding := {
    rows := N.binding.rows
    rows_zero := N.binding.rows_zero
    left := N.binding.left
    right := N.binding.right
    exceptional := N.binding.exceptional
    rowWeight := N.binding.rowWeight
    leftCoefficient := N.binding.leftCoefficient
    rightCoefficient := N.binding.rightCoefficient
    leftPoint := N.binding.leftPoint
    rightPoint := N.binding.rightPoint }
  left := N.left
  right := N.right
  left_base := N.left_base
  right_base := N.right_base
  left_height := N.left_height
  right_height := N.right_height

@[simp] theorem scale_family (a : ℝ) (ha : 0 ≤ a) :
    (N.scale a ha).family = N.family := rfl

@[simp] theorem scale_left (a : ℝ) (ha : 0 ≤ a) (r : Bool) :
    (N.scale a ha).left r = N.left r := rfl

@[simp] theorem scale_right (a : ℝ) (ha : 0 ≤ a) (r : Bool) :
    (N.scale a ha).right r = N.right r := rfl

@[simp] theorem scale_leftChild (a : ℝ) (ha : 0 ≤ a)
    (labels : Finset (Bool × Bool)) (b : N.family.active labels) :
    (N.scale a ha).family.leftChild labels b = N.family.leftChild labels b := rfl

@[simp] theorem scale_rightChild (a : ℝ) (ha : 0 ≤ a)
    (labels : Finset (Bool × Bool)) (b : N.family.active labels) :
    (N.scale a ha).family.rightChild labels b = N.family.rightChild labels b := rfl

@[simp] theorem scale_family_weight (a : ℝ) (ha : 0 ≤ a)
    (labels : Finset (Bool × Bool)) (parentWidth : ℝ) (b : N.family.active labels) :
    (N.scale a ha).family.weight labels parentWidth b =
      N.family.weight labels parentWidth b := rfl

/-- The physical fibre or divisor factor is paid exactly once in the
outer weight of the same selected child pair. -/
theorem scale_outer_weight_mul (a : ℝ) (ha : 0 ≤ a)
    (labels : Finset (Bool × Bool)) (parentWidth : ℝ) (b : N.family.active labels) :
    (leaf.scale a ha).weight * (N.scale a ha).family.weight labels parentWidth b =
      a * (leaf.weight * N.family.weight labels parentWidth b) := by
  change (a * leaf.weight) * N.family.weight labels parentWidth b = _
  ring

end NormalizationData

namespace ConstantAtomExtraction

variable {leaf} (X : leaf.ConstantAtomExtraction)
variable (N : X.leaf.NormalizationData (ι := ι) C Ray ω ψ Z
  rowDomain heightDomain window seminorms)

/-- The actual extraction and normalization scale together, so no
equality transport or new choice of normalized children is needed. -/
def scaleNormalization (a : ℝ) (ha : 0 ≤ a) :
    (X.scale a ha).leaf.NormalizationData (ι := ι) C Ray ω ψ Z
      rowDomain heightDomain window seminorms :=
  N.scale a ha

@[simp] theorem scaleNormalization_family (a : ℝ) (ha : 0 ≤ a) :
    (X.scaleNormalization N a ha).family = N.family := rfl

end ConstantAtomExtraction
end ActualHybridLeaf
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ConstantAtomExtraction.scale_leaf
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.scale_family
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.scale_leftChild
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.scale_rightChild
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.scale_outer_weight_mul
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ConstantAtomExtraction.scaleNormalization_family
