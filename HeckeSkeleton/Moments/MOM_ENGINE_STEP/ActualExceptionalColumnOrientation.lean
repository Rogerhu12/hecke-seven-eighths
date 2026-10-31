import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondFrameColumnSwap
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafColumnSwap
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalThetaPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryLiteralExceptionalLeaf

/-!
# Either original column supplies the exceptional terminal

This is the orientation compatible with the actual second frames.
The stored coefficients and first locations exchange places; the
second locations exchange places and change sign. The original row
weight is conjugated. Consequently both complete joint Fourier
polynomials are exchanged and conjugated, at the same Fourier pair.

Both kernels, the original rows, the exceptional predicate and the
outer scalar are unchanged. The theta labels exchange their two actual
character coordinates. The original ordinary cost is unchanged too,
so this terminal symmetry does not rerun any capacity selection or
replace the already chosen child family.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

section JointColumns

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Negating the entire original location conjugates the phase at the
same Fourier parameter. No transformation of a measure is used. -/
theorem jointPhase_neg_eq_star (ξ x : V) : jointPhase ξ (-x) = star (jointPhase ξ x) := by
  simp only [jointPhase, inner_neg_right, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj, starRingEnd_apply]

theorem jointFourierColumn_star_neg {I : Type*} (columns : Finset I)
    (c : I → ℂ) (x : I → V) (ξ : V) :
    jointFourierColumn columns (fun i => star (c i)) (fun i => -x i) ξ =
      star (jointFourierColumn columns c x ξ) := by
  simp only [jointFourierColumn, star_sum, star_mul', jointPhase_neg_eq_star]

theorem norm_jointFourierColumn_star_neg {I : Type*} (columns : Finset I)
    (c : I → ℂ) (x : I → V) (ξ : V) :
    ‖jointFourierColumn columns (fun i => star (c i)) (fun i => -x i) ξ‖ =
      ‖jointFourierColumn columns c x ξ‖ := by
  rw [jointFourierColumn_star_neg, norm_star]

end JointColumns

variable {K : Type} [Field K] [NumberField K]
variable {H : Type*} {theta : Finset (HeckeCharacter K)}

namespace PairedFiniteCharacters

variable (Q : PairedFiniteCharacters theta H)

/-- Exchange the two actual inducing characters, retaining their
original theta action and subgroup. -/
def swapColumns : PairedFiniteCharacters theta H where
  subgroup := Q.subgroup
  action := Q.action
  left := Q.right
  right := Q.left
  ratio_mem h := by
    simpa only [inv_div] using Q.subgroup.inv_mem (Q.ratio_mem h)

@[simp] theorem swapColumns_exceptional : Q.swapColumns.exceptional = Q.exceptional := by
  funext h
  exact propext (Q.right_exceptional h)

/-- The same original theta class, with its two coordinates exchanged. -/
@[simp] theorem swapColumns_thetaClass (χ : theta × theta) :
    Q.swapColumns.thetaClass (χ.2, χ.1) = Q.thetaClass χ := by
  funext h
  apply propext
  change (Q.right h = χ.2.val ∧ Q.left h = χ.1.val) ↔
    (Q.left h = χ.1.val ∧ Q.right h = χ.2.val)
  exact and_comm

end PairedFiniteCharacters

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

private theorem neg_jointPairPoint (x : U) (y : V) :
    -WithLp.toLp 2 (x, y) = WithLp.toLp 2 (-x, -y) := rfl

namespace ActualHybridLeaf

variable (B : ActualHybridLeaf K H U V)

/-- The column exchange compatible with the unchanged original
single-factor dictionaries and the actual negative frequency. -/
def terminalTranspose : ActualHybridLeaf K H U V where
  leftSlots := B.rightSlots
  rightSlots := B.leftSlots
  rows := B.rows
  left := B.right
  right := B.left
  firstKernel := B.firstKernel
  secondKernel := B.secondKernel
  weight := B.weight
  weight_nonneg := B.weight_nonneg
  rowWeight h := star (B.rowWeight h)
  leftCoefficient := B.rightCoefficient
  rightCoefficient := B.leftCoefficient
  leftFirst := B.rightFirst
  rightFirst := B.leftFirst
  leftSecond h i := -B.rightSecond h i
  rightSecond h i := -B.leftSecond h i
  exceptional := B.exceptional

@[simp] theorem terminalTranspose_firstKernel :
    B.terminalTranspose.firstKernel = B.firstKernel := rfl

@[simp] theorem terminalTranspose_secondKernel :
    B.terminalTranspose.secondKernel = B.secondKernel := rfl

@[simp] theorem terminalTranspose_measure : B.terminalTranspose.measure = B.measure := rfl

@[simp] theorem terminalTranspose_weight : B.terminalTranspose.weight = B.weight := rfl

@[simp] theorem terminalTranspose_rows : B.terminalTranspose.rows = B.rows := rfl

@[simp] theorem terminalTranspose_exceptional :
    B.terminalTranspose.exceptional = B.exceptional := rfl

private theorem transposed_left_column_norm (h : H) (ξ : WithLp 2 (U × V)) :
    ‖jointFourierColumn B.right (B.rightCoefficient h)
      (fun i => WithLp.toLp 2 (B.rightFirst h i, -B.rightSecond h i)) ξ‖ =
    ‖jointFourierColumn B.right (fun i => star (B.rightCoefficient h i))
      (fun i => WithLp.toLp 2 (-B.rightFirst h i, B.rightSecond h i)) ξ‖ := by
  simpa only [star_star, neg_jointPairPoint, neg_neg] using
    norm_jointFourierColumn_star_neg B.right (fun i => star (B.rightCoefficient h i))
      (fun i => WithLp.toLp 2 (-B.rightFirst h i, B.rightSecond h i)) ξ

private theorem transposed_right_column_norm (h : H) (ξ : WithLp 2 (U × V)) :
    ‖jointFourierColumn B.left (fun i => star (B.leftCoefficient h i))
      (fun i => WithLp.toLp 2 (-B.leftFirst h i, -B.leftSecond h i)) ξ‖ =
    ‖jointFourierColumn B.left (B.leftCoefficient h)
      (fun i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i)) ξ‖ := by
  simpa only [neg_jointPairPoint] using
    norm_jointFourierColumn_star_neg B.left (B.leftCoefficient h)
      (fun i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i)) ξ

@[simp] theorem terminalTranspose_exceptionalIntegrand (z : U × V) :
    B.terminalTranspose.exceptionalIntegrand z = B.exceptionalIntegrand z := by
  simp only [exceptionalIntegrand, terminalTranspose, jointColumnPairMagnitude,
    norm_star, B.transposed_left_column_norm, B.transposed_right_column_norm]
  apply Finset.sum_congr rfl
  intro h hh
  ring

@[simp] theorem terminalTranspose_ordinaryIntegrand (z : U × V) :
    B.terminalTranspose.ordinaryIntegrand z = B.ordinaryIntegrand z := by
  simp only [ordinaryIntegrand, terminalTranspose, jointColumnEnergy, norm_star,
    B.transposed_left_column_norm, B.transposed_right_column_norm]
  exact mul_comm _ _

@[simp] theorem terminalTranspose_exceptionalCost :
    B.terminalTranspose.exceptionalCost = B.exceptionalCost := by
  change B.weight * (∫ z, B.terminalTranspose.exceptionalIntegrand z ∂B.measure) =
    B.weight * (∫ z, B.exceptionalIntegrand z ∂B.measure)
  simp only [terminalTranspose_exceptionalIntegrand]

@[simp] theorem terminalTranspose_ordinaryCost :
    B.terminalTranspose.ordinaryCost = B.ordinaryCost := by
  change B.weight * (∫ z, B.terminalTranspose.ordinaryIntegrand z ∂B.measure) =
    B.weight * (∫ z, B.ordinaryIntegrand z ∂B.measure)
  simp only [terminalTranspose_ordinaryIntegrand]

@[simp] theorem terminalTranspose_cost : B.terminalTranspose.cost = B.cost := by
  rw [cost, terminalTranspose_exceptionalCost, terminalTranspose_ordinaryCost, cost]

/-- Orientation commutes with the original finite theta partition.
Only the two actual character coordinates exchange places. -/
theorem thetaClassLeaf_terminalTranspose (Q : PairedFiniteCharacters theta H)
    (χ : theta × theta) :
    (B.thetaClassLeaf Q χ).terminalTranspose =
      B.terminalTranspose.thetaClassLeaf Q.swapColumns (χ.2, χ.1) := by
  simp only [thetaClassLeaf, terminalTranspose, Q.swapColumns_thetaClass χ]

theorem thetaClassLeaf_terminalTranspose_exceptionalCost
    (Q : PairedFiniteCharacters theta H) (χ : theta × theta) :
    (B.terminalTranspose.thetaClassLeaf Q.swapColumns (χ.2, χ.1)).exceptionalCost =
      (B.thetaClassLeaf Q χ).exceptionalCost := by
  rw [← B.thetaClassLeaf_terminalTranspose Q χ, terminalTranspose_exceptionalCost]

/-- The direction is selected by the two original common ideals before
either Fourier variable. This operation changes no numerical length. -/
def orientToSmallerSecond (Z : ℝ) (I J : Ideal (𝓞 K)) : ActualHybridLeaf K H U V :=
  if idealLogLength Z I ≤ idealLogLength Z J then B else B.terminalTranspose

@[simp] theorem orientToSmallerSecond_exceptionalCost (Z : ℝ) (I J : Ideal (𝓞 K)) :
    (B.orientToSmallerSecond Z I J).exceptionalCost = B.exceptionalCost := by
  unfold orientToSmallerSecond
  split_ifs <;> simp only [terminalTranspose_exceptionalCost]

@[simp] theorem orientToSmallerSecond_ordinaryCost (Z : ℝ) (I J : Ideal (𝓞 K)) :
    (B.orientToSmallerSecond Z I J).ordinaryCost = B.ordinaryCost := by
  unfold orientToSmallerSecond
  split_ifs <;> simp only [terminalTranspose_ordinaryCost]

@[simp] theorem orientToSmallerSecond_measure (Z : ℝ) (I J : Ideal (𝓞 K)) :
    (B.orientToSmallerSecond Z I J).measure = B.measure := by
  unfold orientToSmallerSecond
  split_ifs <;> rfl

namespace ConstantAtomExtraction

variable {B} (X : B.ConstantAtomExtraction)

/-- The same two extracted constant atoms follow their original sides.
No division by a possibly zero scalar and no new extraction is used. -/
def terminalTranspose : B.terminalTranspose.ConstantAtomExtraction where
  leftScalar := X.rightScalar
  rightScalar := X.leftScalar
  leftResidual := X.rightResidual
  rightResidual := X.leftResidual
  left := X.right
  right := X.left

theorem terminalTranspose_leaf : X.terminalTranspose.leaf = X.leaf.terminalTranspose := by
  simp only [leaf, terminalTranspose, ActualHybridLeaf.terminalTranspose, withConstantAtoms]
  congr 1
  funext h
  simp only [star_mul', star_star]
  ring

/-- The cost of the original leaf is still the cost of this same
constant-atom residual leaf in its transposed orientation. -/
theorem exceptionalCost_eq_terminalTranspose :
    B.exceptionalCost = X.leaf.terminalTranspose.exceptionalCost :=
  X.exceptionalCost_eq.trans X.leaf.terminalTranspose_exceptionalCost.symm

theorem ordinaryCost_eq_terminalTranspose :
    B.ordinaryCost = X.leaf.terminalTranspose.ordinaryCost :=
  X.ordinaryCost_eq.trans X.leaf.terminalTranspose_ordinaryCost.symm

end ConstantAtomExtraction

section Bindings

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {B}
variable {left : SecondSideFrame (V := WithLp 2 (U × V)) C R Ray .left B.leftSlots}
variable {right : SecondSideFrame (V := WithLp 2 (U × V)) C R Ray .right B.rightSlots}
variable {EL : SecondCoefficientComparison left.dictionary}
variable {ER : SecondCoefficientComparison right.dictionary}
variable {Q : PairedFiniteCharacters theta H}

/-- The centered binding is transported from its original individual
atoms, including the full comparison subtraction and all joint locations. -/
def ExceptionalBinding.terminalTranspose
    (b : B.ExceptionalBinding left right EL ER Q) :
    B.terminalTranspose.ExceptionalBinding right.toLeft left.toRight
      (right.toLeftComparison ER) (left.toRightComparison EL) Q.swapColumns where
  rows := b.rows
  left_columns := b.right_columns
  right_columns := b.left_columns
  exceptional h hh := by
    simpa only [PairedFiniteCharacters.swapColumns_exceptional] using b.exceptional h hh
  rowWeight h hh := by
    change star (B.rowWeight h) = R.swapColumns.weight h * R.swapColumns.correlation h
    rw [R.swapColumns_weight_correlation h, b.rowWeight h hh]
  leftCoefficient h hh i hi := by
    change B.rightCoefficient h i = right.toLeft.centeredCoefficient (right.toLeftComparison ER) h i
    rw [right.toLeft_centeredCoefficient ER h i]
    simpa only [star_star] using congrArg star (b.rightCoefficient h hh i hi)
  rightCoefficient h hh i hi := by
    change star (B.leftCoefficient h i) = left.toRight.centeredCoefficient (left.toRightComparison EL) h i
    rw [left.toRight_centeredCoefficient EL h i, b.leftCoefficient h hh i hi]
  leftPoint h hh i hi := by
    rw [right.toLeft_location h i]
    simpa only [ActualHybridLeaf.terminalTranspose, neg_jointPairPoint, neg_neg] using
      congrArg Neg.neg (b.rightPoint h hh i hi)
  rightPoint h hh i hi := by
    rw [left.toRight_location h i]
    simpa only [ActualHybridLeaf.terminalTranspose, neg_jointPairPoint] using
      congrArg Neg.neg (b.leftPoint h hh i hi)

/-- The ordinary exceptional terminal has the identical orientation
transport, without introducing a comparison rectangle. -/
def OrdinaryExceptionalBinding.terminalTranspose
    (b : B.OrdinaryExceptionalBinding left right Q) :
    B.terminalTranspose.OrdinaryExceptionalBinding right.toLeft left.toRight Q.swapColumns where
  rows := b.rows
  left_columns := b.right_columns
  right_columns := b.left_columns
  exceptional h hh := by
    simpa only [PairedFiniteCharacters.swapColumns_exceptional] using b.exceptional h hh
  rowWeight h hh := by
    change star (B.rowWeight h) = R.swapColumns.weight h * R.swapColumns.correlation h
    rw [R.swapColumns_weight_correlation h, b.rowWeight h hh]
  leftCoefficient h hh i hi := by
    change B.rightCoefficient h i = right.toLeft.coefficient h i
    rw [right.toLeft_coefficient h i]
    simpa only [star_star] using congrArg star (b.rightCoefficient h hh i hi)
  rightCoefficient h hh i hi := by
    change star (B.leftCoefficient h i) = left.toRight.coefficient h i
    rw [left.toRight_coefficient h i, b.leftCoefficient h hh i hi]
  leftPoint h hh i hi := by
    rw [right.toLeft_location h i]
    simpa only [ActualHybridLeaf.terminalTranspose, neg_jointPairPoint, neg_neg] using
      congrArg Neg.neg (b.rightPoint h hh i hi)
  rightPoint h hh i hi := by
    rw [left.toRight_location h i]
    simpa only [ActualHybridLeaf.terminalTranspose, neg_jointPairPoint] using
      congrArg Neg.neg (b.leftPoint h hh i hi)

end Bindings
end ActualHybridLeaf
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.jointFourierColumn_star_neg
#print axioms HeckeSkeleton.Moments.EngineStep.PairedFiniteCharacters.swapColumns_thetaClass
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.terminalTranspose_exceptionalCost
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.terminalTranspose_ordinaryCost
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.thetaClassLeaf_terminalTranspose
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ExceptionalBinding.terminalTranspose
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.OrdinaryExceptionalBinding.terminalTranspose
