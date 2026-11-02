import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondFrameColumnSwap
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafColumnSwap
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalThetaPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryLiteralExceptionalLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafExceptionalBinding

set_option linter.unusedSectionVars false

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
  sorry

theorem jointFourierColumn_star_neg {I : Type*} (columns : Finset I)
    (c : I → ℂ) (x : I → V) (ξ : V) :
    jointFourierColumn columns (fun i => star (c i)) (fun i => -x i) ξ =
      star (jointFourierColumn columns c x ξ) := by
  sorry

theorem norm_jointFourierColumn_star_neg {I : Type*} (columns : Finset I)
    (c : I → ℂ) (x : I → V) (ξ : V) :
    ‖jointFourierColumn columns (fun i => star (c i)) (fun i => -x i) ξ‖ =
      ‖jointFourierColumn columns c x ξ‖ := by
  sorry

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
  sorry

/-- The same original theta class, with its two coordinates exchanged. -/
@[simp] theorem swapColumns_thetaClass (χ : theta × theta) :
    Q.swapColumns.thetaClass (χ.2, χ.1) = Q.thetaClass χ := by
  sorry

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
  sorry

private theorem transposed_right_column_norm (h : H) (ξ : WithLp 2 (U × V)) :
    ‖jointFourierColumn B.left (fun i => star (B.leftCoefficient h i))
      (fun i => WithLp.toLp 2 (-B.leftFirst h i, -B.leftSecond h i)) ξ‖ =
    ‖jointFourierColumn B.left (B.leftCoefficient h)
      (fun i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i)) ξ‖ := by
  sorry

@[simp] theorem terminalTranspose_exceptionalIntegrand (z : U × V) :
    B.terminalTranspose.exceptionalIntegrand z = B.exceptionalIntegrand z := by
  sorry

@[simp] theorem terminalTranspose_ordinaryIntegrand (z : U × V) :
    B.terminalTranspose.ordinaryIntegrand z = B.ordinaryIntegrand z := by
  sorry

@[simp] theorem terminalTranspose_exceptionalCost :
    B.terminalTranspose.exceptionalCost = B.exceptionalCost := by
  sorry

@[simp] theorem terminalTranspose_ordinaryCost :
    B.terminalTranspose.ordinaryCost = B.ordinaryCost := by
  sorry

@[simp] theorem terminalTranspose_cost : B.terminalTranspose.cost = B.cost := by
  sorry

/-- Orientation commutes with the original finite theta partition.
Only the two actual character coordinates exchange places. -/
theorem thetaClassLeaf_terminalTranspose (Q : PairedFiniteCharacters theta H)
    (χ : theta × theta) :
    (B.thetaClassLeaf Q χ).terminalTranspose =
      B.terminalTranspose.thetaClassLeaf Q.swapColumns (χ.2, χ.1) := by
  sorry

theorem thetaClassLeaf_terminalTranspose_exceptionalCost
    (Q : PairedFiniteCharacters theta H) (χ : theta × theta) :
    (B.terminalTranspose.thetaClassLeaf Q.swapColumns (χ.2, χ.1)).exceptionalCost =
      (B.thetaClassLeaf Q χ).exceptionalCost := by
  sorry

/-- The direction is selected by the two original common ideals before
either Fourier variable. This operation changes no numerical length. -/
def orientToSmallerSecond (Z : ℝ) (I J : Ideal (𝓞 K)) : ActualHybridLeaf K H U V :=
  if idealLogLength Z I ≤ idealLogLength Z J then B else B.terminalTranspose

@[simp] theorem orientToSmallerSecond_exceptionalCost (Z : ℝ) (I J : Ideal (𝓞 K)) :
    (B.orientToSmallerSecond Z I J).exceptionalCost = B.exceptionalCost := by
  sorry

@[simp] theorem orientToSmallerSecond_ordinaryCost (Z : ℝ) (I J : Ideal (𝓞 K)) :
    (B.orientToSmallerSecond Z I J).ordinaryCost = B.ordinaryCost := by
  sorry

@[simp] theorem orientToSmallerSecond_measure (Z : ℝ) (I J : Ideal (𝓞 K)) :
    (B.orientToSmallerSecond Z I J).measure = B.measure := by
  sorry

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
  sorry

/-- The cost of the original leaf is still the cost of this same
constant-atom residual leaf in its transposed orientation. -/
theorem exceptionalCost_eq_terminalTranspose :
    B.exceptionalCost = X.leaf.terminalTranspose.exceptionalCost := by
  sorry

theorem ordinaryCost_eq_terminalTranspose :
    B.ordinaryCost = X.leaf.terminalTranspose.ordinaryCost := by
  sorry

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
  rows_zero h hh hn := by
    change star (B.rowWeight h) = 0
    rw [b.rows_zero h hh hn, star_zero]
  left_columns := b.right_columns
  right_columns := b.left_columns
  exceptional h hh := by
    simpa only [terminalTranspose_exceptional,
      PairedFiniteCharacters.swapColumns_exceptional] using b.exceptional h hh
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
    change WithLp.toLp 2 (B.rightFirst h i, -B.rightSecond h i) =
      rawSourceLocation (right.toLeft.leftLocation h) (right.toLeft.rightLocation h)
        (right.toLeft.slotLocation h) i
    rw [right.toLeft_location h i]
    simpa only [ActualHybridLeaf.terminalTranspose, neg_jointPairPoint, neg_neg] using
      congrArg Neg.neg (b.rightPoint h hh i hi)
  rightPoint h hh i hi := by
    change WithLp.toLp 2 (-B.leftFirst h i, -B.leftSecond h i) =
      rawSourceLocation (left.toRight.leftLocation h) (left.toRight.rightLocation h)
        (left.toRight.slotLocation h) i
    rw [left.toRight_location h i]
    simpa only [ActualHybridLeaf.terminalTranspose, neg_jointPairPoint] using
      congrArg Neg.neg (b.leftPoint h hh i hi)

/-- The ordinary exceptional terminal has the identical orientation
transport, without introducing a comparison rectangle. -/
def OrdinaryExceptionalBinding.terminalTranspose
    (b : B.OrdinaryExceptionalBinding left right Q) :
    B.terminalTranspose.OrdinaryExceptionalBinding right.toLeft left.toRight Q.swapColumns where
  rows := b.rows
  rows_zero h hh hn := by
    change star (B.rowWeight h) = 0
    rw [b.rows_zero h hh hn, star_zero]
  left_columns := b.right_columns
  right_columns := b.left_columns
  exceptional h hh := by
    simpa only [terminalTranspose_exceptional,
      PairedFiniteCharacters.swapColumns_exceptional] using b.exceptional h hh
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
    change WithLp.toLp 2 (B.rightFirst h i, -B.rightSecond h i) =
      rawSourceLocation (right.toLeft.leftLocation h) (right.toLeft.rightLocation h)
        (right.toLeft.slotLocation h) i
    rw [right.toLeft_location h i]
    simpa only [ActualHybridLeaf.terminalTranspose, neg_jointPairPoint, neg_neg] using
      congrArg Neg.neg (b.rightPoint h hh i hi)
  rightPoint h hh i hi := by
    change WithLp.toLp 2 (-B.leftFirst h i, -B.leftSecond h i) =
      rawSourceLocation (left.toRight.leftLocation h) (left.toRight.rightLocation h)
        (left.toRight.slotLocation h) i
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
