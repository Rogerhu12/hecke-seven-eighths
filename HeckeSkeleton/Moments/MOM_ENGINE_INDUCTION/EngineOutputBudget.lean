import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

/-!
# Enlarging only the numerical budget of the actual engine output

The literal children, their admissibility, all four terminal terms and
the common positive kernels are retained. The two exponent comparisons
and the scalar comparison spend the already selected induction budget;
no parent or child energy estimate is an input to this operation.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open MeasureTheory EngineStep

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {U t Y₁ Y₂ sigma delta beta C control delta' beta' C' control' : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

/-- The source constants may be replaced by one finite common budget,
and the mass and terminal exponents may be paid by larger losses. -/
def enlargeEngineOutputBudget
    (out : PairedEngineConclusion (Ω := Ω) centered d a U t Y₁ Y₂
      sigma delta beta C control admissible)
    (hU : 1 ≤ U) (hbudget : C * control ≤ C' * control')
    (hnew : 0 ≤ C' * control') (hdelta : delta ≤ delta') (hbeta : beta ≤ beta') :
    PairedEngineConclusion (Ω := Ω) centered d a U t Y₁ Y₂
      sigma delta' beta' C' control' admissible where
  branches := out.branches
  leftData := out.leftData
  rightData := out.rightData
  leftParameters := out.leftParameters
  rightParameters := out.rightParameters
  leftTwist := out.leftTwist
  rightTwist := out.rightTwist
  leftTwist_zero := out.leftTwist_zero
  rightTwist_zero := out.rightTwist_zero
  kernel := out.kernel
  finite_kernel := out.finite_kernel
  left_width := out.left_width
  right_width := out.right_width
  left_width_nonneg := out.left_width_nonneg
  right_width_nonneg := out.right_width_nonneg
  left_plain_left_nonneg := out.left_plain_left_nonneg
  left_plain_right_nonneg := out.left_plain_right_nonneg
  right_plain_left_nonneg := out.right_plain_left_nonneg
  right_plain_right_nonneg := out.right_plain_right_nonneg
  left_length := out.left_length
  right_length := out.right_length
  left_kappa := out.left_kappa
  right_kappa := out.right_kappa
  left_slots := out.left_slots
  right_slots := out.right_slots
  left_theta := out.left_theta
  right_theta := out.right_theta
  left_slot_characters := out.left_slot_characters
  right_slot_characters := out.right_slot_characters
  left_admissible := out.left_admissible
  right_admissible := out.right_admissible
  left_capacity := out.left_capacity
  right_capacity := out.right_capacity
  firstZero := out.firstZero
  secondZero := out.secondZero
  exceptional := out.exceptional
  tail := out.tail
  firstZero_nonneg := out.firstZero_nonneg
  secondZero_nonneg := out.secondZero_nonneg
  exceptional_nonneg := out.exceptional_nonneg
  tail_nonneg := out.tail_nonneg
  terminals := out.terminals.trans
    ((mul_le_mul_of_nonneg_right hbudget
      (Real.rpow_nonneg (zero_le_one.trans hU) beta)).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hU hbeta) hnew))
  left_integrable := out.left_integrable
  right_integrable := out.right_integrable
  cauchy_integrable := out.cauchy_integrable
  parent := out.parent
  mass := out.mass.trans
    ((mul_le_mul_of_nonneg_right hbudget
      (Real.rpow_nonneg (zero_le_one.trans hU) delta)).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hU hdelta) hnew))

end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.enlargeEngineOutputBudget
