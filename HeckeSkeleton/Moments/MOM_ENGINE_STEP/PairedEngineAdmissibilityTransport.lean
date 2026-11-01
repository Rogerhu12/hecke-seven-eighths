import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

/-!
# Preserve the actual engine output while refining admissibility

An internally proved property of each already selected child may be
included in the public admissibility predicate. Every child, parameter,
twist, kernel and terminal value is copied from the same output. The
parent recursion and the mass bound are consequently retained verbatim.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ σ ε terminalExponent C control : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

variable (out : PairedEngineConclusion (Ω := Ω) centered d a
  Z t Y₁ Y₂ σ ε terminalExponent C control admissible)
variable (target : MomentData K ω ψ → RealParameters → Prop)
variable (hleft : ∀ b ξ, target (out.leftData b ξ) (out.leftParameters b))
variable (hright : ∀ b ξ, target (out.rightData b ξ) (out.rightParameters b))

/-- Only the admissibility proofs are replaced. This internal transport
does not choose a new child, new branch enumeration or new kernel. -/
def withAdmissible :
    PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ σ ε terminalExponent C control target where
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
  left_admissible := hleft
  right_admissible := hright
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
  terminals := out.terminals
  left_integrable := out.left_integrable
  right_integrable := out.right_integrable
  cauchy_integrable := out.cauchy_integrable
  parent := out.parent
  mass := out.mass

@[simp] theorem withAdmissible_branches :
    (out.withAdmissible target hleft hright).branches = out.branches := rfl

@[simp] theorem withAdmissible_leftData :
    (out.withAdmissible target hleft hright).leftData = out.leftData := rfl

@[simp] theorem withAdmissible_rightData :
    (out.withAdmissible target hleft hright).rightData = out.rightData := rfl

@[simp] theorem withAdmissible_leftParameters :
    (out.withAdmissible target hleft hright).leftParameters = out.leftParameters := rfl

@[simp] theorem withAdmissible_rightParameters :
    (out.withAdmissible target hleft hright).rightParameters = out.rightParameters := rfl

@[simp] theorem withAdmissible_kernel :
    (out.withAdmissible target hleft hright).kernel = out.kernel := rfl

/-- Restriction to a requested public predicate acts on the same output. -/
def mapAdmissible (h : ∀ child parameters,
    admissible child parameters → target child parameters) :
    PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ σ ε terminalExponent C control target :=
  out.withAdmissible target
    (fun b ξ => h _ _ (out.left_admissible b ξ))
    (fun b ξ => h _ _ (out.right_admissible b ξ))

/-- A zero-slot parent already forces every actual left child to have
no slots. No character closure assumption is involved. -/
theorem left_slot_inverse_of_zero_slots (hzero : d.geometry.slotCount = 0)
    (b : Fin out.branches) (ξ : Ω) (i : Fin (out.leftData b ξ).geometry.slotCount) :
    ((out.leftData b ξ).slotCoefficient i)⁻¹ ∈ (out.leftData b ξ).theta := by
  have hcount : (out.leftData b ξ).geometry.slotCount = 0 :=
    Nat.eq_zero_of_le_zero (by simpa only [hzero] using out.left_slots b ξ)
  exact Fin.elim0 (Fin.cast hcount i)

/-- The same existing slot bound handles the right zero-slot child. -/
theorem right_slot_inverse_of_zero_slots (hzero : d.geometry.slotCount = 0)
    (b : Fin out.branches) (ξ : Ω) (i : Fin (out.rightData b ξ).geometry.slotCount) :
    ((out.rightData b ξ).slotCoefficient i)⁻¹ ∈ (out.rightData b ξ).theta := by
  have hcount : (out.rightData b ξ).geometry.slotCount = 0 :=
    Nat.eq_zero_of_le_zero (by simpa only [hzero] using out.right_slots b ξ)
  exact Fin.elim0 (Fin.cast hcount i)

end HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion

#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.withAdmissible
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.mapAdmissible
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.left_slot_inverse_of_zero_slots
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.right_slot_inverse_of_zero_slots
