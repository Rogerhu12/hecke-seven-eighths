import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

/-!
# The exact empty-parent case of the uniform engine

The original row set can be empty. Then its whole ordinary or centered
energy is exactly zero, so no first row, prime pool or child needs to be
chosen. This constructor has zero branches and zero terminal terms.
It removes an otherwise artificial nonempty-row assumption from the
primitive entrance; nonempty parents use the actual source factories.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K} {Ω : Type*} [MeasurableSpace Ω]

/-- The actual whole parent vanishes on its original empty row set,
including every centered comparison and every live slot. -/
theorem pairedStageEnergy_eq_zero_of_rows_empty
    (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
    (Z t Y₁ Y₂ : ℝ) (hrows : pairedRows d a Z = ∅) :
    pairedStageEnergy centered d a Z t Y₁ Y₂ = 0 := by
  simp only [pairedStageEnergy, hrows, Finset.sum_empty]

namespace PairedEngineConclusion

/-- The empty original carrier gives an exact engine output. No pool
object or source-bound input is involved, and all admissibility and
capacity fields are vacuous on the same empty child carrier. -/
def ofEmptyParent
    (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
    (Z t Y₁ Y₂ step ε terminalExponent C control : ℝ)
    (admissible : MomentData K ω ψ → RealParameters → Prop)
    (hZ : 0 ≤ Z) (hC : 0 ≤ C) (hcontrol : 0 ≤ control)
    (hrows : pairedRows d a Z = ∅) :
    PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ step ε terminalExponent C control admissible where
  branches := 0
  leftData := fun b => Fin.elim0 b
  rightData := fun b => Fin.elim0 b
  leftParameters := fun b => Fin.elim0 b
  rightParameters := fun b => Fin.elim0 b
  leftTwist := fun b => Fin.elim0 b
  rightTwist := fun b => Fin.elim0 b
  leftTwist_zero := fun b => Fin.elim0 b
  rightTwist_zero := fun b => Fin.elim0 b
  kernel := fun b => Fin.elim0 b
  finite_kernel := fun b => Fin.elim0 b
  left_width := fun b => Fin.elim0 b
  right_width := fun b => Fin.elim0 b
  left_width_nonneg := fun b => Fin.elim0 b
  right_width_nonneg := fun b => Fin.elim0 b
  left_plain_left_nonneg := fun b => Fin.elim0 b
  left_plain_right_nonneg := fun b => Fin.elim0 b
  right_plain_left_nonneg := fun b => Fin.elim0 b
  right_plain_right_nonneg := fun b => Fin.elim0 b
  left_length := fun b => Fin.elim0 b
  right_length := fun b => Fin.elim0 b
  left_kappa := fun b => Fin.elim0 b
  right_kappa := fun b => Fin.elim0 b
  left_slots := fun b => Fin.elim0 b
  right_slots := fun b => Fin.elim0 b
  left_theta := fun b => Fin.elim0 b
  right_theta := fun b => Fin.elim0 b
  left_slot_characters := fun b => Fin.elim0 b
  right_slot_characters := fun b => Fin.elim0 b
  left_admissible := fun b => Fin.elim0 b
  right_admissible := fun b => Fin.elim0 b
  left_capacity := fun b => Fin.elim0 b
  right_capacity := fun b => Fin.elim0 b
  firstZero := 0
  secondZero := 0
  exceptional := 0
  tail := 0
  firstZero_nonneg := le_rfl
  secondZero_nonneg := le_rfl
  exceptional_nonneg := le_rfl
  tail_nonneg := le_rfl
  terminals := by
    simpa only [zero_add] using
      mul_nonneg (mul_nonneg hC hcontrol) (Real.rpow_nonneg hZ terminalExponent)
  left_integrable := fun b => Fin.elim0 b
  right_integrable := fun b => Fin.elim0 b
  cauchy_integrable := fun b => Fin.elim0 b
  parent := by
    simp [pairedStageEnergy, hrows]
  mass := by
    simpa using mul_nonneg (mul_nonneg hC hcontrol) (Real.rpow_nonneg hZ ε)

@[simp] theorem ofEmptyParent_branches
    (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
    (Z t Y₁ Y₂ step ε terminalExponent C control : ℝ)
    (admissible : MomentData K ω ψ → RealParameters → Prop)
    (hZ : 0 ≤ Z) (hC : 0 ≤ C) (hcontrol : 0 ≤ control)
    (hrows : pairedRows d a Z = ∅) :
    (ofEmptyParent (Ω := Ω) centered d a Z t Y₁ Y₂ step ε terminalExponent C control
      admissible hZ hC hcontrol hrows).branches = 0 := rfl

end PairedEngineConclusion
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.pairedStageEnergy_eq_zero_of_rows_empty
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.ofEmptyParent
