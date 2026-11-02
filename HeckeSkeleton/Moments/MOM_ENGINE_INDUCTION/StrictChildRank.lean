import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StepOutputAdapter
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileOrderSchedule

/-!
# The strict children's numerical ranks precede their labels

The canonical width drop and literal zero-slot preservation prove the
rank decrease before a recursive label or profile primitive is built.
This permits the actual child's raw window to be converted at its own
scheduled order without a circular appeal to family membership.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open MeasureTheory

/-- Three possible proof stages cannot undo one genuine width-band
decrease. A zero-slot parent retains that slot regime. -/
theorem parameterCoreRank_strict_width {sigma widthLimit padding : ℝ}
    {parent child : RealParameters}
    (hsigma : 0 < sigma) (hchild : 0 ≤ child.m + child.q)
    (hdrop : child.m + child.q + sigma / 2 ≤ parent.m + parent.q)
    (hzero : parent.z = 0 → child.z = 0) :
    parameterCoreRank sigma widthLimit padding child <
      parameterCoreRank sigma widthLimit padding parent := by
  have hband := widthBand_strict hsigma hchild hdrop
  have hslots :
      (if child.z = 0 then 0 else 3 * (widthBand sigma widthLimit + 1)) ≤
        (if parent.z = 0 then 0 else 3 * (widthBand sigma widthLimit + 1)) := by
    by_cases hc : child.z = 0
    · simp [hc]
    · have hp : parent.z ≠ 0 := fun hp => hc (hzero hp)
      simp [hc, hp]
  have hstage :
      (if child.m + child.q + padding < child.n₁ + child.n₂ + child.z then (2 : ℕ)
        else if child.n₁ + child.n₂ + child.z ≤ 5 * (child.m + child.q) / 6 then 0 else 1) ≤ 2 := by
    split_ifs <;> norm_num
  unfold parameterCoreRank
  omega

/-- Every legal strict domain has positive rank, including the
zero-slot ordinary case. The large-width floor alone proves this. -/
theorem parameterCoreRank_pos_of_strict_width {sigma widthLimit padding : ℝ}
    {a : RealParameters} (hsigma : 0 < sigma)
    (hwidth : 16 * sigma < a.m + a.q) :
    0 < parameterCoreRank sigma widthLimit padding a := by
  have hband : widthBand sigma 0 < widthBand sigma (a.m + a.q) :=
    widthBand_strict hsigma (by norm_num) (by linarith)
  have hz : widthBand sigma 0 = 0 := by simp [widthBand]
  rw [hz] at hband
  unfold parameterCoreRank
  split_ifs <;> omega

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω : Type*} [MeasurableSpace Ω]

/-- These are the same actual children as in the source conclusion.
Their primitive membership and labels are not premises. -/
theorem engineOutput_children_rank
    {n : Node K ω ψ} {U sigma delta beta C control widthLimit padding : ℝ}
    {admissible : MomentData K ω ψ → RealParameters → Prop}
    (out : n.EngineOutput (Ω := Ω) U sigma delta beta C control admissible)
    (hsigma : 0 < sigma) (hlength : n.parameters.z = n.data.geometry.totalLength)
    (b : Fin out.branches) (xi : Ω) :
    parameterCoreRank sigma widthLimit padding (out.leftParameters b) <
        parameterCoreRank sigma widthLimit padding n.parameters ∧
      parameterCoreRank sigma widthLimit padding (out.rightParameters b) <
        parameterCoreRank sigma widthLimit padding n.parameters := by
  constructor
  · apply parameterCoreRank_strict_width hsigma (out.left_width_nonneg b)
      (by linarith [out.left_width b])
    intro hzero
    exact (engineOutput_zero_parameters out hlength hzero b xi).1
  · apply parameterCoreRank_strict_width hsigma (out.right_width_nonneg b)
      (by linarith [out.right_width b])
    intro hzero
    exact (engineOutput_zero_parameters out hlength hzero b xi).2

end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.parameterCoreRank_strict_width
#print axioms HeckeSkeleton.Moments.EngineInduction.engineOutput_children_rank
