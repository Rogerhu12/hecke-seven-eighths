module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedFirstLedger
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9ReserveBudget

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fixed polynomial and annular costs in the N8b arithmetic ledger

The original atom budget is a fixed frame coefficient times the square
of the original amplitude. The logarithmic annulus allowance is exactly
one third of its logarithm, hence is bounded by the fixed maximal
annulus. Neither estimate chooses a new moving loss or a new radius.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace ProfileInput

variable (input : ProfileInput call)

theorem frozenAtomBudget_pow_le (frame : SourceFrame) (hframe : call.frame = frame)
    (n : ℕ) :
    input.frozenAtomBudget ^ n ≤ N8ScalarWindow.atomCoefficient c frame ^ n *
      input.amplitude ^ (2 * n) := by
  have h := N8ScalarWindow.frozenAtomBudget_le input
  rw [hframe] at h
  apply (pow_le_pow_left₀ (zero_le_one.trans input.frozenAtomBudget_one) h n).trans_eq
  rw [mul_pow, ← pow_mul]

end ProfileInput

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem annulus_factor_eq :
    call.base ^ (packet.annulusLog / 6) =
      Real.exp (Real.log (max 1 (2 * call.prepared.upper)) / 3) := by
  rw [Real.rpow_def_of_pos call.base_pos]
  congr 1
  unfold annulusLog
  field_simp [(Real.log_pos call.domain.scale).ne'] <;> ring

theorem annulus_factor_le (input : ProfileInput call) (frame : SourceFrame)
    (hframe : call.frame = frame) :
    call.base ^ (packet.annulusLog / 6) ≤ N4.uniformAnnulus c frame := by
  have ha : 0 < max 1 (2 * call.prepared.upper) :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hA : 0 < N4.uniformAnnulus c frame :=
    zero_lt_one.trans_le (N4.uniformAnnulus_one_le c frame)
  have hlog : Real.log (max 1 (2 * call.prepared.upper)) ≤
      Real.log (N4.uniformAnnulus c frame) :=
    Real.log_le_log ha (N4.call_annulus_le frame input hframe)
  have hlog0 : 0 ≤ Real.log (max 1 (2 * call.prepared.upper)) :=
    Real.log_nonneg (le_max_left _ _)
  rw [packet.annulus_factor_eq]
  exact (Real.exp_le_exp.mpr (by linarith)).trans_eq (Real.exp_log hA)

end RawLeafPacket

namespace Call

variable (call : Call c)

theorem arithmetic_loss_budget (p : SourceParameters c) (a : ℝ)
    (ha : a ≤ 128 * ((c.geometry.slots : ℝ) + 1)) :
    call.node.parameters.κ * (momentMesh K c.family).val + a * p.loss ≤
      recipeInductionEdgeLoss c / 2 - 2 * p.loss :=
  (add_le_add le_rfl (mul_le_mul_of_nonneg_right ha p.loss_pos.le)).trans
    (p.mesh_slot_loss_le_arithmeticRemainder _ call.domain.kappa_upper)

theorem arithmetic_loss_rpow (p : SourceParameters c) (a : ℝ)
    (ha : a ≤ 128 * ((c.geometry.slots : ℝ) + 1)) :
    call.base ^ (call.node.parameters.κ * (momentMesh K c.family).val + a * p.loss) ≤
      call.base ^ (recipeInductionEdgeLoss c / 2 - 2 * p.loss) :=
  Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (call.arithmetic_loss_budget p a ha)

/-- Twenty original capacity losses, nine first-scale tilt losses,
two passive-label losses, and the literal first-chart tilt all fit the
unchanged source reserve together with its original mesh. -/
theorem normalized_arithmetic_exponent (p : SourceParameters c) :
    31 * p.loss + 2 * N8Source.columnExponent c * p.tilt +
        call.node.parameters.κ * (momentMesh K c.family).val ≤
      recipeInductionEdgeLoss c / 2 - 2 * p.loss := by
  have hs : 0 ≤ (c.geometry.slots : ℝ) := Nat.cast_nonneg _
  have hσ := N8ScalarWindow.sigma_le_one c
  have hσslots := mul_le_mul_of_nonneg_right hσ
    (show 0 ≤ (c.geometry.slots : ℝ) + 2 by linarith)
  have hcost : 31 + 2 * N8Source.columnExponent c ≤
      128 * ((c.geometry.slots : ℝ) + 1) := by
    dsimp only [N8Source.columnExponent, N8Source.originalLengthBound]
    push_cast
    nlinarith
  have htilt := mul_le_mul_of_nonneg_left p.tilt_le_loss
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (N8Source.columnExponent_pos c).le)
  have hpaid := call.arithmetic_loss_budget p (31 + 2 * N8Source.columnExponent c) hcost
  nlinarith

end Call
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileInput.frozenAtomBudget_pow_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.annulus_factor_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Call.arithmetic_loss_budget
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Call.normalized_arithmetic_exponent
