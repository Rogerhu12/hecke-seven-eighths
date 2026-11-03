import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Pay the separate terminal and kernel estimates

Only addition, multiplication by nonnegative scalars and the fixed loss
split occur here. The inequalities are explicit inputs from the separate
tasks and refer to the same four source terminals and normalized family.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {costs : UniformCosts}

theorem terminal_budget (input : PreparedEstimates costs call)
    (firstZero secondZero exceptional tail : ℝ)
    (hfirst : firstZero ≤ (costs.firstZero call.childOrders).value
      input.profile.amplitude call.request.height * call.base ^ recipeInductionTerminalLoss c)
    (hsecond : secondZero ≤ (costs.secondZero call.childOrders).value
      input.profile.amplitude call.request.height * call.base ^ recipeInductionTerminalLoss c)
    (hexceptional : exceptional ≤ (costs.exceptional call.childOrders).value
      input.profile.amplitude call.request.height * call.base ^ recipeInductionTerminalLoss c)
    (htail : tail ≤ (costs.tail call.childOrders).value
      input.profile.amplitude call.request.height * call.base ^ recipeInductionTerminalLoss c) :
    firstZero + secondZero + exceptional + tail ≤
      call.prepared.engineCoefficient * call.prepared.engineControl *
        call.base ^ recipeInductionTerminalLoss c := by
  calc
    _ ≤ (costs.firstZero call.childOrders).value
          input.profile.amplitude call.request.height * call.base ^ recipeInductionTerminalLoss c +
        (costs.secondZero call.childOrders).value
          input.profile.amplitude call.request.height * call.base ^ recipeInductionTerminalLoss c +
        (costs.exceptional call.childOrders).value
          input.profile.amplitude call.request.height * call.base ^ recipeInductionTerminalLoss c +
        (costs.tail call.childOrders).value
          input.profile.amplitude call.request.height * call.base ^ recipeInductionTerminalLoss c :=
      add_le_add (add_le_add (add_le_add hfirst hsecond) hexceptional) htail
    _ = costs.terminalValue call input.profile * call.base ^ recipeInductionTerminalLoss c := by
      unfold UniformCosts.terminalValue
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right input.terminal_funding
      (Real.rpow_nonneg call.base_pos.le _)

theorem mass_budget (input : PreparedEstimates costs call) (N : NormalizedData call)
    (harithmetic : N.arithmeticMass ≤ (costs.arithmeticMass call.childOrders).value
      input.profile.amplitude call.request.height * call.base ^ (recipeInductionEdgeLoss c / 2))
    (hprofile : N.kernelMass ≤ (costs.profileMass call.childOrders).value
      input.profile.amplitude call.request.height * call.base ^ (recipeInductionEdgeLoss c / 2) *
        N.arithmeticMass) :
    N.MassBound call.prepared.engineCoefficient call.prepared.engineControl
      (recipeInductionEdgeLoss c) := by
  have hvalue : 0 ≤ (costs.profileMass call.childOrders).value
      input.profile.amplitude call.request.height :=
    UniformCost.value_nonneg _
      (zero_le_one.trans input.profile.amplitude_one_le) call.request.height_nonneg
  have hpower : call.base ^ (recipeInductionEdgeLoss c / 2) *
      call.base ^ (recipeInductionEdgeLoss c / 2) = call.base ^ recipeInductionEdgeLoss c := by
    rw [← Real.rpow_add call.base_pos]
    congr 1
    ring
  unfold NormalizedData.MassBound
  calc
    _ ≤ (costs.profileMass call.childOrders).value
          input.profile.amplitude call.request.height *
        call.base ^ (recipeInductionEdgeLoss c / 2) * N.arithmeticMass := hprofile
    _ ≤ (costs.profileMass call.childOrders).value
          input.profile.amplitude call.request.height *
        call.base ^ (recipeInductionEdgeLoss c / 2) *
        ((costs.arithmeticMass call.childOrders).value
          input.profile.amplitude call.request.height *
          call.base ^ (recipeInductionEdgeLoss c / 2)) :=
      mul_le_mul_of_nonneg_left harithmetic
        (mul_nonneg hvalue (Real.rpow_nonneg call.base_pos.le _))
    _ = costs.massValue call input.profile * call.base ^ recipeInductionEdgeLoss c := by
      unfold UniformCosts.massValue
      calc
        _ = ((costs.arithmeticMass call.childOrders).value
              input.profile.amplitude call.request.height *
            (costs.profileMass call.childOrders).value
              input.profile.amplitude call.request.height) *
            (call.base ^ (recipeInductionEdgeLoss c / 2) *
              call.base ^ (recipeInductionEdgeLoss c / 2)) := by ring
        _ = _ := by rw [hpower]
    _ ≤ _ := mul_le_mul_of_nonneg_right input.mass_funding
      (Real.rpow_nonneg call.base_pos.le _)

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.terminal_budget
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.mass_budget
