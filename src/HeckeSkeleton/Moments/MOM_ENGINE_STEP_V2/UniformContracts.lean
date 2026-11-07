module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.EstimateData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Numerical preparation after the independent uniform estimates

The six cost functions below are the particular witnesses returned by
the separate terminal and kernel tasks. They are indexed by the actual
requested child seminorms. The preparation task collects their finite
input orders, propagates these backwards through the rank schedule,
and pays their numerical envelopes. Its output contains original
profile representatives only, never a transformed source or a child.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

/-- Each function is fixed before any moving source and before the
common source profile budget `Cp, Hp` is selected. -/
structure UniformCosts where
  firstZero : Finset (ℕ × ℕ) → UniformCost
  secondZero : Finset (ℕ × ℕ) → UniformCost
  exceptional : Finset (ℕ × ℕ) → UniformCost
  tail : Finset (ℕ × ℕ) → UniformCost
  arithmeticMass : Finset (ℕ × ℕ) → UniformCost
  profileMass : Finset (ℕ × ℕ) → UniformCost

namespace UniformCosts

variable (costs : UniformCosts) {c : TargetContext K}
variable (call : Call c) (input : ProfileInput call)

def terminalValue : ℝ :=
  (costs.firstZero call.childOrders).value input.amplitude call.request.height +
  (costs.secondZero call.childOrders).value input.amplitude call.request.height +
  (costs.exceptional call.childOrders).value input.amplitude call.request.height +
  (costs.tail call.childOrders).value input.amplitude call.request.height

def massValue : ℝ :=
  (costs.arithmeticMass call.childOrders).value input.amplitude call.request.height *
  (costs.profileMass call.childOrders).value input.amplitude call.request.height

end UniformCosts

/-- The original input meets the particular finite demands already
selected by the estimate tasks. Funding is a numerical inequality;
none of the six analytic estimates is assumed in this record. -/
structure PreparedEstimates {c : TargetContext K}
    (costs : UniformCosts) (call : Call c) where
  profile : ProfileInput call
  firstZero_ready : (costs.firstZero call.childOrders).Ready call profile
  secondZero_ready : (costs.secondZero call.childOrders).Ready call profile
  exceptional_ready : (costs.exceptional call.childOrders).Ready call profile
  tail_ready : (costs.tail call.childOrders).Ready call profile
  arithmeticMass_ready : (costs.arithmeticMass call.childOrders).Ready call profile
  profileMass_ready : (costs.profileMass call.childOrders).Ready call profile
  terminal_funding : costs.terminalValue call profile ≤
    call.prepared.engineCoefficient * call.prepared.engineControl
  mass_funding : costs.massValue call profile ≤
    call.prepared.engineCoefficient * call.prepared.engineControl

/-- All numerical choices precede the original scale, index, node and
frequency. Each frequency then receives its actual original profile
window by the merged Mellin bridge. -/
structure UniformRealization (c : TargetContext K) (frame : SourceFrame)
    (costs : UniformCosts) where
  preparation : UniformPreparation c frame
  inputs : ∀ (Cp Hp : ℝ) (hCp : 0 < Cp)
    (hminimum : preparation.schedule.minimumCp ≤ Cp) (hHp : 0 ≤ Hp)
    (request : preparation.Request Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ),
      PreparedEstimates costs (preparation.toCall request frequency)

/-- Finite unions, backward profile orders and finite-rank maxima turn
the independently proved scalar witnesses into legal original inputs.
The fixed eligibility checks in `PreparedEstimates` cannot be replaced
by a predicate selected by the certificate. -/
def UniformChoiceTask (c : TargetContext K) : Prop :=
  ∀ (frame : SourceFrame) (costs : UniformCosts),
    Nonempty (UniformRealization c frame costs)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
