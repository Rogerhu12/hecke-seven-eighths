import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Include construction requirements in the same uniform preparation

Some source and profile constructions require a larger original scale
or more original seminorms before their scalar estimates can be applied.
These are concrete input demands, not predicates chosen by a witness.
Adding them to a cost preserves its numerical envelope exactly.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

structure UniformDemand where
  orders : Finset (ℕ × ℕ)
  threshold : ℝ
  threshold_one_le : 1 ≤ threshold

namespace UniformDemand

structure Ready {c : TargetContext K} (demand : UniformDemand)
    (call : Call c) (input : ProfileInput call) : Prop where
  orders : demand.orders ⊆ input.orders
  large : demand.threshold ≤ call.base

def join (left right : UniformDemand) : UniformDemand where
  orders := left.orders ∪ right.orders
  threshold := max left.threshold right.threshold
  threshold_one_le := left.threshold_one_le.trans (le_max_left _ _)

theorem ready_left {left right : UniformDemand} {c : TargetContext K}
    {call : Call c} {input : ProfileInput call}
    (ready : (left.join right).Ready call input) : left.Ready call input where
  orders := (Finset.subset_union_left).trans ready.orders
  large := (le_max_left _ _).trans ready.large

theorem ready_right {left right : UniformDemand} {c : TargetContext K}
    {call : Call c} {input : ProfileInput call}
    (ready : (left.join right).Ready call input) : right.Ready call input where
  orders := (Finset.subset_union_right).trans ready.orders
  large := (le_max_right _ _).trans ready.large

end UniformDemand

namespace UniformCost

def withDemand (cost : UniformCost) (demand : UniformDemand) : UniformCost where
  orders := cost.orders ∪ demand.orders
  coefficient := cost.coefficient
  coefficient_nonneg := cost.coefficient_nonneg
  profileDegree := cost.profileDegree
  heightDegree := cost.heightDegree
  heightDegree_nonneg := cost.heightDegree_nonneg
  threshold := max cost.threshold demand.threshold
  threshold_one_le := cost.threshold_one_le.trans (le_max_left _ _)

@[simp] theorem withDemand_value (cost : UniformCost) (demand : UniformDemand)
    (amplitude height : ℝ) :
    (cost.withDemand demand).value amplitude height = cost.value amplitude height := rfl

theorem ready_of_withDemand {cost : UniformCost} {demand : UniformDemand}
    {c : TargetContext K} {call : Call c} {input : ProfileInput call}
    (ready : (cost.withDemand demand).Ready call input) : cost.Ready call input where
  orders := (Finset.subset_union_left).trans ready.orders
  large := (le_max_left _ _).trans ready.large

theorem demand_ready_of_withDemand {cost : UniformCost} {demand : UniformDemand}
    {c : TargetContext K} {call : Call c} {input : ProfileInput call}
    (ready : (cost.withDemand demand).Ready call input) : demand.Ready call input where
  orders := (Finset.subset_union_right).trans ready.orders
  large := (le_max_right _ _).trans ready.large

end UniformCost

def UniformCosts.withDemand (costs : UniformCosts)
    (demand : Finset (ℕ × ℕ) → UniformDemand) : UniformCosts where
  firstZero orders := (costs.firstZero orders).withDemand (demand orders)
  secondZero orders := (costs.secondZero orders).withDemand (demand orders)
  exceptional orders := (costs.exceptional orders).withDemand (demand orders)
  tail orders := (costs.tail orders).withDemand (demand orders)
  arithmeticMass orders := (costs.arithmeticMass orders).withDemand (demand orders)
  profileMass orders := (costs.profileMass orders).withDemand (demand orders)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
