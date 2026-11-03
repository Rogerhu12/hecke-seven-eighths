import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# U1: select the finite orders before the moving source

The child orders determine six already selected analytic costs. Their
original seminorm demands are collected before choosing the source
Mellin order. The backward schedule therefore has no circular demand.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open EngineInduction EngineInduction.Source EngineStep
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

namespace UniformCosts

def demandOrders (costs : UniformCosts) (orders : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (costs.firstZero orders).orders ∪ (costs.secondZero orders).orders ∪
    (costs.exceptional orders).orders ∪ (costs.tail orders).orders ∪
      (costs.arithmeticMass orders).orders ∪ (costs.profileMass orders).orders

theorem firstZero_orders (costs : UniformCosts) (orders : Finset (ℕ × ℕ)) :
    (costs.firstZero orders).orders ⊆ costs.demandOrders orders := by
  intro q hq
  simp only [demandOrders, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hq))))

theorem secondZero_orders (costs : UniformCosts) (orders : Finset (ℕ × ℕ)) :
    (costs.secondZero orders).orders ⊆ costs.demandOrders orders := by
  intro q hq
  simp only [demandOrders, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hq))))

theorem exceptional_orders (costs : UniformCosts) (orders : Finset (ℕ × ℕ)) :
    (costs.exceptional orders).orders ⊆ costs.demandOrders orders := by
  intro q hq
  simp only [demandOrders, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inr hq)))

theorem tail_orders (costs : UniformCosts) (orders : Finset (ℕ × ℕ)) :
    (costs.tail orders).orders ⊆ costs.demandOrders orders := by
  intro q hq
  simp only [demandOrders, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr hq))

theorem arithmeticMass_orders (costs : UniformCosts) (orders : Finset (ℕ × ℕ)) :
    (costs.arithmeticMass orders).orders ⊆ costs.demandOrders orders := by
  intro q hq
  simp only [demandOrders, Finset.mem_union]
  exact Or.inl (Or.inr hq)

theorem profileMass_orders (costs : UniformCosts) (orders : Finset (ℕ × ℕ)) :
    (costs.profileMass orders).orders ⊆ costs.demandOrders orders := by
  intro q hq
  simp only [demandOrders, Finset.mem_union]
  exact Or.inr hq

end UniformCosts

namespace UniformOrderPreparation

variable (c : TargetContext K) (frame : SourceFrame) (costs : UniformCosts)

def rankBound : ℕ := 6 * (widthBand (recipeInductionSigma c) 2 + 1)

def range : StrictProfileRange :=
  StrictProfileRange.ofSchedule frame.lower frame.upper frame.lower_pos
    frame.interval.le (rankBound c)

def childOrders (J : ℕ) : Finset (ℕ × ℕ) :=
  (range c frame).childOrders (K := K) (ω := c.family.omega)
    (ψ := targetCharacter K c) ∅ J frame.decay

def extraOrders (J : ℕ) : Finset (ℕ × ℕ) :=
  costs.demandOrders (childOrders c frame J)

def inputOrders (J : ℕ) : Finset (ℕ × ℕ) :=
  (range c frame).inputOrders (K := K) (ω := c.family.omega)
    (ψ := targetCharacter K c) (extraOrders c frame costs J) J frame.decay

def mellinOrder (J : ℕ) : ℕ :=
  (range c frame).mellinOrder (K := K) (ω := c.family.omega)
    (ψ := targetCharacter K c) (extraOrders c frame costs J) J frame.decay

def engine (J : ℕ) : ℕ := mellinOrder c frame costs J + 2

def amplitude (J : ℕ) : ℝ :=
  (range c frame).amplitude (K := K) (ω := c.family.omega)
    (ψ := targetCharacter K c) (extraOrders c frame costs J) J frame.decay

theorem amplitude_one_le (J : ℕ) : 1 ≤ amplitude c frame costs J :=
  StrictProfileRange.amplitude_one_le _ _ _ _

theorem demandOrders_subset (J : ℕ) :
    costs.demandOrders (childOrders c frame J) ⊆ inputOrders c frame costs J := by
  intro q hq
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_insert_of_mem
  exact (range c frame).childOrders_extra
    (extraOrders c frame costs J) J frame.decay hq

def schedule : OrderSchedule where
  engine := engine c frame costs
  minimumCp := strictChildProfileMinimum
    (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
    1 (engine c frame costs) frame.reflection (recipeInductionSigma c)
    2 (recipeInductionSigma c / 16) frame.decay frame.lower frame.upper
    frame.lower_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) frame.upper_large)

def atRank (rank : ℕ) : ℕ :=
  backwardProfileOrder 1 (engine c frame costs) frame.reflection (rank - 1)

theorem engine_atRank_le {rank : ℕ} (hrank : 0 < rank) :
    engine c frame costs (atRank c frame costs rank) ≤
      backwardProfileOrder 1 (engine c frame costs) frame.reflection rank :=
  (backwardProfileOrder_parent_orders 1 _ _ hrank).1

end UniformOrderPreparation
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformOrderPreparation.demandOrders_subset
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformOrderPreparation.engine_atRank_le
