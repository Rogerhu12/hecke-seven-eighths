module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformMellinPreparation

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# U1: all six estimates receive the same prepared original input

The literal Mellin-to-Schwartz theorem constructs the original profile
representatives at each frequency. Their amplitude and finite orders
were selected earlier. Each cost's input and threshold requirements
then follow from the finite unions and numerical maxima; the four
terminal terms and the product of the two mass costs are both funded.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformRealizationProof

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineInduction EngineInduction.Source
open UniformOrderPreparation UniformMellinPreparation

variable {K : Type} [Field K] [NumberField K]
variable (c : TargetContext K) (frame : SourceFrame) (costs : UniformCosts)

local instance realizationReflectionMeasurable : MeasurableSpace (ℕ × Bool) := ⊤
local instance realizationReflectionSingleton : MeasurableSingletonClass (ℕ × Bool) := by
  constructor
  intro x
  trivial

variable {Cp Hp : ℝ} {hCp : 0 < Cp}
variable {hminimum : (schedule c frame costs).minimumCp ≤ Cp} {hHp : 0 ≤ Hp}

def profileInput
    (request : (preparation c frame costs).Request Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    ProfileInput ((preparation c frame costs).toCall request frequency) where
  regular :=
    { cap := rfl
      weight := rfl
      lower := rfl
      upper := rfl
      heightDegree_nonneg := hHp
      minimumCp := hminimum }
  orders := inputOrders c frame costs (atRank c frame costs (requestRank c frame costs request))
  amplitude := amplitude c frame costs (atRank c frame costs (requestRank c frame costs request))
  amplitude_one_le := amplitude_one_le c frame costs _
  raw := Classical.choice (mellinStrictModel_rawWindow
    (Ω := CombinedParameter) (UniformOrderPreparation.range c frame)
    (extraOrders c frame costs (atRank c frame costs (requestRank c frame costs request)))
    (atRank c frame costs (requestRank c frame costs request))
    request.parent c.geometry.slots frame.decay
    (lower c frame (requestRank c frame costs request))
    (upper c frame (requestRank c frame costs request))
    (zero_lt_one.trans frame.decay_gt_one).le
    (lower_pos c frame _) (interval c frame _)
    (StrictProfileRange.expanded_contains_schedule frame.lower frame.upper
      frame.lower_pos frame.interval.le (rankBound c) (requestRank c frame costs request))
    (profileFamilyBudget Cp Hp request.height)
    (profileFamilyBudget_one_le hCp.le hHp request.height_nonneg)
    request.base (zero_lt_one.trans request.domain.scale)
    request.node.down.property.slot_count (originalProfiles c frame costs request) frequency)

def estimates
    (request : (preparation c frame costs).Request Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    PreparedEstimates costs ((preparation c frame costs).toCall request frequency) := by
  let call := (preparation c frame costs).toCall request frequency
  let input := profileInput c frame costs request frequency
  let rank := requestRank c frame costs request
  let J := atRank c frame costs rank
  let orders := childOrders c frame J
  let amplitude := UniformOrderPreparation.amplitude c frame costs J
  have hamp : 0 ≤ amplitude := zero_le_one.trans (amplitude_one_le c frame costs J)
  have hrank : rank ≤ rankBound c := requestRank_le c frame costs request
  have hlarge : (costs.totalEnvelope orders amplitude hamp).threshold ≤ call.base :=
    (HeightEnvelope.threshold_le_finite (rankBound c)
      (UniformScalarPreparation.atRank c frame costs) hrank).trans
        (base_threshold c frame costs hCp hminimum hHp request)
  have ht := costs.thresholds_le_total orders amplitude hamp
  have ho := demandOrders_subset c frame costs J
  refine
    { profile := input
      firstZero_ready := ⟨?_, ?_⟩
      secondZero_ready := ⟨?_, ?_⟩
      exceptional_ready := ⟨?_, ?_⟩
      tail_ready := ⟨?_, ?_⟩
      arithmeticMass_ready := ⟨?_, ?_⟩
      profileMass_ready := ⟨?_, ?_⟩
      terminal_funding := ?_
      mass_funding := ?_ }
  · exact (costs.firstZero_orders orders).trans ho
  · exact ht.1.trans hlarge
  · exact (costs.secondZero_orders orders).trans ho
  · exact ht.2.1.trans hlarge
  · exact (costs.exceptional_orders orders).trans ho
  · exact ht.2.2.1.trans hlarge
  · exact (costs.tail_orders orders).trans ho
  · exact ht.2.2.2.1.trans hlarge
  · exact (costs.arithmeticMass_orders orders).trans ho
  · exact ht.2.2.2.2.1.trans hlarge
  · exact (costs.profileMass_orders orders).trans ho
  · exact ht.2.2.2.2.2.trans hlarge
  · exact (costs.terminalEnvelope_bound orders amplitude hamp request.height_nonneg).trans
      (((costs.terminalEnvelope orders amplitude hamp).value_le_add_left
        (costs.massEnvelope orders amplitude hamp) request.height_nonneg).trans
          (HeightEnvelope.value_le_finite (rankBound c)
            (UniformScalarPreparation.atRank c frame costs) hrank request.height_nonneg))
  · exact (costs.massEnvelope_eq orders amplitude hamp request.height_nonneg).le.trans
      (((costs.terminalEnvelope orders amplitude hamp).value_le_add_right
        (costs.massEnvelope orders amplitude hamp) request.height_nonneg).trans
          (HeightEnvelope.value_le_finite (rankBound c)
            (UniformScalarPreparation.atRank c frame costs) hrank request.height_nonneg))

def realization : UniformRealization c frame costs where
  preparation := preparation c frame costs
  inputs _Cp _Hp _hCp _hminimum _hHp request frequency :=
    estimates c frame costs request frequency

theorem uniformChoice (c : TargetContext K) : UniformChoiceTask c := by
  intro frame costs
  exact ⟨realization c frame costs⟩

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformRealizationProof

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformRealizationProof.uniformChoice
