import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Order
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Recursion
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Family
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Terminal
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ExceptionalCounting
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.TerminalCertificate
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Interface
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Induction

/-!
# Recursive axiom audit for the paired-moment induction

This target covers the eight clean proof modules and the three conditional
paired-moment projections. The existing skeleton adapter has a separate
integration boundary because its upstream model definitions are admitted.
-/

-- Order
#print axioms HeckeSkeleton.Moments.EngineInduction.State
#print axioms HeckeSkeleton.Moments.EngineInduction.State.Earlier
#print axioms HeckeSkeleton.Moments.EngineInduction.State.comparison
#print axioms HeckeSkeleton.Moments.EngineInduction.State.earlier_rank_lt
#print axioms HeckeSkeleton.Moments.EngineInduction.State.earlier_wellFounded
#print axioms HeckeSkeleton.Moments.EngineInduction.State.induction
#print axioms HeckeSkeleton.Moments.EngineInduction.State.rank
#print axioms HeckeSkeleton.Moments.EngineInduction.State.rank_lt_bound
#print axioms HeckeSkeleton.Moments.EngineInduction.State.smaller_band
#print axioms HeckeSkeleton.Moments.EngineInduction.State.zero_before_positive
#print axioms HeckeSkeleton.Moments.EngineInduction.boundedBand
#print axioms HeckeSkeleton.Moments.EngineInduction.strict_child_earlier
#print axioms HeckeSkeleton.Moments.EngineInduction.widthBand
#print axioms HeckeSkeleton.Moments.EngineInduction.widthBand_mono
#print axioms HeckeSkeleton.Moments.EngineInduction.widthBand_strict

-- Recursion
#print axioms HeckeSkeleton.Moments.EngineInduction.LocalStep
#print axioms HeckeSkeleton.Moments.EngineInduction.LocalStep.bound
#print axioms HeckeSkeleton.Moments.EngineInduction.LocalStep.uniform_rank_bound
#print axioms HeckeSkeleton.Moments.EngineInduction.localStep_power_bound
#print axioms HeckeSkeleton.Moments.EngineInduction.propagated_majorant

-- Family
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.PositiveSlotBound
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.PrimeProductBound
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.SectorBound
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.UniformBound
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.ZeroSlotBound
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.base
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.base_noSlots
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.capacity
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.energy
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.energy_nonneg
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.parameters
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.parameters_noSlots_n₁
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.parameters_noSlots_n₂
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.parameters_noSlots_z
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.positiveEligible
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.positiveSlotBound_of_sectorBound
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.primeEnergy
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.primeEnergy_nonneg
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.selectedLength
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.selectedLength_noSlots
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.slotWidth
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.uniformBound_of_sectorBound
#print axioms HeckeSkeleton.Moments.EngineInduction.SourceFamily.zeroSlotBound_of_sectorBound

-- Terminal
#print axioms HeckeSkeleton.Moments.EngineInduction.actual_child_width_drop
#print axioms HeckeSkeleton.Moments.EngineInduction.centered_divisor_saving
#print axioms HeckeSkeleton.Moments.EngineInduction.centered_exceptional_excess_le
#print axioms HeckeSkeleton.Moments.EngineInduction.centered_exceptional_excess_le_sub
#print axioms HeckeSkeleton.Moments.EngineInduction.centered_exceptional_terminal
#print axioms HeckeSkeleton.Moments.EngineInduction.centered_positive_slot_length
#print axioms HeckeSkeleton.Moments.EngineInduction.centered_positive_terminal
#print axioms HeckeSkeleton.Moments.EngineInduction.centered_zero_slot_terminal
#print axioms HeckeSkeleton.Moments.EngineInduction.child_width_drop
#print axioms HeckeSkeleton.Moments.EngineInduction.exists_coarse_loss_parameters
#print axioms HeckeSkeleton.Moments.EngineInduction.exists_fine_loss_parameters
#print axioms HeckeSkeleton.Moments.EngineInduction.exists_ordered_coarse_loss_parameters
#print axioms HeckeSkeleton.Moments.EngineInduction.finite_strict_call_count
#print axioms HeckeSkeleton.Moments.EngineInduction.positive_capacity_total_length
#print axioms HeckeSkeleton.Moments.EngineInduction.positive_slot_comparison_margin
#print axioms HeckeSkeleton.Moments.EngineInduction.slot_removal_budget
#print axioms HeckeSkeleton.Moments.EngineInduction.small_width_slot_cost
#print axioms HeckeSkeleton.Moments.EngineInduction.smaller_extraction_le_mean
#print axioms HeckeSkeleton.Moments.EngineInduction.uncentered_exceptional_excess_le
#print axioms HeckeSkeleton.Moments.EngineInduction.width_chain_drop
#print axioms HeckeSkeleton.Moments.EngineInduction.zero_slot_comparison_margin

-- ExceptionalCounting
#print axioms HeckeSkeleton.Moments.EngineInduction.SixthPowerClassification
#print axioms HeckeSkeleton.Moments.EngineInduction.SixthPowerClassification.card_le_root_bound
#print axioms HeckeSkeleton.Moments.EngineInduction.SixthPowerClassification.norm_factorization
#print axioms HeckeSkeleton.Moments.EngineInduction.SixthPowerClassification.root_encoding_injective
#print axioms HeckeSkeleton.Moments.EngineInduction.SixthPowerClassification.root_nonzero
#print axioms HeckeSkeleton.Moments.EngineInduction.SixthPowerClassification.root_norm_le
#print axioms HeckeSkeleton.Moments.EngineInduction.SixthPowerClassification.root_norm_le_power
#print axioms HeckeSkeleton.Moments.EngineInduction.sixth_power_exceptional_count
#print axioms HeckeSkeleton.Moments.EngineInduction.sixth_power_exceptional_count_strong

-- TerminalCertificate
#print axioms HeckeSkeleton.Moments.EngineInduction.TerminalComponents
#print axioms HeckeSkeleton.Moments.EngineInduction.TerminalComponents.bound
#print axioms HeckeSkeleton.Moments.EngineInduction.TerminalLedger
#print axioms HeckeSkeleton.Moments.EngineInduction.TerminalLedger.exponent_le
#print axioms HeckeSkeleton.Moments.EngineInduction.terminalBudget
#print axioms HeckeSkeleton.Moments.EngineInduction.terminalBudget_nonneg

-- Interface
#print axioms HeckeSkeleton.Moments.EngineInduction.Node
#print axioms HeckeSkeleton.Moments.EngineInduction.Node.comparison_product
#print axioms HeckeSkeleton.Moments.EngineInduction.Node.energy
#print axioms HeckeSkeleton.Moments.EngineInduction.Node.energy_nonneg
#print axioms HeckeSkeleton.Moments.EngineInduction.Node.normalizedEnergy
#print axioms HeckeSkeleton.Moments.EngineInduction.Node.ordinary
#print axioms HeckeSkeleton.Moments.EngineInduction.Node.ordinary_energy
#print axioms HeckeSkeleton.Moments.EngineInduction.Node.plainPair
#print axioms HeckeSkeleton.Moments.EngineInduction.Node.width
#print axioms HeckeSkeleton.Moments.EngineInduction.PolynomialSystem
#print axioms HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.schedule
#print axioms HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.strict_child_earlier
#print axioms HeckeSkeleton.Moments.EngineInduction.RawSingleStep
#print axioms HeckeSkeleton.Moments.EngineInduction.RawSingleStep.toSingleStep
#print axioms HeckeSkeleton.Moments.EngineInduction.RootCertificate
#print axioms HeckeSkeleton.Moments.EngineInduction.SingleStep
#print axioms HeckeSkeleton.Moments.EngineInduction.SingleStepInput

-- Induction
#print axioms HeckeSkeleton.Moments.EngineInduction.SingleStep.energy_bound
#print axioms HeckeSkeleton.Moments.EngineInduction.SingleStepInput.sectorBound
#print axioms HeckeSkeleton.Moments.EngineInduction.paired_positive_below_one
#print axioms HeckeSkeleton.Moments.EngineInduction.paired_positive_endpoint
#print axioms HeckeSkeleton.Moments.EngineInduction.paired_zero_slot_models
