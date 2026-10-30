import HeckeSkeleton.PrimeCancellationWiring

/-!
Reproducible dependency audit for the actual prime-cancellation adapter.
Run after `lake build +HeckeSkeleton.PrimeCancellationWiring:olean`:

    lake env lean HeckeSkeleton/PrimeCancellationAudit.lean

The existing skeleton has admitted model data.  Printing the declarations
separately distinguishes analytic input dependencies from model-interface
dependencies; this file does not assert that the imported skeleton is complete.
-/

#print axioms HeckeSkeleton.PrimeCancellationHecke.exists_ideal_count_bound
#print axioms HeckeSkeleton.PrimeCancellationHecke.actualPrimeArithmetic
#print axioms HeckeSkeleton.PrimeCancellationHecke.deletedSlotData
#print axioms HeckeSkeleton.PrimeCancellationHecke.emptySlotData
#print axioms HeckeSkeleton.PrimeCancellationHecke.exists_uniform_finiteOrder_polynomial
#print axioms HeckeSkeleton.PrimeCancellationWindows.actualPrimeWindowSchwartz_uniform_seminorm
#print axioms HeckeSkeleton.PrimeCancellationBounds.absorb_slot_logarithms
#print axioms HeckeSkeleton.PrimeCancellationMoment.logQ_le_of_norm_polynomial
#print axioms HeckeSkeleton.PrimeCancellationMoment.source_paired_energy_le_of_slot_bounds
#print axioms HeckeSkeleton.PrimeCancellationMoment.source_conductor_control_of_polynomial
#print axioms HeckeSkeleton.PrimeCancellationMoment.decomposedMomentDataWithSlots_inverse_mem
#print axioms HeckeSkeleton.PrimeCancellationMoment.inverse_mem_restrictSlots
#print axioms HeckeSkeleton.PrimeCancellationWiring.primePolynomial_bound_of_analytic_data
#print axioms HeckeSkeleton.PrimeCancellationWiring.exists_uniform_paired_prime_bound
#print axioms HeckeSkeleton.PrimeCancellationWiring.paired_primes_below_one_of_models

-- The original expansion data occur in SourceMomentIndex itself.
#print axioms HeckeSkeleton.highExpansion
#print axioms HeckeSkeleton.rows_in_norm_envelope
#print axioms HeckeSkeleton.targetData
#print axioms HeckeSkeleton.SourceMomentIndex
