import HeckeSkeleton.PrimeCancellationWiring

/-!
Reproducible dependency audit for the actual prime-cancellation adapter.
Run after `lake build +HeckeSkeleton.PrimeCancellationWiring:olean`:

    lake env lean HeckeSkeleton/PrimeCancellationAudit.lean

The existing skeleton has admitted model data.  Printing the declarations
separately distinguishes analytic input dependencies from model-interface
dependencies; this file does not assert that the imported skeleton is complete.
-/

#print axioms HeckeSkeleton.PrimeCancellationHecke.deletedSlotData
#print axioms HeckeSkeleton.PrimeCancellationHecke.emptySlotData
#print axioms HeckeSkeleton.PrimeCancellationHecke.exists_uniform_finiteOrder_polynomial
#print axioms HeckeSkeleton.PrimeCancellationMoment.source_paired_energy_le_of_slot_bounds
#print axioms HeckeSkeleton.PrimeCancellationMoment.source_conductor_control_of_polynomial
#print axioms HeckeSkeleton.PrimeCancellationWiring.primePolynomial_bound_of_analytic_data
#print axioms HeckeSkeleton.PrimeCancellationWiring.exists_uniform_paired_prime_bound
#print axioms HeckeSkeleton.PrimeCancellationWiring.paired_primes_below_one_of_models
