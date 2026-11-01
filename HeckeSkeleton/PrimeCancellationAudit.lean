import HeckeSkeleton.PrimeCancellationWiring
import Lean.Util.CollectAxioms

/-!
Reproducible dependency audit for the actual prime-cancellation adapter.
Run after `lake build +HeckeSkeleton.PrimeCancellationWiring:olean`:

    lake env lean HeckeSkeleton/PrimeCancellationAudit.lean

The adapters import the actual source data directly, below the moment
theorem layer.  Printing the declarations separately records analytic
input dependencies and the exact source-index dependencies.
-/

/-! The explicit-index main theorems must pass the strict recursive whitelist.
The original source-index compatibility interface is audited separately below. -/

open Lean Elab Command in
run_cmd do
  let names := #[
    `HeckeSkeleton.PrimeCancellationExplicit.exists_uniform_paired_prime_bound,
    `HeckeSkeleton.PrimeCancellationExplicit.paired_primes_below_one_of_explicit_models]
  for name in names do
    unless (← getEnv).contains name do
      throwError "Missing prime-cancellation declaration {name}"
    let deps ← Lean.collectAxioms name
    for a in deps do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unexpected dependency {a} in {name}"
    logInfo m!"PRIME_CANCELLATION_CLEAN_AXIOMS|{name}|{String.intercalate "," (deps.toList.map toString)}"
  logInfo m!"PRIME_CANCELLATION_CLEAN_AUDIT_CHECKED|{names.size}"

#print axioms HeckeSkeleton.PrimeCancellationExplicit.exists_uniform_paired_prime_bound
#print axioms HeckeSkeleton.PrimeCancellationExplicit.paired_primes_below_one_of_explicit_models
#print axioms HeckeSkeleton.PrimeCancellationExplicit.ExplicitModelFamily
#print axioms HeckeSkeleton.PrimeCancellationExplicit.exists_paired_linear_count
#print axioms HeckeSkeleton.PrimeCancellationMoment.canonicalFixedBadPrimeSupport

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

-- The original expansion data occur in the actual source index itself.
#print axioms HeckeSkeleton.highExpansion
#print axioms HeckeSkeleton.rows_in_norm_envelope
#print axioms HeckeSkeleton.targetData
#print axioms HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.ActualSourceIndex
