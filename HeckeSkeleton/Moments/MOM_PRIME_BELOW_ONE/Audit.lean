import HeckeSkeleton.Moments
import Lean.Util.CollectAxioms

/-! The actual model contract and the original skeleton target must both
have only Lean's three standard axioms. This module is included in the
whole-project library build, so a nonstandard dependency fails that gate. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let targets := [
    ``HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.actual_prime_conductor_norm_bound,
    ``HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.actualPrimeWindow_uniform_seminorm,
    ``HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.actualPrimeSlotModelControl,
    ``HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.actual_paired_primes_below_one,
    ``HeckeSkeleton.paired_primes_below_one]
  for name in targets do
    unless (← getEnv).contains name do
      throwError "MOM_PRIME_BELOW_ONE missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "MOM_PRIME_BELOW_ONE nonstandard axiom in {name}: {ax}"
    logInfo m!"MOM_PRIME_BELOW_ONE_CLEAN_AXIOMS|{name}|{axioms}"
  logInfo m!"MOM_PRIME_BELOW_ONE_CLEAN_AUDIT_CHECKED|{targets.length}"

#print axioms HeckeSkeleton.paired_primes_below_one
