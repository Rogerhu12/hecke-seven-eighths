import HeckeSkeleton.WindowPIT
import Lean.Util.CollectAxioms

/-! Recursive guards for the actual upstream PIT and its original-window consumer. -/

open Lean Elab Command in
run_cmd do
  let names := #[
    `TauCeti.primeCount_univ_isEquivalent_div_log,
    `HeckeSkeleton.WindowPIT.scaled_div_tendsto,
    `HeckeSkeleton.WindowPIT.interval_lower_of_equivalent,
    `HeckeSkeleton.WindowPIT.primeCount_interval_lower,
    `HeckeSkeleton.WindowPIT.exists_positive_interval,
    `HeckeSkeleton.WindowPIT.prime_interval_card,
    `HeckeSkeleton.WindowPIT.prime_interval_mem,
    `HeckeSkeleton.WindowPIT.window_prime_lower]
  for name in names do
    unless (← getEnv).contains name do
      throwError "Missing PIT declaration {name}"
    let deps ← Lean.collectAxioms name
    for a in deps do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unexpected dependency {a} in {name}"
    logInfo m!"PIT_AXIOMS|{name}|{String.intercalate "," (deps.toList.map toString)}"
  logInfo m!"PIT_AUDIT_CHECKED|{names.size}"

#print axioms HeckeSkeleton.WindowPIT.window_prime_lower
