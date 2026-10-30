module

public import HeckeSkeleton.Theta
public import Lean.Util.CollectAxioms

/-!
# Admission gate for the five THETA_GLOBAL entry points

This audit uses the actual skeleton declarations after their complete
dependency closure has been built. It deliberately rejects `sorryAx` and
every nonstandard axiom, including any inherited through a source
constructor. The two local input packages remain explicit parameters.

The presence of this file is not a compilation certificate. A successful
run must print all five `THETA_GLOBAL_AXIOMS` records and exit with code 0.
-/

open Lean Elab Command in
run_cmd do
  for name in #[`HeckeSkeleton.finiteMellinData,
      `HeckeSkeleton.finite_valuation_cutoff,
      `HeckeSkeleton.finite_valuation_decay,
      `HeckeSkeleton.marked_reflected_absolute,
      `HeckeSkeleton.marked_reflection] do
    unless ((← getEnv).find? name).isSome do
      throwError "THETA_GLOBAL entry {name} was not imported"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "THETA_GLOBAL entry {name} depends on forbidden axiom {axiomName}"
    logInfo m!"THETA_GLOBAL_AXIOMS|{name}|{String.intercalate "," (axioms.toList.map toString)}"
