import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileNormTwists
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileEuler
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.CanonicalProfileControl
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let namespacePrefix := `HeckeSkeleton.Moments.UniformAmplify
  let names := (env.constants.fold (init := (#[] : Array Name)) fun acc name _ =>
    if namespacePrefix.isPrefixOf (privateToUserName name) then acc.push name else acc).qsort Name.lt
  unless names.size > 0 do
    throwError "The MOM_UNIFORM_AMPLIFY namespace is missing"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"MOM_UNIFORM_AMPLIFY_AXIOMS|{name}|{dependencies}"
  logInfo m!"MOM_UNIFORM_AMPLIFY_ANALYSISAUDIT_PASSED|{names.size}"

