import CubicSieve.Initial
import Lean.Util.CollectAxioms

/-! Strict recursive audit of the actual initial exponent, including its
balanced sections, local-type cover, primitive characters and coefficient match. -/

open Lean Elab Command in
run_cmd do
  let names := #[
    `CubicSieve.Initial.hasCubicExponent_two,
    `CubicSieve.InitialArithmetic.exists_balanced_section,
    `CubicSieve.LocalTypes.typeSet_finite,
    `CubicSieve.LocalTypes.cover_of_idelic_cube,
    `CubicSieve.PrimitiveCharacters.primitiveCharacter_realizes,
    `CubicSieve.PrimitiveCharacters.primitiveCharacter_conductor,
    `CubicSieve.PrimitiveCharacters.primitiveCharacter_exterior_coefficient,
    `CubicSieve.PrimitiveCharacters.primitiveCharacter_cube,
    `CubicSieve.PrimitiveCharacters.primitiveCharacter_distinct]
  for name in names do
    let deps ← Lean.collectAxioms name
    for a in deps do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unexpected dependency {a} in {name}"
    logInfo m!"CUBIC_INITIAL_AXIOMS|{name}|{String.intercalate "," (deps.toList.map toString)}"
  logInfo m!"CUBIC_INITIAL_AUDIT_CHECKED|{names.size}"
