import CubicSieve.GaussPoissonFinite
import CubicSieve.OrbitDualNorm
import CubicSieve.CoprimeGramDual
import Lean.Util.CollectAxioms

/-! Recursive axiom guard for the arithmetic and all-sector operator bridges. -/

open Lean Elab Command in
run_cmd do
  let names := #[
    `CubicSieve.Gauss.crt_fourier_conj,
    `CubicSieve.GaussSquarefree.quotientFunction_eq_product,
    `CubicSieve.GaussSquarefree.mixedRow_fourier,
    `CubicSieve.GaussSquarefree.thetaGamma_norm,
    `CubicSieve.GaussCharacters.quotientCubicCharacter_cube,
    `CubicSieve.GaussPoissonFinite.divisorFourier_eq,
    `CubicSieve.OrbitRows.orbitEquiv,
    `CubicSieve.OrbitRows.scalarOrbit_norm,
    `CubicSieve.OrbitKernel.coefficient_classOrbit,
    `CubicSieve.OrbitDualNorm.orbital_family_bound,
    `CubicSieve.CoprimeGramDual.coprime_family_bound]
  for name in names do
    let deps ← Lean.collectAxioms name
    for a in deps do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unexpected dependency {a} in {name}"
    logInfo m!"CUBIC_ARITHMETIC_OPERATOR_AXIOMS|{name}|{String.intercalate "," (deps.toList.map toString)}"
  logInfo m!"CUBIC_ARITHMETIC_OPERATOR_AUDIT_CHECKED|{names.size}"
