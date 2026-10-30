import CubicSieve.GaussPairOrbitalPoisson
import CubicSieve.ProfileGaussian
import Lean.Util.CollectAxioms

/-! Recursive guards for the literal pair modulus and the actual Gaussian
Fourier normalization. No conditional final sieve estimate is audited here. -/

open Lean Elab Command in
run_cmd do
  let names := #[
    `CubicSieve.GaussPair.pairNormalizedGauss_eq,
    `CubicSieve.GaussPairFourier.pairFourier,
    `CubicSieve.GaussPairLiteral.literal_divisorFourier,
    `CubicSieve.GaussPairOrbitalPoisson.pair_orbital_poisson,
    `CubicSieve.Profile.Gaussian.canonicalFourier_factor,
    `CubicSieve.Profile.Gaussian.physicalDual_eq_kappa]
  for name in names do
    unless (← getEnv).contains name do
      throwError "Missing endpoint {name}"
    let deps ← Lean.collectAxioms name
    for a in deps do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unexpected dependency {a} in {name}"
    logInfo m!"CUBIC_POISSON_AXIOMS|{name}|{String.intercalate "," (deps.toList.map toString)}"
  logInfo m!"CUBIC_POISSON_AUDIT_CHECKED|{names.size}"
