import CubicSieve.AnalyticDualNorm
import CubicSieve.AnalyticGcdGram
import Lean.Util.CollectAxioms

/-! Strict recursive audit of the real extraction, growth, decay and gcd
dependencies. This audit supplies no Poisson or exponent-improvement input. -/

open Lean Elab Command in
run_cmd do
  let names := #[
    `CubicSieve.AnalyticFactorization.exterior_factorization,
    `CubicSieve.AnalyticFactorization.exterior_extraction_injective,
    `CubicSieve.AnalyticRowDecomposition.extracted_kernel,
    `CubicSieve.AnalyticDyadic.energy_partition,
    `CubicSieve.AnalyticExtraction.exists_fixed_extraction_block_bound,
    `CubicSieve.AnalyticGrowth.full_ideal_growth,
    `CubicSieve.AnalyticDualNorm.U_growth,
    `CubicSieve.AnalyticDualNorm.weighted_poisson_tail,
    `CubicSieve.AnalyticDecay.weighted_two_power_majorant,
    `CubicSieve.AnalyticDecay.weighted_sieve_poisson_bound,
    `CubicSieve.AnalyticGcd.quotient_product,
    `CubicSieve.AnalyticGcd.quotient_norm,
    `CubicSieve.AnalyticGcd.gcd_pair_factor,
    `CubicSieve.AnalyticGcd.divisorEnergy_budget,
    `CubicSieve.AnalyticGcd.exists_divisorEnergy_epsilon_budget,
    `CubicSieve.AnalyticGcd.coprime_mask,
    `CubicSieve.AnalyticGcd.weighted_gram_descent,
    `CubicSieve.AnalyticGcd.pulledCoefficient_epsilon_budget]
  for name in names do
    let deps ← Lean.collectAxioms name
    for a in deps do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unexpected dependency {a} in {name}"
    logInfo m!"CUBIC_ANALYTIC_AXIOMS|{name}|{String.intercalate "," (deps.toList.map toString)}"
  logInfo m!"CUBIC_ANALYTIC_AUDIT_CHECKED|{names.size}"
