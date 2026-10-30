import CubicSieve.Algebra
import CubicSieve.CubicConductors
import CubicSieve.SkeletonBridge
import Lean.Util.CollectAxioms

/-! Recursively audit the completed lemmas. Conditional bridges retain their
analytic inputs as parameters; this audit does not supply those inputs. -/

open Lean Elab Command in
run_cmd do
  let names := #[
    `CubicSieve.Algebra.cubic_row_decomposition,
    `CubicSieve.Algebra.extracted_coefficients_energy_le,
    `CubicSieve.Iteration.finite_improvement,
    `CubicSieve.Bootstrap.four_thirds_of_improvement,
    `CubicSieve.Bootstrap.sharp_of_improvement,
    `CubicSieve.Improvement.improve_of_full_estimate,
    `CubicSieve.Improvement.sharp_of_full_estimates,
    `CubicSieve.FiniteKernel.hasBound_iff_norm_sq_le,
    `CubicSieve.FiniteKernel.transpose_bound_iff,
    `CubicSieve.FiniteKernel.restrict_bound,
    `CubicSieve.FiniteKernel.phase_transpose_bound,
    `CubicSieve.ExteriorKernel.positiveKernel_pow_four,
    `CubicSieve.ExteriorKernel.positiveKernel_cube_coprime_mask,
    `CubicSieve.ExteriorKernel.symbol_eq_zero_iff_not_coprime,
    `CubicSieve.ExteriorKernel.kernel_reciprocity,
    `CubicSieve.ExteriorKernel.both_orientations_of_positive,
    `CubicSieve.ExteriorSieve.B_reciprocity,
    `CubicSieve.ExteriorSieve.target_iff_sharp_bound,
    `CubicSieve.ExteriorSieve.exists_linear_product_bound,
    `CubicSieve.ExteriorSieve.targetAt_of_one_third_le,
    `CubicSieve.CubicCharacters.square_kummer_not_unramified_of_valuation,
    `CubicSieve.CubicCharacters.cubicCharacter_pow_three,
    `CubicSieve.CubicCharacters.cubicCharacter_localConductorExponent,
    `CubicSieve.CubicCharacters.cubicCharacter_idealCoefficient,
    `CubicSieve.CubicConductors.conductor_dvd_budget_mul,
    `CubicSieve.CubicConductors.conductor_outside_S,
    `CubicSieve.CubicConductors.exists_fixed_conductor_norm_bound,
    `CubicSieve.CubicConductors.character_injective_squarefree,
    `CubicSieve.CubicConductors.ratio_not_normTwist,
    `CubicSieve.Endpoint.target_of_analytic_estimates]
  for name in names do
    let deps ← Lean.collectAxioms name
    for a in deps do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unexpected dependency {a} in {name}"
    logInfo m!"CUBIC_PROVED_AXIOMS|{name}|{String.intercalate "," (deps.toList.map toString)}"
  logInfo m!"CUBIC_AUDIT_CHECKED|{names.size}"
  -- TargetContext's type already contains the admitted momentMesh.
  -- Its compatibility theorems are reported separately from the clean core.
  for name in #[`CubicSieve.SkeletonBridge.target_iff_skeleton,
      `CubicSieve.SkeletonBridge.moment_cubic_sieve_of_analytic_estimates] do
    let deps ← Lean.collectAxioms name
    for a in deps do
      unless #[`propext, `Classical.choice, `Quot.sound, `sorryAx].contains a do
        throwError "Unexpected legacy dependency {a} in {name}"
    logInfo m!"CUBIC_LEGACY_BRIDGE_AXIOMS|{name}|{String.intercalate "," (deps.toList.map toString)}"
  let original ← Lean.collectAxioms `HeckeSkeleton.moment_cubic_sieve
  logInfo m!"CUBIC_ORIGINAL_OBLIGATION_AXIOMS|{String.intercalate "," (original.toList.map toString)}"

#print axioms HeckeSkeleton.moment_cubic_sieve
#print axioms HeckeSkeleton.TargetContext
#print axioms HeckeSkeleton.momentMesh
