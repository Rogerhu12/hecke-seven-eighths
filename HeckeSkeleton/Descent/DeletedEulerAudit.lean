import HeckeSkeleton.Descent
import Lean.Util.CollectAxioms

/-! Reject every nonstandard axiom in the arithmetic bridges and final descent. -/

open Lean Elab Command in
run_cmd do
  let names := #[
    `HeckeSkeleton.Descent.LocalNorm.primeCoefficient_heckeNormPullback,
    `HeckeSkeleton.Descent.ArtinFrobenius.primeCoefficient_artinTwist,
    `HeckeSkeleton.Descent.ArtinFrobenius.orderOf_qprime_eq_inertiaDeg,
    `HeckeSkeleton.Descent.FiniteCircleEuler.prod_fullCircleDual_one_sub_mul,
    `HeckeSkeleton.Descent.DeletedProducts.hasProd_heckeDeletedContinuation,
    `HeckeSkeleton.Descent.PrimeAssembly.deleted_artin_identity_of_good_prime_factors,
    `HeckeSkeleton.Descent.LocalIdentity.good_prime_artin_euler_identity,
    `HeckeSkeleton.Descent.DeletedEuler.artinDeletedEulerProduct,
    `HeckeSkeleton.Descent.deletedEulerFactorization,
    `HeckeSkeleton.Descent.descend]
  for name in names do
    unless (← getEnv).contains name do
      throwError "Missing descent declaration {name}"
    let deps ← Lean.collectAxioms name
    for a in deps do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unexpected dependency {a} in {name}"
    logInfo m!"DESCENT_AXIOMS|{name}|{String.intercalate "," (deps.toList.map toString)}"
  logInfo m!"DESCENT_AUDIT_CHECKED|{names.size}"

#print axioms HeckeSkeleton.Descent.descend
