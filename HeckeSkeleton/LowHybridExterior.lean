import HeckeSkeleton.LowHybrid.ExteriorEnergy
import HeckeSkeleton.LowFrozenCube.ExteriorBounds

/-!
# Actual exterior-ideal mixed energy and frozen-cube bounds

Consumer entry point for `cloud_tasks/WIRE_LOW_HYBRID.md`.

* `LowHybrid.Exterior.hybrid_energy`, `hybrid_energy_with_beta_mass`, and
  `hybrid_energy_bounded` use the literal actual-ideal row.
* `LowHybrid.Exterior.completed_quadratic_energy_bounded` is the standalone
  completed quadratic estimate.
* `LowFrozenCube.Exterior.ofReflectionIndex` constructs the frozen datum
  from the project's original reflection index.
* `LowFrozenCube.Exterior.localWeylScalar_eq_ordinary` identifies the actual
  finite Weyl table, and `primitiveLocalBounds` proves its scalar bounds.
* `LowFrozenCube.Exterior.reflectedTerm_eq_rawSourceTerm` identifies the
  original reflected coefficient, retaining its Mellin kernel and weights.
* `LowFrozenCube.Exterior.reflectionSourceBlock_annularSupport` fills the
  coefficient norm conditions from the original unramified character input.
* The uniform frozen source and family theorems in
  `LowFrozenCube.Exterior` are ready for the reflected-energy consumer.

The existing abstract core and existing actual arithmetic definitions are
preserved.  This import does not use the admitted top-level `Moments` or
`Theta` skeleton to obtain either arithmetic sieve or generator data.
-/
