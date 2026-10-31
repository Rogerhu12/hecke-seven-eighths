import HeckeSkeleton.ThetaLocal.ProjectDigitTable
import HeckeSkeleton.ThetaLocal.ProjectArchimedeanWhittaker

/-!
# Theta local wiring into HeckeGeneral

This is the entry point for `cloud_tasks/WIRE_THETA_LOCAL.md`.

The exterior-prime results use the project's actual residue characters,
principal phases, Gauss sums and finite Weyl sums.  The complex-place results
specialize the actual Whittaker vectors and Mellin pair to the Hecke character
parameters.  `directReflectionMultiplier` records the inverse-character
correction forced by the existing `archRadial` convention.

See `cloud_notes/theta_local/WIRING_REPORT.md` for the statement, normalization
audit and build evidence.  `ProjectAudit` checks the public declarations.
-/
