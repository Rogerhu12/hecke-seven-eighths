import HeckeSkeleton.HeckeHighRowLRatio
import HeckeSkeleton.FiniteOrderKernelOpen
import ActualCanonicalRowConsumers
import RowCharacterNormTwistExclusion

/-!
Verified arithmetic inputs for the original physical row provider.

The internal imports are deliberately first: the isolated external proofs
refer to these exact HeckeSkeleton modules. The external-input manifest
registers their source, successful native evidence, and dependency closure.

Canonical character identification follows from the existing all-ideal
coefficient calibration. The conductor bound therefore adds no calibration
or conductor assumption. Norm-twist exclusion uses the original allowed
generator condition; its target specialization still depends on the three
named AR-ALLOWED obligations until the actual data constructor is connected.
-/
