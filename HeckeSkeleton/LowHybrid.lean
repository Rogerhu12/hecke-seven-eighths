import HeckeSkeleton.LowHybrid.ArithmeticLosses
import HeckeSkeleton.LowHybrid.Assembly
import HeckeSkeleton.LowHybrid.BlockAdmissible
import HeckeSkeleton.LowHybrid.CanonicalInputs
import HeckeSkeleton.LowHybrid.CanonicalSupport
import HeckeSkeleton.LowHybrid.ColumnMass
import HeckeSkeleton.LowHybrid.CommonTactics
import HeckeSkeleton.LowHybrid.CompletedQuadratic
import HeckeSkeleton.LowHybrid.CompletedQuadraticBound
import HeckeSkeleton.LowHybrid.Corollaries
import HeckeSkeleton.LowHybrid.Counting
import HeckeSkeleton.LowHybrid.CountingBridge
import HeckeSkeleton.LowHybrid.CountingPositivity
import HeckeSkeleton.LowHybrid.DivisorEnvelope
import HeckeSkeleton.LowHybrid.Factorization
import HeckeSkeleton.LowHybrid.Global
import HeckeSkeleton.LowHybrid.Homogeneity
import HeckeSkeleton.LowHybrid.HybridEnergy
import HeckeSkeleton.LowHybrid.Losses
import HeckeSkeleton.LowHybrid.Masks
import HeckeSkeleton.LowHybrid.NaturalLosses
import HeckeSkeleton.LowHybrid.NormalForm
import HeckeSkeleton.LowHybrid.NormalFormAlgebra
import HeckeSkeleton.LowHybrid.NormalFormBound
import HeckeSkeleton.LowHybrid.NormalFormFinite
import HeckeSkeleton.LowHybrid.NormalFormKernels
import HeckeSkeleton.LowHybrid.NormalFormSupport
import HeckeSkeleton.LowHybrid.NormalFormUniform
import HeckeSkeleton.LowHybrid.Normalization
import HeckeSkeleton.LowHybrid.Parameters
import HeckeSkeleton.LowHybrid.PrimeArithmetic
import HeckeSkeleton.LowHybrid.PrimeDivisorBounds
import HeckeSkeleton.LowHybrid.ProductBounds
import HeckeSkeleton.LowHybrid.Rows
import HeckeSkeleton.LowHybrid.SieveBounds
import HeckeSkeleton.LowHybrid.SieveComposition
import HeckeSkeleton.LowHybrid.SquarefreeDivisors
import HeckeSkeleton.LowHybrid.SupportPower
import HeckeSkeleton.LowHybrid.Transpose
import HeckeSkeleton.LowHybrid.Weighted
import HeckeSkeleton.LowHybrid.WeightedSieveBounds

/-!
# LOW-HYBRID: complete standalone finite hybrid-energy estimates

`hybrid_energy` is the original normalized mixed energy with the exact mark
mass. `hybrid_energy_with_beta_mass` permits arbitrary beta and records its
actual finite maximum squared norm. `hybrid_energy_bounded` is the displayed
unit-coefficient estimate in the task. All normal-form, divisor, harmonic,
and product-fiber data are constructed from prime coordinates and elementary
norm counting; the quadratic and cubic sieve conclusions are explicit inputs.

The project-specific ExteriorIdeal/allowed-generator dictionary is described
in WIRING_NOTES.md. No TargetContext or project source is modified.
-/
