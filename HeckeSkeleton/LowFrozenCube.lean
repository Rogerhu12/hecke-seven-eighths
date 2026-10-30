import HeckeSkeleton.LowFrozenCube.AggregateSource
import HeckeSkeleton.LowFrozenCube.Assembly
import HeckeSkeleton.LowFrozenCube.CoefficientSeparation
import HeckeSkeleton.LowFrozenCube.ColumnNormalization
import HeckeSkeleton.LowFrozenCube.FrozenBounds
import HeckeSkeleton.LowFrozenCube.FrozenCounts
import HeckeSkeleton.LowFrozenCube.FrozenPartition
import HeckeSkeleton.LowFrozenCube.FrozenReduction
import HeckeSkeleton.LowFrozenCube.FrozenSupportExtension
import HeckeSkeleton.LowFrozenCube.FullHybridBound
import HeckeSkeleton.LowFrozenCube.HybridExit
import HeckeSkeleton.LowFrozenCube.Ledger
import HeckeSkeleton.LowFrozenCube.LocalBudget
import HeckeSkeleton.LowFrozenCube.LocalCoefficients
import HeckeSkeleton.LowFrozenCube.LocalTable
import HeckeSkeleton.LowFrozenCube.Overlap
import HeckeSkeleton.LowFrozenCube.Phases
import HeckeSkeleton.LowFrozenCube.PowerfulCounting
import HeckeSkeleton.LowFrozenCube.PrimeCoordinates
import HeckeSkeleton.LowFrozenCube.PrimeProducts
import HeckeSkeleton.LowFrozenCube.Products
import HeckeSkeleton.LowFrozenCube.RawInput
import HeckeSkeleton.LowFrozenCube.RawRowBlockExit
import HeckeSkeleton.LowFrozenCube.RawSource
import HeckeSkeleton.LowFrozenCube.RowCoordinates
import HeckeSkeleton.LowFrozenCube.RowTableExit
import HeckeSkeleton.LowFrozenCube.Scale
import HeckeSkeleton.LowFrozenCube.SourceLedger
import HeckeSkeleton.LowFrozenCube.TableExit
import HeckeSkeleton.LowFrozenCube.TerminalSource
import HeckeSkeleton.LowFrozenCube.UniformAggregateSource
import HeckeSkeleton.LowFrozenCube.UniformAggregateTerminal
import HeckeSkeleton.LowFrozenCube.UniformSourceLedger
import HeckeSkeleton.LowFrozenCube.UniformTerminalSource
import HeckeSkeleton.LowFrozenCube.UniformWeightedHybridBound
import HeckeSkeleton.LowFrozenCube.Valuations
import HeckeSkeleton.LowFrozenCube.WeightedHybridBound

/-!
# LOW-FROZEN-CUBE: original local indices, full cubes, and source-energy bounds

The raw finite source is split using actual prime coordinates and the local
table. The full cube splits over the ordinary support only, preserving
inactive dual primes. Its coefficients, collision zeros, row blocks, and
normalization are proved before applying LOW-HYBRID. SourceLedger and
TerminalSource connect the actual source to the stated exponent ledger;
AggregateSource supplies positive finite aggregation over frozen row blocks.

These are standalone arithmetic and finite-sum theorems. See WIRING_NOTES.md
for the precise boundary with the external project's reflection objects.
-/
