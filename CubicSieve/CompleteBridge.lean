import CubicSieve.Complete
import CubicSieve.SkeletonBridge

/-! Exact consumer of the complete candidate, on the original arithmetic
choice and its original set S. No skeleton source file is changed. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.CompleteBridge

theorem moment_cubic_sieve (K : Type) [Field K] [NumberField K]
    (c : HeckeSkeleton.TargetContext K) : HeckeSkeleton.CubicSieveBound K c := by
  apply (SkeletonBridge.target_iff_skeleton K c).mp
  exact Complete.targetBound (HeckeSkeleton.axiomChoice K c).A
    (HeckeSkeleton.probeData K c).arithmetic (HeckeSkeleton.allowedGenerators K c)

end CubicSieve.CompleteBridge
