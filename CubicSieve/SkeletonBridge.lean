import CubicSieve.Endpoint
import HeckeSkeleton.Moments

/-! Exact comparison with the existing obligation. No skeleton file is changed. -/

set_option autoImplicit false
noncomputable section

namespace CubicSieve.SkeletonBridge

variable (K : Type) [Field K] [NumberField K]
variable (c : HeckeSkeleton.TargetContext K)

theorem target_iff_skeleton :
    ExteriorSieve.TargetBound K (HeckeSkeleton.places K c)
      (HeckeSkeleton.probeData K c).arithmetic ↔ HeckeSkeleton.CubicSieveBound K c :=
  Iff.rfl

/-- The original target follows once its actual initial and improvement estimates
are proved. Those estimates remain explicit parameters of this theorem. -/
theorem moment_cubic_sieve_of_analytic_estimates
    (hstart : Bootstrap.HasCubicExponent
      (ExteriorSieve.B K (HeckeSkeleton.places K c)
        (HeckeSkeleton.probeData K c).arithmetic) 2)
    (hfull : ∀ ξ : ℝ, (4 / 3 : ℝ) < ξ → ξ ≤ 2 →
      Bootstrap.HasCubicExponent
        (ExteriorSieve.B K (HeckeSkeleton.places K c)
          (HeckeSkeleton.probeData K c).arithmetic) ξ →
      Improvement.FullEstimate
        (ExteriorSieve.B K (HeckeSkeleton.places K c)
          (HeckeSkeleton.probeData K c).arithmetic) ξ) :
    HeckeSkeleton.CubicSieveBound K c :=
  (target_iff_skeleton K c).mp
    (Endpoint.target_of_analytic_estimates K (HeckeSkeleton.places K c)
      (HeckeSkeleton.probeData K c).arithmetic (HeckeSkeleton.allowedGenerators K c)
      hstart hfull)

end CubicSieve.SkeletonBridge
