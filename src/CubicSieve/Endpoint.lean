import CubicSieve.ExteriorSieve
import CubicSieve.Improvement

/-!
The exact exterior-ideal target reduced to its two remaining analytic inputs.
Neither analytic input is constructed here. In particular this is not an
unconditional proof of the cubic large sieve.
-/

set_option autoImplicit false
noncomputable section

namespace CubicSieve.Endpoint

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem target_of_analytic_estimates (hD : AllowedGeneratorInput K S D)
    (hstart : Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) 2)
    (hfull : ∀ ξ : ℝ, (4 / 3 : ℝ) < ξ → ξ ≤ 2 →
      Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) ξ →
        Improvement.FullEstimate (ExteriorSieve.B K S D) ξ) :
    ExteriorSieve.TargetBound K S D := by
  apply ExteriorSieve.target_of_sharp_bound K S D
  apply Improvement.sharp_of_full_estimates hstart
  · intro M T N _ hMT _
    exact ExteriorSieve.B_mono K S D hMT le_rfl
  · exact ExteriorSieve.B_reciprocity K S D hD
  · exact hfull

end CubicSieve.Endpoint
