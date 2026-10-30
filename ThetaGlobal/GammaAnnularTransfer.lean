import ThetaGlobal.GammaDeconvolver

/-!
# Arbitrary-test transfer with the Gamma deconvolver actually constructed

This is the complete conditional analytic transfer interface. It assumes no
deconvolution kernel, power moments, scalar convolution identity, scalar
regularizer limit, or regularized theta identity. Those are all derived.
The independently required fixed-profile global identity is named hseed.
Consequently this theorem does not claim to prove that global prerequisite.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GammaAnnularTransfer

open MeasureTheory Filter
open AnnularTransfer GammaDeconvolver GaussianStripDecay ScalarMellinConvolution
open scoped Topology BigOperators

variable {ι C I J : Type*} [Fintype ι] [Countable I] [Countable J]

/-- The actual gamma Mellin formula supplies DeconvolverData, rather than
leaving the existence of such data as an analytic premise. -/
def profileDeconvolver (p : GammaProfile ι) (L : LocalProfiles C)
    (hM : L.M = fun t : ℝ => directGamma p ((t : ℂ) * Complex.I))
    (Vhat : ℂ → ℂ) (hV : Differentiable ℂ Vhat)
    (hVstrip : BoundedOnVerticalStrips Vhat)
    (hGamma : ExponentialStripGrowth (reciprocalGamma p))
    (ε : ℝ) (hε : 0 < ε) :
    DeconvolverData L.M (fun t => Vhat ((t : ℂ) * Complex.I)) ε := by
  rw [hM]
  exact gammaDeconvolver p Vhat hV hVstrip hGamma ε hε

/-- For an actual test V, the completed analytic transfer reduces to the
named fixed-profile global seed and ordinary local Mellin/profile estimates.
Both final series are proved summable. The direct limit is the pointwise
value V(exp x), and the reflected limit is the prescribed scalar inverse.

The two uniform-tail inputs concern the scalar transforms of the original
test. In the project they are proved on Re(s)=2 by RegularizedTestProject
and RegularizedKernelProject, without assuming the smoothed test is annular.
-/
theorem arbitrary_test_from_seed
    (p : GammaProfile ι) (L : LocalProfiles C)
    (hM : L.M = fun t : ℝ => directGamma p ((t : ℂ) * Complex.I))
    (V : ℝ → ℂ)
    (hVentire : Differentiable ℂ (mellin V))
    (hVstrip : BoundedOnVerticalStrips (mellin V))
    (hGamma : ExponentialStripGrowth (reciprocalGamma p))
    (hVconvergent : MellinConvergent V 0)
    (hVvertical : Complex.VerticalIntegrable (mellin V) 0)
    (hVcontinuous : ∀ x, 0 < x → ContinuousAt V x)
    (hRintegrable : ∀ c, Integrable (fun t : ℝ =>
      mellin V (((-t : ℝ) : ℂ) * Complex.I) * L.R c t))
    (a : I → ℂ) (b : J → ℂ) (x : I → ℝ) (y : J → ℝ) (sector : J → C)
    (ha : Summable (fun i => ‖a i‖ * Real.exp (-L.exponent * x i)))
    (hb : Summable (fun j => ‖b j‖ * Real.exp (-L.exponent * y j)))
    (hseed : ∀ u : ℝ, (∑' i, a i * L.direct (u + x i)) =
      ∑' j, b j * L.reflected (sector j) (y j - u))
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 < ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0))
    (CV CPhi : ℝ)
    (hVtail : ∀ n z,
      ‖regularizedTest (fun t => mellin V ((t : ℂ) * Complex.I)) (ε n) z‖ ≤
        CV * Real.exp (-L.exponent * z))
    (hPhitail : ∀ n c z,
      ‖regularizedReflected (fun t => mellin V ((t : ℂ) * Complex.I))
        (L.R c) (ε n) z‖ ≤ CPhi * Real.exp (-L.exponent * z)) :
    Summable (fun i => a i * V (Real.exp (x i))) ∧
      Summable (fun j => b j * inverseLine
        (fun t : ℝ => mellin V (((-t : ℝ) : ℂ) * Complex.I) * L.R (sector j) t)
        (y j)) ∧
      (∑' i, a i * V (Real.exp (x i))) =
        ∑' j, b j * inverseLine
          (fun t : ℝ => mellin V (((-t : ℝ) : ℂ) * Complex.I) * L.R (sector j) t)
          (y j) := by
  apply AnnularTransfer.arbitrary_test_reflection L
    (fun t => mellin V ((t : ℂ) * Complex.I))
    a b x y sector ha hb hseed ε
    (fun n => profileDeconvolver p L hM (mellin V) hVentire hVstrip hGamma (ε n) (hε₀ n))
    (fun z => V (Real.exp z))
    (fun c z => inverseLine
      (fun t : ℝ => mellin V (((-t : ℝ) : ℂ) * Complex.I) * L.R c t) z)
    ?_ ?_ CV CPhi hVtail hPhitail
  · intro z
    exact ScalarGaussianLimits.regularizedTest_tendsto_actual_test V
      hVconvergent hVvertical ε (fun n => (hε₀ n).le) hε₁ hε z
      (hVcontinuous _ (Real.exp_pos z))
  · intro c z
    exact ScalarGaussianLimits.regularizedReflected_tendsto
      (fun t => mellin V ((t : ℂ) * Complex.I)) (L.R c) (hRintegrable c)
      ε (fun n => (hε₀ n).le) hε₁ hε z

end ThetaGlobal.GammaAnnularTransfer

