import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Complex.Basic

/-!
# Passing from a fixed profile to arbitrary tests by regularized convolution

This module is the global sum/integral and limit part of the Gaussian Mellin
deconvolution argument.  `forward` and `reverse` are fixed-profile expansions;
their identity is obtained from automorphy and weighted orbit unfolding in
the intended application.  The hypotheses below expose that prerequisite
explicitly.  In particular the final test-function reflection is never an
assumption.  Every exchange has a summable integral-norm hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GaussianTransfer

open MeasureTheory Filter
open scoped BigOperators Topology

variable {T I J : Type*} [MeasurableSpace T] [Countable I] [Countable J]
  {μ : Measure T}

/-- Integrating two equal fixed-profile expansions against a deconvolver
preserves equality, with all exchanges certified by absolute mass. -/
theorem convolve_fixed_profile
    (forward : I → T → ℂ) (reverse : J → T → ℂ) (kernel : T → ℂ)
    (hseed : ∀ᵐ t ∂μ, (∑' i, forward i t) = ∑' j, reverse j t)
    (hforward : ∀ i, Integrable (fun t => kernel t * forward i t) μ)
    (hreverse : ∀ j, Integrable (fun t => kernel t * reverse j t) μ)
    (hfmass : Summable (fun i => ∫ t, ‖kernel t * forward i t‖ ∂μ))
    (hrmass : Summable (fun j => ∫ t, ‖kernel t * reverse j t‖ ∂μ)) :
    (∑' i, ∫ t, kernel t * forward i t ∂μ) =
      ∑' j, ∫ t, kernel t * reverse j t ∂μ := by
  rw [integral_tsum_of_summable_integral_norm hforward hfmass,
    integral_tsum_of_summable_integral_norm hreverse hrmass]
  apply integral_congr_ae
  filter_upwards [hseed] with t ht
  simp only [tsum_mul_left, ht]

/-- The same result after identifying each scalar local convolution. -/
theorem regularized_identity
    (forward : I → T → ℂ) (reverse : J → T → ℂ) (kernel : T → ℂ)
    (a : I → ℂ) (b : J → ℂ)
    (hseed : ∀ᵐ t ∂μ, (∑' i, forward i t) = ∑' j, reverse j t)
    (hforward : ∀ i, Integrable (fun t => kernel t * forward i t) μ)
    (hreverse : ∀ j, Integrable (fun t => kernel t * reverse j t) μ)
    (hfmass : Summable (fun i => ∫ t, ‖kernel t * forward i t‖ ∂μ))
    (hrmass : Summable (fun j => ∫ t, ‖kernel t * reverse j t‖ ∂μ))
    (hfirst : ∀ i, (∫ t, kernel t * forward i t ∂μ) = a i)
    (hsecond : ∀ j, (∫ t, kernel t * reverse j t ∂μ) = b j) :
    (∑' i, a i) = ∑' j, b j := by
  simpa only [hfirst, hsecond] using
    convolve_fixed_profile forward reverse kernel hseed hforward hreverse hfmass hrmass

/-- Removing a regularizer requires only two explicit summable majorants.
No analytic continuation or growth assertion about a global Dirichlet
series enters this theorem. -/
theorem remove_regularizer
    (a : ℕ → I → ℂ) (b : ℕ → J → ℂ) (a₀ : I → ℂ) (b₀ : J → ℂ)
    (A : I → ℝ) (B : J → ℝ)
    (hA : Summable A) (hB : Summable B)
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (a₀ i)))
    (hb : ∀ j, Tendsto (fun n => b n j) atTop (𝓝 (b₀ j)))
    (ha_bound : ∀ n i, ‖a n i‖ ≤ A i)
    (hb_bound : ∀ n j, ‖b n j‖ ≤ B j)
    (heq : ∀ n, (∑' i, a n i) = ∑' j, b n j) :
    Summable a₀ ∧ Summable b₀ ∧ (∑' i, a₀ i) = ∑' j, b₀ j := by
  have hta := tendsto_tsum_of_dominated_convergence hA ha (Eventually.of_forall ha_bound)
  have htb := tendsto_tsum_of_dominated_convergence hB hb (Eventually.of_forall hb_bound)
  have hsa : Summable a₀ := hA.of_norm_bounded fun i =>
    le_of_tendsto ((ha i).norm) (Eventually.of_forall fun n => ha_bound n i)
  have hsb : Summable b₀ := hB.of_norm_bounded fun j =>
    le_of_tendsto ((hb j).norm) (Eventually.of_forall fun n => hb_bound n j)
  refine ⟨hsa, hsb, ?_⟩
  exact tendsto_nhds_unique (hta.congr heq) htb

/-- Full global transfer once the scalar Mellin convolution formulas have
been established.  The fixed-profile identity is independent of `a₀,b₀`.
All assumptions are included here so that the unresolved automorphic
realization cannot be hidden in a packaged final-reflection field. -/
theorem reflection_from_regularized_convolution
    (forward : I → T → ℂ) (reverse : J → T → ℂ)
    (kernel : ℕ → T → ℂ)
    (a : ℕ → I → ℂ) (b : ℕ → J → ℂ) (a₀ : I → ℂ) (b₀ : J → ℂ)
    (hseed : ∀ᵐ t ∂μ, (∑' i, forward i t) = ∑' j, reverse j t)
    (hforward : ∀ n i, Integrable (fun t => kernel n t * forward i t) μ)
    (hreverse : ∀ n j, Integrable (fun t => kernel n t * reverse j t) μ)
    (hfmass : ∀ n, Summable (fun i => ∫ t, ‖kernel n t * forward i t‖ ∂μ))
    (hrmass : ∀ n, Summable (fun j => ∫ t, ‖kernel n t * reverse j t‖ ∂μ))
    (hfirst : ∀ n i, (∫ t, kernel n t * forward i t ∂μ) = a n i)
    (hsecond : ∀ n j, (∫ t, kernel n t * reverse j t ∂μ) = b n j)
    (A : I → ℝ) (B : J → ℝ) (hA : Summable A) (hB : Summable B)
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (a₀ i)))
    (hb : ∀ j, Tendsto (fun n => b n j) atTop (𝓝 (b₀ j)))
    (ha_bound : ∀ n i, ‖a n i‖ ≤ A i)
    (hb_bound : ∀ n j, ‖b n j‖ ≤ B j) :
    Summable a₀ ∧ Summable b₀ ∧ (∑' i, a₀ i) = ∑' j, b₀ j := by
  apply remove_regularizer a b a₀ b₀ A B hA hB ha hb ha_bound hb_bound
  intro n
  exact regularized_identity forward reverse (kernel n) (a n) (b n) hseed
    (hforward n) (hreverse n) (hfmass n) (hrmass n) (hfirst n) (hsecond n)

end ThetaGlobal.GaussianTransfer

#print axioms ThetaGlobal.GaussianTransfer.reflection_from_regularized_convolution
