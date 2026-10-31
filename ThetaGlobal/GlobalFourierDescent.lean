import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Integrated rational Fourier descent from automorphy

This file proves the global analytic identity before identifying its
Fourier coefficients with the separated ideal coefficients.  The inputs
are a rational Weyl-invariant function, its absolutely convergent
nonzero-frequency Fourier expansions, integrable majorants for exchanging
series and integral, and vanishing integrals of the constant terms.

No seed identity, marked reflection, functional equation, or separated
ideal coefficient formula is an assumption.  For the actual residual
vector, `GlobalCoreSource.lean` supplies automorphy and pointwise Fourier
reconstruction.  Angular cancellation supplies constant-term vanishing.
The remaining local evaluations and frequency reindexing are explicit
separate obligations.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ThetaGlobal.GlobalFourierDescent

variable {X I J G E : Type*} [MeasurableSpace X]

/-- Termwise integration of a nonzero-frequency Fourier expansion whose
weighted constant term has integral zero.  The absolute integral-norm
sum, not an assertion about the desired theta identity, justifies Fubini. -/
theorem integrated_fourier_of_vanishing_constant [Countable I]
    (μ : Measure X) (weight f constantTerm : X → ℂ) (a : I → X → ℂ)
    (hfourier : ∀ x, HasSum (fun i => a i x) (f x - constantTerm x))
    (ha : ∀ i, Integrable (fun x => weight x * a i x) μ)
    (ha_norm : Summable (fun i => ∫ x, ‖weight x * a i x‖ ∂μ))
    (hf : Integrable (fun x => weight x * f x) μ)
    (hc : Integrable (fun x => weight x * constantTerm x) μ)
    (hc_zero : (∫ x, weight x * constantTerm x ∂μ) = 0) :
    HasSum (fun i => ∫ x, weight x * a i x ∂μ)
      (∫ x, weight x * f x ∂μ) := by
  have hs := hasSum_integral_of_summable_integral_norm ha ha_norm
  have he : (∫ x, (∑' i, weight x * a i x) ∂μ) =
      ∫ x, weight x * f x ∂μ := by
    calc
      _ = ∫ x, (weight x * f x - weight x * constantTerm x) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change (∑' i, weight x * a i x) =
            weight x * f x - weight x * constantTerm x
          rw [((hfourier x).mul_left (weight x)).tsum_eq, mul_sub]
      _ = (∫ x, weight x * f x ∂μ) -
          ∫ x, weight x * constantTerm x ∂μ := integral_sub hf hc
      _ = ∫ x, weight x * f x ∂μ := by rw [hc_zero, sub_zero]
  exact he ▸ hs

/-- Weyl invariance and the two actual Fourier expansions yield an
equality of integrated rational-frequency series. -/
theorem integrated_fourier_weyl [Countable I] [Countable J] [Mul G]
    (μ : Measure X) (weight : X → ℂ) (theta : G → ℂ) (w : G) (g : X → G)
    (hweyl : ∀ z, theta (w * z) = theta z)
    (constant₀ constant₁ : X → ℂ) (a : I → X → ℂ) (b : J → X → ℂ)
    (hfourier₀ : ∀ x, HasSum (fun i => a i x) (theta (g x) - constant₀ x))
    (hfourier₁ : ∀ x, HasSum (fun j => b j x) (theta (w * g x) - constant₁ x))
    (ha : ∀ i, Integrable (fun x => weight x * a i x) μ)
    (ha_norm : Summable (fun i => ∫ x, ‖weight x * a i x‖ ∂μ))
    (hb : ∀ j, Integrable (fun x => weight x * b j x) μ)
    (hb_norm : Summable (fun j => ∫ x, ‖weight x * b j x‖ ∂μ))
    (hθ : Integrable (fun x => weight x * theta (g x)) μ)
    (hc₀ : Integrable (fun x => weight x * constant₀ x) μ)
    (hc₁ : Integrable (fun x => weight x * constant₁ x) μ)
    (hc₀_zero : (∫ x, weight x * constant₀ x ∂μ) = 0)
    (hc₁_zero : (∫ x, weight x * constant₁ x ∂μ) = 0) :
    (∑' i, ∫ x, weight x * a i x ∂μ) =
      ∑' j, ∫ x, weight x * b j x ∂μ := by
  have hfourier₁' : ∀ x,
      HasSum (fun j => b j x) (theta (g x) - constant₁ x) := by
    intro x
    simpa only [hweyl] using hfourier₁ x
  exact
    (integrated_fourier_of_vanishing_constant μ weight (fun x => theta (g x))
      constant₀ a hfourier₀ ha ha_norm hθ hc₀ hc₀_zero).tsum_eq.trans
    (integrated_fourier_of_vanishing_constant μ weight (fun x => theta (g x))
      constant₁ b hfourier₁' hb hb_norm hθ hc₁ hc₁_zero).tsum_eq.symm

/-- Finite digit averages preserve the pointwise nonzero-frequency
Fourier expansion, with their exact averaged constant term. -/
theorem finite_average_fourier_hasSum [Fintype E]
    (coefficient : E → ℂ) (value constantTerm : E → ℂ) (a : E → I → ℂ)
    (hfourier : ∀ d, HasSum (a d) (value d - constantTerm d)) :
    HasSum (fun i => ∑ d, coefficient d * a d i)
      ((∑ d, coefficient d * value d) - ∑ d, coefficient d * constantTerm d) := by
  have hs := hasSum_sum (s := Finset.univ) fun d _ =>
    (hfourier d).mul_left (coefficient d)
  simpa only [mul_sub, Finset.sum_sub_distrib] using hs

/-- The finite digit average can be taken before the rational Fourier
descent.  The hypotheses on integrals concern the actual averaged
coefficient functions, allowing cancellation in the finite average. -/
theorem integrated_finite_average_weyl
    [Countable I] [Countable J] [Fintype E] [Mul G]
    (μ : Measure X) (weight : X → ℂ) (theta : G → ℂ) (w : G)
    (coefficient : E → ℂ) (g : E → X → G)
    (hweyl : ∀ z, theta (w * z) = theta z)
    (constant₀ constant₁ : E → X → ℂ)
    (a : E → I → X → ℂ) (b : E → J → X → ℂ)
    (hfourier₀ : ∀ d x,
      HasSum (fun i => a d i x) (theta (g d x) - constant₀ d x))
    (hfourier₁ : ∀ d x,
      HasSum (fun j => b d j x) (theta (w * g d x) - constant₁ d x))
    (ha : ∀ i, Integrable (fun x => weight x * ∑ d, coefficient d * a d i x) μ)
    (ha_norm : Summable
      (fun i => ∫ x, ‖weight x * ∑ d, coefficient d * a d i x‖ ∂μ))
    (hb : ∀ j, Integrable (fun x => weight x * ∑ d, coefficient d * b d j x) μ)
    (hb_norm : Summable
      (fun j => ∫ x, ‖weight x * ∑ d, coefficient d * b d j x‖ ∂μ))
    (hθ : Integrable (fun x => weight x * ∑ d, coefficient d * theta (g d x)) μ)
    (hc₀ : Integrable (fun x => weight x * ∑ d, coefficient d * constant₀ d x) μ)
    (hc₁ : Integrable (fun x => weight x * ∑ d, coefficient d * constant₁ d x) μ)
    (hc₀_zero : (∫ x, weight x * ∑ d, coefficient d * constant₀ d x ∂μ) = 0)
    (hc₁_zero : (∫ x, weight x * ∑ d, coefficient d * constant₁ d x ∂μ) = 0) :
    (∑' i, ∫ x, weight x * ∑ d, coefficient d * a d i x ∂μ) =
      ∑' j, ∫ x, weight x * ∑ d, coefficient d * b d j x ∂μ := by
  have h₀ (x : X) :
      HasSum (fun i => ∑ d, coefficient d * a d i x)
        ((∑ d, coefficient d * theta (g d x)) -
          ∑ d, coefficient d * constant₀ d x) :=
    finite_average_fourier_hasSum coefficient (fun d => theta (g d x))
      (fun d => constant₀ d x) (fun d i => a d i x) (fun d => hfourier₀ d x)
  have h₁ (x : X) :
      HasSum (fun j => ∑ d, coefficient d * b d j x)
        ((∑ d, coefficient d * theta (g d x)) -
          ∑ d, coefficient d * constant₁ d x) := by
    apply finite_average_fourier_hasSum coefficient (fun d => theta (g d x))
      (fun d => constant₁ d x) (fun d j => b d j x)
    intro d
    simpa only [hweyl] using hfourier₁ d x
  exact
    (integrated_fourier_of_vanishing_constant μ weight
      (fun x => ∑ d, coefficient d * theta (g d x))
      (fun x => ∑ d, coefficient d * constant₀ d x)
      (fun i x => ∑ d, coefficient d * a d i x)
      h₀ ha ha_norm hθ hc₀ hc₀_zero).tsum_eq.trans
    (integrated_fourier_of_vanishing_constant μ weight
      (fun x => ∑ d, coefficient d * theta (g d x))
      (fun x => ∑ d, coefficient d * constant₁ d x)
      (fun j x => ∑ d, coefficient d * b d j x)
      h₁ hb hb_norm hθ hc₁ hc₁_zero).tsum_eq.symm

end ThetaGlobal.GlobalFourierDescent
