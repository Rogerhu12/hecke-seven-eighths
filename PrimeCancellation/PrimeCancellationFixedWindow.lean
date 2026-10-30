/-
Copyright (c) 2026. Released under the Apache 2.0 license.

Fixed smooth windows require no separate Mellin-decay premise. The window
constant below is chosen before the entire function, its zero boundary,
the Dirichlet coefficients, the buffer, and the smoothing scale.
-/
import PrimeCancellationLogProfile
import PrimeCancellationWindowControl

noncomputable section
open Filter MeasureTheory Set Complex
open scoped Topology BigOperators ContDiff

namespace PrimeCancellation.Analytic

/-- Cancellation for the logarithmically divided version of a fixed smooth
window, derived from zero-free analytic data and an absolutely convergent
Euler-series identity. No bound for a prime sum, a weighted Dirichlet sum,
or the Mellin transform is an input. -/
theorem exists_uniform_fixed_logWindow_sum_bound (W : ℝ → ℂ)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1 : ℝ) 2) :
    ∃ P₀ D : ℝ, 2 ≤ P₀ ∧ 0 ≤ D ∧
      ∀ (β : ℝ) (F : ℂ → ℂ) (d : ZeroFreeData F β),
      ∀ {ι : Type*} [Countable ι] (r : ι → ℝ) (_hr : ∀ i, 0 < r i) (c : ι → ℂ),
      Summable (fun i => ‖c i‖ * (r i) ^ (-(2 : ℝ))) →
      (∀ s : ℂ, 1 < s.re →
        (∑' i, c i * (r i : ℂ) ^ (-s)) = -deriv F s / F s) →
      ∀ δ P : ℝ, 1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 → P₀ ≤ P →
        ‖∑' i, c i * PrimeCancellationLogWindow.logWindow P W (r i / P)‖ ≤
          24 * (D * (heightConstant d + 3 * (d.k : ℝ))) / δ ^ 2 * P ^ (β + δ) := by
  obtain ⟨P₀, D, hP₀, hD, hdecay⟩ :=
    PrimeCancellationLogProfile.exists_uniform_logWindow_mellin_decay W hW hWs
  refine ⟨P₀, D, hP₀, hD, ?_⟩
  intro β F d ι _ r hr c hc heuler δ P hβ hβ' hδ hδ' hP
  have hPtwo : 2 ≤ P := hP₀.trans hP
  have hPone : 1 ≤ P := (by norm_num : (1 : ℝ) ≤ 2).trans hPtwo
  have hsupp : Function.support (PrimeCancellationLogWindow.logWindow P W) ⊆
      Icc (1 : ℝ) 2 :=
    PrimeCancellationLogWindow.support_logWindow_subset_Icc P W hWs
  have hV : ContDiff ℝ ∞ (PrimeCancellationLogWindow.logWindow P W) :=
    PrimeCancellationLogWindow.contDiff_logWindow hPtwo hW hWs
  apply norm_weighted_sum_le_of_cubic_decay d r hr c hc heuler
    (PrimeCancellationLogWindow.logWindow P W) 1 2 (by norm_num) hsupp hV
    δ P D hβ hβ' hδ hδ' hPone hD
  intro σ hσ t
  exact hdecay P hP σ ⟨by linarith [hσ.1], hσ.2⟩ t

end PrimeCancellation.Analytic

#print axioms PrimeCancellation.Analytic.exists_uniform_fixed_logWindow_sum_bound
