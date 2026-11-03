/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeCancellationFixedWindow
import PrimeCancellationPrimeSeries
import PrimeCancellationMaskCount
import PrimeCancellationUniformity

/-!
# Model-independent prime cancellation

The main theorem below derives an unweighted prime-sum estimate from
zero-free analytic data, the actual prime-power Euler identity, and linear
counting of prime objects.  Mellin decay, contour shifting, and removal of
higher powers are proved in the imported modules, not assumed here.

The constants depending on the fixed smooth window are chosen before the
zero boundary, analytic function, Euler coefficients, buffer, and scale.
All scales P >= 1 are covered, including the short-window regime.

The Hecke project adapters are separate, uncompiled files under draft/.
This file does not assert the original `HeckeSkeleton.paired_primes_below_one`.
-/

noncomputable section
open MeasureTheory Set Complex
open scoped Topology BigOperators ContDiff

namespace PrimeCancellation

open Analytic PrimeCancellationPrimeSeries

def primePowerNorm {α : Type*} (ν : α → ℝ) (np : ℕ × α) : ℝ :=
  (ν np.2) ^ (np.1 + 1)

def primePowerCoefficient {α : Type*} (ν : α → ℝ) (a : α → ℂ)
    (np : ℕ × α) : ℂ :=
  (Real.log (ν np.2) : ℂ) * (a np.2) ^ (np.1 + 1)

def primeBoundConstant {F : ℂ → ℂ} {β : ℝ} (data : ZeroFreeData F β)
    (δ D M degreeBound P₀ : ℝ) : ℝ :=
  24 * (D * (heightConstant data + 3 * (data.k : ℝ))) / δ ^ 2 +
    M * degreeBound * (1 + Real.sqrt 2) + 2 * M * degreeBound * P₀

theorem primeBoundConstant_nonneg {F : ℂ → ℂ} {β : ℝ}
    (data : ZeroFreeData F β) (δ D M degreeBound P₀ : ℝ)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hd : 0 ≤ degreeBound) (hP₀ : 0 ≤ P₀) :
    0 ≤ primeBoundConstant data δ D M degreeBound P₀ := by
  have h0 := heightConstant_nonneg data
  unfold primeBoundConstant
  positivity

/-- The fixed-window prime-sum cancellation theorem.

`PrimeArithmetic` supplies only norm >= 2, elementary linear counting and
bounded coefficients. `WindowBound` supplies the support and sup norm.
The remaining inputs are zero-free analytic data, absolute convergence on
Re(s)=2, and the prime-power Euler identity. No cancellation bound occurs
among the hypotheses.
-/
theorem exists_uniform_fixed_window_prime_bound (W : ℝ → ℂ)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1 : ℝ) 2) :
    ∃ P₀ D : ℝ, 2 ≤ P₀ ∧ 0 ≤ D ∧
      ∀ {α : Type*} [Countable α] (ν : α → ℝ) (a : α → ℂ)
        (degreeBound M : ℝ),
      PrimeArithmetic ν a degreeBound → WindowBound W M →
      ∀ (β : ℝ) (F : ℂ → ℂ) (data : ZeroFreeData F β),
      Summable (fun np : ℕ × α =>
        ‖primePowerCoefficient ν a np‖ * (primePowerNorm ν np) ^ (-(2 : ℝ))) →
      (∀ s : ℂ, 1 < s.re →
        (∑' np : ℕ × α,
          primePowerCoefficient ν a np * (primePowerNorm ν np : ℂ) ^ (-s)) =
            -deriv F s / F s) →
      ∀ δ P : ℝ, 1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 → 1 ≤ P →
        ‖primeSum ν a W P‖ ≤
          primeBoundConstant data δ D M degreeBound P₀ * P ^ (β + δ) := by
  obtain ⟨P₀, D, hP₀, hD, hweighted⟩ :=
    exists_uniform_fixed_logWindow_sum_bound W hW hWs
  refine ⟨P₀, D, hP₀, hD, ?_⟩
  intro α _ ν a degreeBound M hA hWin β F data habs heuler δ P hβ hβ' hδ hδ' hP
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hM := hWin.nonneg
  have hdegree := hA.d_nonneg
  have h0 := heightConstant_nonneg data
  have hlargeC : 0 ≤
      24 * (D * (heightConstant data + 3 * (data.k : ℝ))) / δ ^ 2 := by positivity
  have hE : 0 ≤ M * degreeBound * (1 + Real.sqrt 2) := by positivity
  have hsmallC : 0 ≤ 2 * M * degreeBound * P₀ := by positivity
  by_cases hlarge : P₀ ≤ P
  · have hr : ∀ np : ℕ × α, 0 < primePowerNorm ν np := by
      intro np
      exact pow_pos (by linarith [hA.norm_ge_two np.2]) _
    have hw := hweighted β F data (primePowerNorm ν) hr (primePowerCoefficient ν a)
      habs heuler δ P hβ hβ' hδ hδ' hlarge
    change ‖weightedSum ν a W P‖ ≤
      24 * (D * (heightConstant data + 3 * (data.k : ℝ))) / δ ^ 2 * P ^ (β + δ) at hw
    have hp := norm_prime_sum_le_of_decomposition
      (weightedSum ν a W P) (primeSum ν a W P) (tailSum ν a W P)
      P (β + δ)
      (24 * (D * (heightConstant data + 3 * (data.k : ℝ))) / δ ^ 2)
      (M * degreeBound * (1 + Real.sqrt 2)) hP (by linarith) hE
      (weightedSum_eq_primeSum_add_tailSum ν a W degreeBound M P hPpos hA hWin) hw
      (norm_tailSum_le ν a W degreeBound M P hPpos hA hWin)
    refine hp.trans ?_
    unfold primeBoundConstant
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hsmallC)
      (Real.rpow_nonneg hPpos.le _)
  · have hPP₀ : P ≤ P₀ := (lt_of_not_ge hlarge).le
    have hone : 1 ≤ P ^ (β + δ) :=
      Real.one_le_rpow hP (by linarith)
    calc
      ‖primeSum ν a W P‖ ≤ 2 * M * degreeBound * P :=
        norm_primeSum_le ν a W degreeBound M P hPpos hA hWin
      _ ≤ 2 * M * degreeBound * P₀ :=
        mul_le_mul_of_nonneg_left hPP₀ (by positivity)
      _ ≤ (2 * M * degreeBound * P₀) * P ^ (β + δ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hsmallC
      _ ≤ primeBoundConstant data δ D M degreeBound P₀ * P ^ (β + δ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hPpos.le _)
        unfold primeBoundConstant
        linarith

end PrimeCancellation

#print axioms PrimeCancellation.primeBoundConstant_nonneg
#print axioms PrimeCancellation.exists_uniform_fixed_window_prime_bound
