/-
Copyright (c) 2026 OpenAI. Released under the Apache 2.0 license.
-/
import PrimeCancellation
import PrimeCancellationSchwartzControl

/-!
# Prime cancellation controlled by a fixed finite family of source seminorms

Unlike a fixed-window existential bound, the finite seminorm family and
its constant here are chosen before the window W itself. Thus the result
can be used for varying windows once those standard seminorms are bounded.
No Mellin-decay hypothesis is present in the main statement.
-/

noncomputable section
open MeasureTheory Set Complex
open scoped Topology BigOperators ContDiff SchwartzMap

namespace PrimeCancellation.UniformProfiles

open Analytic PrimeCancellationPrimeSeries

def sourceSeminorm (s : Finset (ℕ × ℕ)) (W : SchwartzMap ℝ ℂ) : ℝ :=
  s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W

def analyticConstant {F : ℂ → ℂ} {β : ℝ} (data : ZeroFreeData F β)
    (δ C degreeBound : ℝ) : ℝ :=
  24 * C * (heightConstant data + 3 * (data.k : ℝ)) / δ ^ 2 +
    degreeBound * (1 + Real.sqrt 2) + 2 * degreeBound * Real.exp 4

theorem sourceSeminorm_nonneg (s : Finset (ℕ × ℕ)) (W : SchwartzMap ℝ ℂ) :
    0 ≤ sourceSeminorm s W := by unfold sourceSeminorm; positivity

theorem analyticConstant_nonneg {F : ℂ → ℂ} {β : ℝ}
    (data : ZeroFreeData F β) (δ C degreeBound : ℝ)
    (hC : 0 ≤ C) (hd : 0 ≤ degreeBound) :
    0 ≤ analyticConstant data δ C degreeBound := by
  have h0 := heightConstant_nonneg data
  unfold analyticConstant
  positivity

/-- A standard finite-seminorm prime-sum estimate, uniform over W itself.
All the arithmetic and analytic premises precede any cancellation estimate. -/
theorem exists_uniform_prime_seminorm_bound :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ (0, 0) ∈ s ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Icc (1 : ℝ) 2 →
      ∀ {α : Type*} [Countable α] (ν : α → ℝ) (a : α → ℂ) (degreeBound : ℝ),
      PrimeArithmetic ν a degreeBound →
      ∀ (β : ℝ) (F : ℂ → ℂ) (data : ZeroFreeData F β),
      Summable (fun np : ℕ × α =>
        ‖primePowerCoefficient ν a np‖ * (primePowerNorm ν np) ^ (-(2 : ℝ))) →
      (∀ z : ℂ, 1 < z.re →
        (∑' np : ℕ × α,
          primePowerCoefficient ν a np * (primePowerNorm ν np : ℂ) ^ (-z)) =
            -deriv F z / F z) →
      ∀ δ P : ℝ, 1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 → 1 ≤ P →
        ‖primeSum ν a W P‖ ≤
          analyticConstant data δ C degreeBound * sourceSeminorm s W * P ^ (β + δ) := by
  obtain ⟨s, C, hC, hs, hsource⟩ :=
    SchwartzControl.uniform_window_and_logWindow_source_bound
  refine ⟨s, C, hC, hs, ?_⟩
  intro W hWs α _ ν a degreeBound hA β F data habs heuler δ P hβ hβ' hδ hδ' hP
  let M := sourceSeminorm s W
  have hM : 0 ≤ M := sourceSeminorm_nonneg s W
  have hWin : WindowBound W M := ⟨hM, hWs, (hsource W hWs).1⟩
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hdegree := hA.d_nonneg
  have h0 := heightConstant_nonneg data
  have hP₀ : 2 ≤ Real.exp (4 : ℝ) := by
    have he := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hbig : 0 ≤
      24 * ((C * M) * (heightConstant data + 3 * (data.k : ℝ))) / δ ^ 2 := by
    positivity
  have htail : 0 ≤ M * degreeBound * (1 + Real.sqrt 2) := by positivity
  have hsmall : 0 ≤ 2 * M * degreeBound * Real.exp 4 := by positivity
  have hfactor : analyticConstant data δ C degreeBound * M =
      (24 * ((C * M) * (heightConstant data + 3 * (data.k : ℝ))) / δ ^ 2 +
        M * degreeBound * (1 + Real.sqrt 2)) + 2 * M * degreeBound * Real.exp 4 := by
    unfold analyticConstant
    ring
  by_cases hlarge : Real.exp 4 ≤ P
  · have hPtwo : 2 ≤ P := hP₀.trans hlarge
    have hr : ∀ np : ℕ × α, 0 < primePowerNorm ν np := by
      intro np
      exact pow_pos (by linarith [hA.norm_ge_two np.2]) _
    have hV : ContDiff ℝ ∞ (PrimeCancellationLogWindow.logWindow P W) :=
      PrimeCancellationLogWindow.contDiff_logWindow hPtwo (W.smooth ⊤) hWs
    have hVs := PrimeCancellationLogWindow.support_logWindow_subset_Icc P W hWs
    have hdecay : ∀ σ ∈ Icc (β + δ) 2, ∀ t : ℝ,
        ‖mellin (PrimeCancellationLogWindow.logWindow P W) ((σ : ℂ) + t * I)‖ ≤
          (C * M) / (1 + |t|) ^ 3 := by
      intro σ hσ t
      exact (hsource W hWs).2 P hlarge σ ⟨by linarith [hσ.1], hσ.2⟩ t
    have hw := norm_weighted_sum_le_of_cubic_decay data
      (primePowerNorm ν) hr (primePowerCoefficient ν a) habs heuler
      (PrimeCancellationLogWindow.logWindow P W) 1 2 (by norm_num) hVs hV
      δ P (C * M) hβ hβ' hδ hδ' hP (mul_nonneg hC.le hM) hdecay
    change ‖weightedSum ν a W P‖ ≤
      24 * ((C * M) * (heightConstant data + 3 * (data.k : ℝ))) / δ ^ 2 *
        P ^ (β + δ) at hw
    have hp := norm_prime_sum_le_of_decomposition
      (weightedSum ν a W P) (primeSum ν a W P) (tailSum ν a W P)
      P (β + δ)
      (24 * ((C * M) * (heightConstant data + 3 * (data.k : ℝ))) / δ ^ 2)
      (M * degreeBound * (1 + Real.sqrt 2)) hP (by linarith) htail
      (weightedSum_eq_primeSum_add_tailSum ν a W degreeBound M P hPpos hA hWin) hw
      (norm_tailSum_le ν a W degreeBound M P hPpos hA hWin)
    refine hp.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hPpos.le _)
    change _ ≤ analyticConstant data δ C degreeBound * M
    rw [hfactor]
    exact le_add_of_nonneg_right hsmall
  · have hPP₀ : P ≤ Real.exp 4 := (lt_of_not_ge hlarge).le
    have hone : 1 ≤ P ^ (β + δ) := Real.one_le_rpow hP (by linarith)
    calc
      ‖primeSum ν a W P‖ ≤ 2 * M * degreeBound * P :=
        norm_primeSum_le ν a W degreeBound M P hPpos hA hWin
      _ ≤ 2 * M * degreeBound * Real.exp 4 :=
        mul_le_mul_of_nonneg_left hPP₀ (by positivity)
      _ ≤ (2 * M * degreeBound * Real.exp 4) * P ^ (β + δ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hsmall
      _ ≤ analyticConstant data δ C degreeBound * sourceSeminorm s W *
          P ^ (β + δ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hPpos.le _)
        change _ ≤ analyticConstant data δ C degreeBound * M
        rw [hfactor]
        simpa only [zero_add] using
          add_le_add (add_nonneg hbig htail) (le_refl (2 * M * degreeBound * Real.exp 4))

end PrimeCancellation.UniformProfiles

#print axioms PrimeCancellation.UniformProfiles.sourceSeminorm_nonneg
#print axioms PrimeCancellation.UniformProfiles.analyticConstant_nonneg
#print axioms PrimeCancellation.UniformProfiles.exists_uniform_prime_seminorm_bound
