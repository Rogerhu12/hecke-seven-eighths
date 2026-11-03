import CubicSieve.Iteration
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Numerical end of the cubic large-sieve bootstrap, generalized from
openai/math, DirichletL/CubicSieve/Sharp.lean.

The arithmetic exponent-improvement theorem remains an explicit hypothesis.
These lemmas do not establish that theorem for the exterior-ideal kernel.
-/

set_option autoImplicit false

noncomputable section
namespace CubicSieve.Bootstrap

def HasCubicExponent (B : ℝ → ℝ → ℝ) (ξ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    B M N ≤ C * (M * N) ^ ε * (M + N ^ ξ + (M * N) ^ (2 / 3 : ℝ))

def HasSharpBound (B : ℝ → ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    B M N ≤ C * (M * N) ^ ε * (M + N + (M * N) ^ (2 / 3 : ℝ))

variable {B : ℝ → ℝ → ℝ}

/-- Finite exponent improvement and epsilon absorption reach the limiting exponent. -/
theorem four_thirds_of_improvement
    (hstart : HasCubicExponent B 2)
    (himprove : ∀ ξ : ℝ, (4 / 3 : ℝ) < ξ → ξ ≤ 2 →
      HasCubicExponent B ξ → HasCubicExponent B (Iteration.step ξ)) :
    HasCubicExponent B (4 / 3 : ℝ) := by
  intro ε hε
  obtain ⟨ξ, _hξ, _hξ2, hξε, hx⟩ := Iteration.finite_improvement hstart himprove
    (show 0 < ε / 2 by positivity)
  obtain ⟨C, hC, hb⟩ := hx (ε / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hMN : 0 < M * N := mul_pos hM0 hN0
  have hp : 1 ≤ N ^ (ε / 2) := Real.one_le_rpow hN (by positivity)
  have hNpow : N ^ ξ ≤ N ^ (4 / 3 : ℝ) * N ^ (ε / 2) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN hξε.le
  have hcross : 0 ≤ (M * N) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hMN.le _
  have hs : M + N ^ ξ + (M * N) ^ (2 / 3 : ℝ) ≤
      N ^ (ε / 2) * (M + N ^ (4 / 3 : ℝ) + (M * N) ^ (2 / 3 : ℝ)) := by
    nlinarith [mul_nonneg hM0.le (sub_nonneg.mpr hp),
      mul_nonneg hcross (sub_nonneg.mpr hp)]
  have hnp : N ^ (ε / 2) ≤ (M * N) ^ (ε / 2) :=
    Real.rpow_le_rpow hN0.le (by nlinarith) (by positivity)
  calc
    _ ≤ C * (M * N) ^ (ε / 2) *
        (M + N ^ ξ + (M * N) ^ (2 / 3 : ℝ)) := hb M N hM hN
    _ ≤ C * (M * N) ^ (ε / 2) *
        (N ^ (ε / 2) * (M + N ^ (4 / 3 : ℝ) + (M * N) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ C * (M * N) ^ (ε / 2) *
        ((M * N) ^ (ε / 2) * (M + N ^ (4 / 3 : ℝ) + (M * N) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnp (by positivity))
        (by positivity)
    _ = _ := by
      have he : (M * N) ^ (ε / 2) * (M * N) ^ (ε / 2) = (M * N) ^ ε := by
        rw [← Real.rpow_add hMN]
        congr 1
        ring
      calc
        _ = C * ((M * N) ^ (ε / 2) * (M * N) ^ (ε / 2)) *
            (M + N ^ (4 / 3 : ℝ) + (M * N) ^ (2 / 3 : ℝ)) := by ring
        _ = _ := by rw [he]

theorem four_thirds_le_cross (M N : ℝ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    N ^ (4 / 3 : ℝ) ≤ (M * N) ^ (2 / 3 : ℝ) := by
  have hN0 : 0 ≤ N := by linarith
  calc
    N ^ (4 / 3 : ℝ) = (N * N) ^ (2 / 3 : ℝ) := by
      rw [Real.mul_rpow hN0 hN0, ← Real.rpow_add (by linarith : 0 < N)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (mul_nonneg hN0 hN0)
      (mul_le_mul_of_nonneg_right hNM hN0) (by norm_num)

/-- Reciprocity turns the one-sided limiting exponent into the symmetric sharp shape. -/
theorem sharp_of_four_thirds (h : HasCubicExponent B (4 / 3 : ℝ))
    (hrecip : ∀ M N : ℝ, B M N = B N M) : HasSharpBound B := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro M N hM hN
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hcross : 0 ≤ (M * N) ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg hM0 hN0) _
  by_cases hNM : N ≤ M
  · have hh := four_thirds_le_cross M N hN hNM
    calc
      _ ≤ C * (M * N) ^ ε * (M + N ^ (4 / 3 : ℝ) + (M * N) ^ (2 / 3 : ℝ)) :=
        hb M N hM hN
      _ ≤ C * (M * N) ^ ε * (2 * (M + N + (M * N) ^ (2 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  · have hMN := le_of_not_ge hNM
    have hh := four_thirds_le_cross N M hM hMN
    have hs : N + M ^ (4 / 3 : ℝ) + (N * M) ^ (2 / 3 : ℝ) ≤
        2 * (M + N + (M * N) ^ (2 / 3 : ℝ)) := by
      rw [mul_comm N M] at hh ⊢
      linarith
    calc
      _ = B N M := hrecip M N
      _ ≤ C * (N * M) ^ ε * (N + M ^ (4 / 3 : ℝ) + (N * M) ^ (2 / 3 : ℝ)) :=
        hb N M hN hM
      _ ≤ C * (N * M) ^ ε * (2 * (M + N + (M * N) ^ (2 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [mul_comm N M]; ring

theorem sharp_of_improvement
    (hstart : HasCubicExponent B 2)
    (himprove : ∀ ξ : ℝ, (4 / 3 : ℝ) < ξ → ξ ≤ 2 →
      HasCubicExponent B ξ → HasCubicExponent B (Iteration.step ξ))
    (hrecip : ∀ M N : ℝ, B M N = B N M) : HasSharpBound B :=
  sharp_of_four_thirds (four_thirds_of_improvement hstart himprove) hrecip

end CubicSieve.Bootstrap
