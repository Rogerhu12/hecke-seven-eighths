/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeCancellationAnalytic

/-!
# From cubic Mellin decay to cancellation and prime extraction

The first lemmas turn the standard cubic decay bound for a Mellin transform
into the precise inverse-quadratic majorant needed by the contour theorem.
The final lemmas remove a separately bounded higher-prime-power remainder
and keep track of the square-root normalization exactly.
-/

noncomputable section
open Filter MeasureTheory Set Complex
open scoped Topology BigOperators ContDiff

namespace PrimeCancellation.Analytic

variable {F : ℂ → ℂ} {β : ℝ}

theorem heightWeight_le_linear (d : ZeroFreeData F β) (t : ℝ) :
    heightWeight d t ≤
      (heightConstant d + 3 * (d.k : ℝ)) * (1 + |t|) := by
  have h0 := heightConstant_nonneg d
  have hk : 0 ≤ (d.k : ℝ) := Nat.cast_nonneg _
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 4 + |t|)
  have hmul := mul_le_mul_of_nonneg_left hlog hk
  have h0x := mul_nonneg h0 (abs_nonneg t)
  have hkx := mul_nonneg hk (abs_nonneg t)
  unfold heightWeight
  nlinarith

theorem windowControl_of_cubic_decay (d : ZeroFreeData F β)
    (V : ℝ → ℂ) (l D : ℝ) (hD : 0 ≤ D)
    (hdecay : ∀ σ ∈ Icc l 2, ∀ t : ℝ,
      ‖mellin V ((σ : ℂ) + t * I)‖ ≤ D / (1 + |t|) ^ 3) :
    WindowControl d V l (D * (heightConstant d + 3 * (d.k : ℝ))) := by
  intro σ hσ t
  have hx : 0 < 1 + |t| := by positivity
  have hB : 0 ≤ heightConstant d + 3 * (d.k : ℝ) := by
    have h0 := heightConstant_nonneg d
    positivity
  calc
    ‖mellin V ((σ : ℂ) + t * I)‖ * heightWeight d t ≤
        (D / (1 + |t|) ^ 3) *
          ((heightConstant d + 3 * (d.k : ℝ)) * (1 + |t|)) :=
      mul_le_mul (hdecay σ hσ t) (heightWeight_le_linear d t)
        (heightWeight_nonneg d t) (div_nonneg hD (pow_nonneg hx.le _))
    _ = (D * (heightConstant d + 3 * (d.k : ℝ))) / (1 + |t|) ^ 2 := by
      field_simp
    _ ≤ (D * (heightConstant d + 3 * (d.k : ℝ))) / (1 + t ^ 2) := by
      apply div_le_div_of_nonneg_left (mul_nonneg hD hB) (by positivity)
      nlinarith [sq_abs t, abs_nonneg t]

theorem norm_weighted_sum_le_of_cubic_decay {ι : Type*} [Countable ι]
    (d : ZeroFreeData F β) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖ * (r i) ^ (-(2 : ℝ))))
    (heuler : ∀ s : ℂ, 1 < s.re →
      (∑' i, c i * (r i : ℂ) ^ (-s)) = -deriv F s / F s)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (δ P D : ℝ) (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 1)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hP : 1 ≤ P) (hD : 0 ≤ D)
    (hdecay : ∀ σ ∈ Icc (β + δ) 2, ∀ t : ℝ,
      ‖mellin V ((σ : ℂ) + t * I)‖ ≤ D / (1 + |t|) ^ 3) :
    ‖∑' i, c i * V (r i / P)‖ ≤
      24 * (D * (heightConstant d + 3 * (d.k : ℝ))) / δ ^ 2 * P ^ (β + δ) := by
  apply norm_weighted_sum_le d r hr c hc heuler V a b ha hsupp hV
    δ P (D * (heightConstant d + 3 * (d.k : ℝ))) hβ hβ' hδ hδ' hP
  · have h0 := heightConstant_nonneg d
    positivity
  · exact windowControl_of_cubic_decay d V (β + δ) D hD hdecay

/-- An exact prime-power decomposition and a square-root error suffice to
extract the unweighted prime sum. No prime-sum bound is among the inputs. -/
theorem norm_prime_sum_le_of_decomposition (weighted primes powers : ℂ)
    (P γ C E : ℝ) (hP : 1 ≤ P) (hγ : 1 / 2 ≤ γ) (hE : 0 ≤ E)
    (hdecomp : weighted = primes + powers)
    (hweighted : ‖weighted‖ ≤ C * P ^ γ)
    (hpowers : ‖powers‖ ≤ E * Real.sqrt P) :
    ‖primes‖ ≤ (C + E) * P ^ γ := by
  have hsqrt : Real.sqrt P ≤ P ^ γ := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hP hγ
  have heq : primes = weighted - powers := by rw [hdecomp]; ring
  rw [heq]
  calc
    ‖weighted - powers‖ ≤ ‖weighted‖ + ‖powers‖ := norm_sub_le _ _
    _ ≤ C * P ^ γ + E * Real.sqrt P := add_le_add hweighted hpowers
    _ ≤ C * P ^ γ + E * P ^ γ :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsqrt hE)
    _ = (C + E) * P ^ γ := by ring

theorem normalized_prime_sq_le_of_decomposition (weighted primes powers : ℂ)
    (P β δ C E : ℝ) (hP : 1 ≤ P) (hβ : 1 / 2 ≤ β)
    (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hdecomp : weighted = primes + powers)
    (hweighted : ‖weighted‖ ≤ C * P ^ (β + δ))
    (hpowers : ‖powers‖ ≤ E * Real.sqrt P) :
    ‖(Real.sqrt P : ℂ)⁻¹ * primes‖ ^ 2 ≤
      (C + E) ^ 2 * P ^ ((2 * β - 1) + 2 * δ) := by
  have hsum := norm_prime_sum_le_of_decomposition weighted primes powers P (β + δ) C E
    hP (by linarith) hE hdecomp hweighted hpowers
  have hnorm := PrimeCancellationAux.norm_normalized_sq_le_rpow P (β + δ) (C + E)
    (zero_lt_one.trans_le hP) (add_nonneg hC hE) primes hsum
  have hexp : 2 * (β + δ) - 1 = (2 * β - 1) + 2 * δ := by ring
  simpa only [hexp] using hnorm

end PrimeCancellation.Analytic

#print axioms PrimeCancellation.Analytic.heightWeight_le_linear
#print axioms PrimeCancellation.Analytic.windowControl_of_cubic_decay
#print axioms PrimeCancellation.Analytic.norm_weighted_sum_le_of_cubic_decay
#print axioms PrimeCancellation.Analytic.norm_prime_sum_le_of_decomposition
#print axioms PrimeCancellation.Analytic.normalized_prime_sq_le_of_decomposition
