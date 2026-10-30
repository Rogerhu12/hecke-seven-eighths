/-
Copyright (c) 2026 OpenAI. Released under the Apache 2.0 license.

The Fourier integration-by-parts argument follows the generic portions of
OpenAI/math fd4aeeb2, CompactProfileFamily.lean and
Mellin/UniformKernelBounds.lean (Apache 2.0). This standalone formulation
keeps explicit zeroth and j-th L1 derivative bounds rather than importing
the source's number-field and Schwartz-pullback development.
-/
import PrimeCancellationCompactFamily
import PrimeCancellationWindowControl

/-!
# Explicit finite-order Mellin control

This module proves a quantitative interface for arbitrary parameter
families. The zeroth and third derivative L1 bounds of the logarithmic
profile imply a uniform cubic Mellin bound, with an explicit constant.
No compactness of the parameter set and no pre-existing Mellin-decay or
prime-cancellation estimate is assumed.

Converting standard seminorms of an original variable window W to these
two logarithmic-profile L1 quantities is a separate calculus obligation.
-/

set_option autoImplicit false
noncomputable section

namespace PrimeCancellation.MellinSeminorm

open MeasureTheory Set Filter
open scoped Classical FourierTransform ContDiff Topology
open PrimeCancellationCompactFamily

def fourierL1Constant (j : ℕ) (L₀ Lj : ℝ) : ℝ :=
  2 ^ j * (L₀ + Lj / (2 * Real.pi) ^ j)

def mellinL1Constant (j : ℕ) (L₀ Lj : ℝ) : ℝ :=
  (1 + 2 * Real.pi) ^ j * fourierL1Constant j L₀ Lj

theorem mellinL1Constant_nonneg (j : ℕ) (L₀ Lj : ℝ)
    (hL₀ : 0 ≤ L₀) (hLj : 0 ≤ Lj) :
    0 ≤ mellinL1Constant j L₀ Lj := by
  unfold mellinL1Constant fourierL1Constant
  positivity

/-- Fourier integration by parts with an explicit highest-derivative L1
bound. Integrability is supplied at every lower derivative order. -/
theorem fourier_power_le_of_deriv_L1 (f : ℝ → ℂ) (j : ℕ) (Lj : ℝ)
    (hf : ContDiff ℝ ∞ f) (hi : ∀ k : ℕ, Integrable (iteratedDeriv k f))
    (hLj : (∫ u : ℝ, ‖iteratedDeriv j f u‖) ≤ Lj) (w : ℝ) :
    |w| ^ j * ‖𝓕 f w‖ ≤ Lj / (2 * Real.pi) ^ j := by
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hf
    (fun k _ => hi k) (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 f w‖) =
      ‖𝓕 (iteratedDeriv j f) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j f) w‖ ≤ Lj :=
    (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j f) w).trans hLj
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  simpa only [mul_comm] using hn

theorem fourier_weighted_le_of_deriv_L1 (f : ℝ → ℂ) (j : ℕ) (L₀ Lj : ℝ)
    (hf : ContDiff ℝ ∞ f) (hi : ∀ k : ℕ, Integrable (iteratedDeriv k f))
    (hL₀ : (∫ u : ℝ, ‖f u‖) ≤ L₀)
    (hLj : (∫ u : ℝ, ‖iteratedDeriv j f u‖) ≤ Lj) (w : ℝ) :
    (1 + |w|) ^ j * ‖𝓕 f w‖ ≤ fourierL1Constant j L₀ Lj := by
  have hL₀non : 0 ≤ L₀ := (integral_nonneg (fun _ => norm_nonneg _)).trans hL₀
  have hLjnon : 0 ≤ Lj := (integral_nonneg (fun _ => norm_nonneg _)).trans hLj
  have hquot : 0 ≤ Lj / (2 * Real.pi) ^ j := by positivity
  have hbase : ‖𝓕 f w‖ ≤ L₀ :=
    (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) f w).trans hL₀
  have hpower := fourier_power_le_of_deriv_L1 f j Lj hf hi hLj w
  unfold fourierL1Constant
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 f w‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * L₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := (lt_of_not_ge hw).le
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 f w‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 f w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * (Lj / (2 * Real.pi) ^ j) :=
        mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem mellinLogFamily_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (Function.uncurry (mellinLogFamily V)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (-p.1 * p.2) • V (Real.exp (-p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).smul
    (hV.comp (Real.contDiff_exp.comp contDiff_snd.neg))

/-- Two finite-order L1 quantities give the Mellin decay on a fixed
vertical line. Compact support supplies all integration-by-parts hypotheses. -/
theorem mellin_weighted_le_of_log_deriv_L1 (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (σ : ℝ) (j : ℕ) (L₀ Lj : ℝ)
    (hL₀ : (∫ u : ℝ, ‖mellinLogFamily V σ u‖) ≤ L₀)
    (hLj : (∫ u : ℝ, ‖iteratedDeriv j (mellinLogFamily V σ) u‖) ≤ Lj) (t : ℝ) :
    (1 + |t|) ^ j * ‖mellin V ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      mellinL1Constant j L₀ Lj := by
  have hF := mellinLogFamily_smooth V hV
  have hs : ContDiff ℝ ∞ (mellinLogFamily V σ) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hi : ∀ k : ℕ, Integrable (iteratedDeriv k (mellinLogFamily V σ)) := by
    intro k
    exact compact_family_deriv_integrable (mellinLogFamily V) hF
      (Icc (-Real.log b) (-Real.log a)) isCompact_Icc
      (mellinLogFamily_support V a b ha hsupp) σ k
  have hb := fourier_weighted_le_of_deriv_L1 (mellinLogFamily V σ) j L₀ Lj
    hs hi hL₀ hLj (t / (2 * Real.pi))
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  rw [mellin_eq_logFamily_fourier]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j *
        ((1 + |t / (2 * Real.pi)|) ^ j * ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖) := by
      rw [mul_pow, mul_assoc]
    _ ≤ mellinL1Constant j L₀ Lj :=
      mul_le_mul_of_nonneg_left hb (by positivity)

/-- The parameter set may be arbitrary. Uniform 0th- and 3rd-order L1
bounds give the same cubic Mellin constant for every member of the family. -/
theorem family_cubic_decay_of_log_deriv_L1 {η : Type*} (V : η → ℝ → ℂ)
    (a b lo hi L₀ L₃ : ℝ) (ha : 0 < a)
    (hsupp : ∀ q, Function.support (V q) ⊆ Icc a b)
    (hV : ∀ q, ContDiff ℝ ∞ (V q))
    (hL₀ : ∀ q, ∀ σ ∈ Icc lo hi, (∫ u : ℝ, ‖mellinLogFamily (V q) σ u‖) ≤ L₀)
    (hL₃ : ∀ q, ∀ σ ∈ Icc lo hi,
      (∫ u : ℝ, ‖iteratedDeriv 3 (mellinLogFamily (V q) σ) u‖) ≤ L₃) :
    ∀ q, ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      ‖mellin (V q) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        mellinL1Constant 3 L₀ L₃ / (1 + |t|) ^ 3 := by
  intro q σ hσ t
  have hb := mellin_weighted_le_of_log_deriv_L1 (V q) a b ha (hsupp q) (hV q)
    σ 3 L₀ L₃ (hL₀ q σ hσ) (hL₃ q σ hσ) t
  apply (le_div_iff₀ (show 0 < (1 + |t|) ^ 3 by positivity)).mpr
  simpa only [mul_comm] using hb

/-- Direct quantitative cancellation from two finite-order logarithmic
profile bounds. The zero-free and Euler inputs are unchanged. -/
theorem norm_weighted_sum_le_of_log_deriv_L1 {ι : Type*} [Countable ι]
    {F : ℂ → ℂ} {β : ℝ} (data : Analytic.ZeroFreeData F β)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖ * (r i) ^ (-(2 : ℝ))))
    (heuler : ∀ s : ℂ, 1 < s.re →
      (∑' i, c i * (r i : ℂ) ^ (-s)) = -deriv F s / F s)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (δ P L₀ L₃ : ℝ) (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 1)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hP : 1 ≤ P)
    (hL₀non : 0 ≤ L₀) (hL₃non : 0 ≤ L₃)
    (hL₀ : ∀ σ ∈ Icc (β + δ) 2, (∫ u : ℝ, ‖mellinLogFamily V σ u‖) ≤ L₀)
    (hL₃ : ∀ σ ∈ Icc (β + δ) 2,
      (∫ u : ℝ, ‖iteratedDeriv 3 (mellinLogFamily V σ) u‖) ≤ L₃) :
    ‖∑' i, c i * V (r i / P)‖ ≤
      24 * (mellinL1Constant 3 L₀ L₃ *
        (Analytic.heightConstant data + 3 * (data.k : ℝ))) / δ ^ 2 * P ^ (β + δ) := by
  apply Analytic.norm_weighted_sum_le_of_cubic_decay data r hr c hc heuler V a b ha hsupp hV
    δ P (mellinL1Constant 3 L₀ L₃) hβ hβ' hδ hδ' hP
    (mellinL1Constant_nonneg 3 L₀ L₃ hL₀non hL₃non)
  intro σ hσ t
  have hb := mellin_weighted_le_of_log_deriv_L1 V a b ha hsupp hV σ 3 L₀ L₃
    (hL₀ σ hσ) (hL₃ σ hσ) t
  apply (le_div_iff₀ (show 0 < (1 + |t|) ^ 3 by positivity)).mpr
  simpa only [mul_comm] using hb

#print axioms mellinL1Constant_nonneg
#print axioms fourier_power_le_of_deriv_L1
#print axioms fourier_weighted_le_of_deriv_L1
#print axioms mellinLogFamily_smooth
#print axioms mellin_weighted_le_of_log_deriv_L1
#print axioms family_cubic_decay_of_log_deriv_L1
#print axioms norm_weighted_sum_le_of_log_deriv_L1

end PrimeCancellation.MellinSeminorm
