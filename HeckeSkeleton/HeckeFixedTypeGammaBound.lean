import HeckeSkeleton.HeckeGammaReciprocal
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic

/-!
A fixed-infinity-type Gamma bound on the left boundary of a Hecke strip.
Angular shifts and radial parameters are arbitrary fixed real numbers;
they are not specialized to finite-order characters.

The beta-integral comparison is adapted from openai/math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/NumberTheory/CubicMoment/Estimates/GammaBetaComparison.lean,
as present in Axiom snapshot 09afbb4ce6570c1615d58509dc197fc9f0956b7d,
Analysis/Gamma/ShiftAndReflectedRatioBounds.lean.
License: Apache-2.0, full text sources/openai-math-LICENSE.txt.
Changes: retain arbitrary nonnegative angular shift a and radial shift tau.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HeckeFixedTypeGammaBound

open MeasureTheory Set
open scoped Classical ComplexConjugate

private theorem beta_real_integral_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ in (0 : ℝ)..1, t ^ (x - 1) * (1 - t) ^ (y - 1)) =
      Real.Gamma x * Real.Gamma y / Real.Gamma (x + y) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (∫ t : ℝ in (0 : ℝ)..1,
      ((t ^ (x - 1) * (1 - t) ^ (y - 1) : ℝ) : ℂ)) =
      Complex.betaIntegral (x : ℂ) (y : ℂ) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [Complex.ofReal_mul, Complex.ofReal_cpow ht.1,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2), Complex.ofReal_sub, Complex.ofReal_one]
  rw [he, Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hx) (by simpa using hy)]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, ← Complex.ofReal_add, Complex.Gamma_ofReal]

private theorem beta_norm_le_real (s : ℂ) {d : ℝ} (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.betaIntegral s (d : ℂ)‖ ≤
      Real.Gamma s.re * Real.Gamma d / Real.Gamma (s.re + d) := by
  rw [← beta_real_integral_eq s.re d hs hd]
  unfold Complex.betaIntegral
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  have hp : 0 < 1 - t := sub_pos.mpr ht.2
  rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp

/-- Beta comparison uniform in the imaginary part. -/
theorem gamma_real_shift_ratio_bound (s : ℂ) (d : ℝ)
    (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.Gamma s‖ / ‖Complex.Gamma (s + (d : ℂ))‖ ≤
      Real.Gamma s.re / Real.Gamma (s.re + d) := by
  have h := beta_norm_le_real s hs hd
  have hg : 0 < Real.Gamma d := Real.Gamma_pos_of_pos hd
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hs (by simpa using hd),
    norm_div, norm_mul, Complex.Gamma_ofReal, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hg] at h
  apply (mul_le_mul_iff_right₀ hg).mp
  convert h using 1 <;> ring

/-- The precise Gamma-C multiplier in the Hecke FE has a polynomial bound
on Re(s)=-delta, uniformly in height and for arbitrary fixed infinity type.
Reciprocal Gamma recurrence is used, so Gamma pole/default values are safe. -/
theorem gammaC_fixedType_reflected_left_bound (δ a τ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = -δ →
      ‖Complex.Gammaℂ (1 - s - (τ : ℂ) * Complex.I + (a : ℂ)) *
        (Complex.Gammaℂ (s + (τ : ℂ) * Complex.I + (a : ℂ)))⁻¹‖ ≤
          C * (2 + |s.im|) ^ 2 := by
  have hgap : 0 < 1 - 2 * δ := by linarith
  have hx : 0 < 1 + δ + a := by linarith
  have hy : 0 < 2 - δ + a := by linarith
  let A : ℝ := Real.Gamma (1 + δ + a) / Real.Gamma (2 - δ + a)
  let B : ℝ := (2 * Real.pi) ^ (-(1 + δ + a)) / (2 * Real.pi) ^ (δ - a)
  let M : ℝ := 3 + a + |τ|
  have hA : 0 < A := div_pos (Real.Gamma_pos_of_pos hx) (Real.Gamma_pos_of_pos hy)
  have hbase : 0 < 2 * Real.pi := by positivity
  have hB : 0 < B := div_pos (Real.rpow_pos_of_pos hbase _) (Real.rpow_pos_of_pos hbase _)
  have hM : 1 ≤ M := by dsimp [M]; linarith [abs_nonneg τ]
  refine ⟨B * A * M ^ 2, by positivity, ?_⟩
  intro s hs
  let w : ℂ := s + (τ : ℂ) * Complex.I + (a : ℂ)
  let z : ℂ := 1 - s - (τ : ℂ) * Complex.I + (a : ℂ)
  have hwre : w.re = a - δ := by simp [w, hs]; ring
  have hwim : w.im = s.im + τ := by simp [w]
  have hzre : z.re = 1 + δ + a := by simp [z, hs]
  have hshift : z + ((1 - 2 * δ : ℝ) : ℂ) = conj (w + 2) := by
    apply Complex.ext <;> simp [z, w, hs] <;> ring
  have hb := gamma_real_shift_ratio_bound z (1 - 2 * δ) (by rw [hzre]; exact hx) hgap
  rw [hshift, Complex.Gamma_conj, Complex.norm_conj, hzre] at hb
  have hb' : ‖Complex.Gamma z‖ / ‖Complex.Gamma (w + 2)‖ ≤ A := by
    convert hb using 1 <;> dsimp [A] <;> congr 2 <;> ring
  have hwbound : ‖w‖ ≤ M + |s.im| := by
    calc
      ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ (a + δ) + (|s.im| + |τ|) := by
        rw [hwre, hwim]
        exact add_le_add (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_add_le _ _)
      _ ≤ M + |s.im| := by dsimp [M]; linarith
  have hfactor : M + |s.im| + 1 ≤ M * (2 + |s.im|) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hM) (abs_nonneg s.im)]
  have hwpoly : ‖w‖ ≤ M * (2 + |s.im|) := by linarith
  have hw1poly : ‖w + 1‖ ≤ M * (2 + |s.im|) := by
    have hh := norm_add_le w (1 : ℂ)
    rw [norm_one] at hh
    linarith
  have hpoly : ‖w‖ * ‖w + 1‖ ≤ M ^ 2 * (2 + |s.im|) ^ 2 := by
    have hh := mul_le_mul hwpoly hw1poly (norm_nonneg _) (by positivity)
    convert hh using 1 <;> ring
  have hrec : (Complex.Gamma w)⁻¹ = w * (w + 1) * (Complex.Gamma (w + 2))⁻¹ := by
    rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one w,
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (w + 1)]
    ring_nf
  have hg : ‖Complex.Gamma z * (Complex.Gamma w)⁻¹‖ ≤
      A * (M ^ 2 * (2 + |s.im|) ^ 2) := by
    rw [hrec, norm_mul, norm_mul, norm_mul, norm_inv]
    calc
      _ = (‖Complex.Gamma z‖ / ‖Complex.Gamma (w + 2)‖) * (‖w‖ * ‖w + 1‖) := by ring
      _ ≤ _ := mul_le_mul hb' hpoly (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hA.le
  have hnorm : ‖Complex.Gammaℂ z * (Complex.Gammaℂ w)⁻¹‖ =
      B * ‖Complex.Gamma z * (Complex.Gamma w)⁻¹‖ := by
    simp only [Complex.Gammaℂ_def, norm_mul, norm_inv]
    have he1 : ‖(2 * (Real.pi : ℂ)) ^ (-z)‖ = (2 * Real.pi) ^ (-(1 + δ + a)) := by
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase]
      simp only [Complex.neg_re, hzre]
    have he2 : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ = (2 * Real.pi) ^ (δ - a) := by
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase]
      simp only [Complex.neg_re, hwre]
      congr 1 <;> ring
    rw [he1, he2]
    norm_num
    dsimp [B]
    ring
  change ‖Complex.Gammaℂ z * (Complex.Gammaℂ w)⁻¹‖ ≤ _
  rw [hnorm]
  calc
    B * ‖Complex.Gamma z * (Complex.Gamma w)⁻¹‖ ≤
        B * (A * (M ^ 2 * (2 + |s.im|) ^ 2)) := mul_le_mul_of_nonneg_left hg hB.le
    _ = _ := by ring

end HeckeSkeleton.HeckeFixedTypeGammaBound
