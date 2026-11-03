import HeckeSkeleton.HeckeFixedTypeGammaBound
import HeckeSkeleton.HeckeGammaQualitativeGrowth

/-!
A polynomial Gamma bound on the complete dynamic-w interval of a high row.
The actual numerator row character is finite order, so over a totally
complex field its Gamma profile has zero radial and angular shifts.
No finite-order condition is imposed on the target/background character.

The proof uses the beta comparison from HeckeFixedTypeGammaBound, whose
upstream source and Apache-2.0 provenance are recorded there. The compact
real bounds use the generic elementary Gamma estimates recorded in
HeckeGammaQualitativeGrowth. Recurrence is applied to reciprocal Gamma,
so the proof includes w=0 and all totalized Gamma pole values.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HeckeDynamicGammaBound

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open HeckeSkeleton.HeckeFixedTypeGammaBound HeckeSkeleton.HeckeGammaQualitativeGrowth
open scoped Classical BigOperators ComplexConjugate

/-- One absolute constant works for the whole dynamic real interval.
The denominator occurs as the entire reciprocal Gamma factor. -/
theorem gammaC_reflected_dynamic_bound :
    ∃ G : ℝ, 0 < G ∧ ∀ w : ℂ, -(1 / 1000 : ℝ) ≤ w.re ∧ w.re ≤ 1 / 2 →
      ‖Complex.Gammaℂ (1 - w) * (Complex.Gammaℂ w)⁻¹‖ ≤
        G * (2 + |w.im|) ^ 2 := by
  obtain ⟨M, hM, hMb⟩ := gamma_real_interval_bound
    (a := (1 / 2 : ℝ)) (b := 2) (by norm_num)
  obtain ⟨A, hA, hAb⟩ := gamma_inverse_strip_exp_bound 1 3 (by norm_num)
  refine ⟨M * A, mul_pos hM hA, ?_⟩
  intro w hw
  have hnum : Real.Gamma (1 - w.re) ≤ M :=
    hMb _ ⟨by linarith [hw.2], by linarith [hw.1]⟩
  have hden : 0 < Real.Gamma (2 + w.re) :=
    Real.Gamma_pos_of_pos (by linarith [hw.1])
  have hinv : (Real.Gamma (2 + w.re))⁻¹ ≤ A := by
    have h := hAb ((2 + w.re : ℝ) : ℂ)
      ⟨by simp only [Complex.ofReal_re]; linarith [hw.1],
        by simp only [Complex.ofReal_re]; linarith [hw.2]⟩
    simpa only [Complex.Gamma_ofReal, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hden, Complex.ofReal_im, abs_zero,
      mul_zero, Real.exp_zero, mul_one] using h
  have hr : Real.Gamma (1 - w.re) / Real.Gamma (2 + w.re) ≤ M * A := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hnum hinv (inv_nonneg.mpr hden.le) hM.le
  have hshift : (1 - w) + ((1 + 2 * w.re : ℝ) : ℂ) = conj (w + 2) := by
    apply Complex.ext <;> simp <;> ring
  have hb := gamma_real_shift_ratio_bound (1 - w) (1 + 2 * w.re)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith [hw.2])
    (by linarith [hw.1])
  rw [hshift, Complex.Gamma_conj, Complex.norm_conj] at hb
  have hmain : ‖Complex.Gamma (1 - w)‖ / ‖Complex.Gamma (w + 2)‖ ≤ M * A := by
    apply hb.trans
    convert hr using 1 <;> simp only [Complex.sub_re, Complex.one_re] <;> congr 2 <;> ring
  have hwabs : |w.re| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hw.1], hw.2⟩
  have hwnorm : ‖w‖ ≤ 2 + |w.im| := by
    have hn := Complex.norm_le_abs_re_add_abs_im w
    linarith
  have hw1norm : ‖w + 1‖ ≤ 2 + |w.im| := by
    have hn := norm_add_le w (1 : ℂ)
    rw [norm_one] at hn
    have hwn := Complex.norm_le_abs_re_add_abs_im w
    linarith
  have hpoly : ‖w‖ * ‖w + 1‖ ≤ (2 + |w.im|) ^ 2 := by
    have h := mul_le_mul hwnorm hw1norm (norm_nonneg _) (by positivity)
    simpa only [pow_two] using h
  have hrec : (Complex.Gamma w)⁻¹ =
      w * (w + 1) * (Complex.Gamma (w + 2))⁻¹ := by
    rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one w,
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (w + 1)]
    ring_nf
  have hcore : ‖Complex.Gamma (1 - w) * (Complex.Gamma w)⁻¹‖ ≤
      (M * A) * (2 + |w.im|) ^ 2 := by
    rw [hrec, norm_mul, norm_mul, norm_mul, norm_inv]
    calc
      _ = (‖Complex.Gamma (1 - w)‖ / ‖Complex.Gamma (w + 2)‖) *
          (‖w‖ * ‖w + 1‖) := by ring
      _ ≤ _ := mul_le_mul hmain hpoly
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_pos hM hA).le
  have hbase : 0 < 2 * Real.pi := by positivity
  have hnorm : ‖Complex.Gammaℂ (1 - w) * (Complex.Gammaℂ w)⁻¹‖ =
      ((2 * Real.pi) ^ (-(1 - w.re)) / (2 * Real.pi) ^ (-w.re)) *
        ‖Complex.Gamma (1 - w) * (Complex.Gamma w)⁻¹‖ := by
    simp only [Complex.Gammaℂ_def, norm_mul, norm_inv]
    have h1 : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - w))‖ =
        (2 * Real.pi) ^ (-(1 - w.re)) := by
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase]
      simp only [Complex.neg_re, Complex.sub_re, Complex.one_re]
    have h2 : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ = (2 * Real.pi) ^ (-w.re) := by
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase, Complex.neg_re]
    rw [h1, h2]
    norm_num
    ring
  have hscale : (2 * Real.pi) ^ (-(1 - w.re)) / (2 * Real.pi) ^ (-w.re) ≤ 1 := by
    rw [← Real.rpow_sub hbase]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [Real.pi_gt_three]) (by linarith [hw.2])
  rw [hnorm]
  exact (mul_le_mul hscale hcore (norm_nonneg _) (by positivity)).trans_eq (one_mul _)

variable (K : Type) [Field K] [NumberField K]

/-- The actual finite-order row profile, with all infinite places retained. -/
theorem canonicalGammaProfile_finiteOrder_of_complex
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : FiniteOrder χ) (w : ℂ) :
    canonicalHeckeGammaProfile K χ w =
      Complex.Gammaℂ w ^ Fintype.card (InfinitePlace K) := by
  rw [canonicalHeckeGammaProfile, heckeGammaProfile]
  calc
    _ = ∏ _v : InfinitePlace K, Complex.Gammaℂ w := by
      apply Finset.prod_congr rfl
      intro v _
      rw [if_neg (v.not_isReal_iff_isComplex.mpr (hcomplex v)),
        heckeRadialParameter_finiteOrder K v hχ,
        heckeArchWeight_of_complex K χ v (hcomplex v),
        heckeComplexWeight_finiteOrder K v (hcomplex v) hχ]
      simp
    _ = _ := by simp

/-- A character-uniform bound for the exact numerator Gamma multiplier of
the physical high-row FE. The target character does not occur here. -/
theorem exists_uniform_finiteOrder_reflectedGamma_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) :
    ∃ G : ℝ, 0 < G ∧ ∀ χ : HeckeCharacter K, FiniteOrder χ → ∀ w : ℂ,
      -(1 / 1000 : ℝ) ≤ w.re ∧ w.re ≤ 1 / 2 →
      ‖(canonicalHeckeGammaProfile K χ w)⁻¹ *
        canonicalHeckeGammaProfile K χ⁻¹ (1 - w)‖ ≤
          G * (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨G, hG, hGb⟩ := gammaC_reflected_dynamic_bound
  let n := Fintype.card (InfinitePlace K)
  refine ⟨G ^ n, pow_pos hG _, ?_⟩
  intro χ hχ w hw
  rw [canonicalGammaProfile_finiteOrder_of_complex K hcomplex χ hχ,
    canonicalGammaProfile_finiteOrder_of_complex K hcomplex χ⁻¹ hχ.inv]
  have heq : (Complex.Gammaℂ w ^ n)⁻¹ * Complex.Gammaℂ (1 - w) ^ n =
      (Complex.Gammaℂ (1 - w) * (Complex.Gammaℂ w)⁻¹) ^ n := by
    rw [mul_pow, inv_pow, mul_comm]
  change ‖(Complex.Gammaℂ w ^ n)⁻¹ * Complex.Gammaℂ (1 - w) ^ n‖ ≤ _
  rw [heq, norm_pow]
  calc
    _ ≤ (G * (2 + |w.im|) ^ 2) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) (hGb w hw) n
    _ = G ^ n * (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
      rw [mul_pow, ← pow_mul]

end HeckeSkeleton.HeckeDynamicGammaBound
