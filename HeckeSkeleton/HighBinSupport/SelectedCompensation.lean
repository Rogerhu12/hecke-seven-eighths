import HeckeSkeleton.HighBinSupport.HighEulerScalarBounds
/-!
# Selected ramified factors and the repeated-prime loss

The compensation used in the prime windows is computed from the same
ramified table. All five rows have the required q^(a+6e) estimate after a
single explicit cutoff. The valuation-one row additionally has a finite
algebraic cancellation, which is the source of its square-root bound.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

noncomputable section
namespace HighBin.SelectedCompensation
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open scoped ComplexConjugate

/-- The actual selected numerator for a ramified row. -/
def compensated (η L W H : ℂ) : ℂ := conj η * L * (H - 1) - W * H

/-- Once H is nonzero, this is exactly the selected numerator divided by H. -/
def normalizedCompensation (η L W H : ℂ) : ℂ :=
  conj η * (L * (H - 1)) / H - W

lemma normalizedCompensation_eq (η L W H : ℂ) (hH : H ≠ 0) :
    normalizedCompensation η L W H = compensated η L W H / H := by
  unfold normalizedCompensation compensated
  field_simp [hH]

lemma norm_lower_of_close_one (H : ℂ) (hH : ‖H - 1‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖H‖ := by
  have h := norm_sub_norm_le (1 : ℂ) H
  rw [norm_sub_rev] at h
  norm_num at h
  linarith

lemma normalizedCompensation_norm_le_weighted (η L W H : ℂ) (t : ℝ)
    (hη : ‖η‖ ≤ 1) (hH : ‖H - 1‖ ≤ 1 / 2)
    (ht : ‖L * (H - 1)‖ ≤ t) :
    ‖normalizedCompensation η L W H‖ ≤ 2 * t + ‖W‖ := by
  have hlower := norm_lower_of_close_one H hH
  have hpos : 0 < ‖H‖ := by linarith
  have ht0 : 0 ≤ t := (norm_nonneg _).trans ht
  have hnum : ‖conj η * (L * (H - 1))‖ ≤ t := by
    rw [norm_mul, Complex.norm_conj]
    calc
      ‖η‖ * ‖L * (H - 1)‖ ≤ 1 * t :=
        mul_le_mul hη ht (norm_nonneg _) (by norm_num)
      _ = t := one_mul t
  have hdiv : ‖conj η * (L * (H - 1)) / H‖ ≤ 2 * t := by
    rw [norm_div]
    apply (div_le_iff₀ hpos).mpr
    have hscale := mul_le_mul_of_nonneg_left hlower (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht0)
    nlinarith
  exact (norm_sub_le _ _).trans (add_le_add hdiv le_rfl)

/-- All repeated rows lose at most q^(a+6e), with the cutoff stated
explicitly. This is the factor absorbed by the conductor deficit. -/
theorem all_rows_selected_bound (P : PhaseData) (q a e : ℝ)
    (hq : 2 ≤ q) (ha : 1 / 2 ≤ a) (he : 0 ≤ e)
    (s w z : ℂ) (hs : s.re = a + 16 * e) (hw : w.re = 1 - a - 6 * e)
    (hz : z.re = 17 / 50) (j : Fin 5)
    (hcut : 9 * q ^ (-10 * e) ≤ 1 / 2) :
    ‖normalizedCompensation P.eta ((q : ℂ) ^ s) ((q : ℂ) ^ (-w))
      (ramifiedTableValue P q s w z j)‖ ≤ 19 * q ^ (a + 6 * e) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have htable := ramified_table_dynamic_bound P q a e hq ha he s w z hs hw hz j
  have hweighted : ‖(q : ℂ) ^ s * (ramifiedTableValue P q s w z j - 1)‖ ≤
      9 * q ^ (a + 6 * e) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    calc
      _ ≤ q ^ s.re * (9 * q ^ (-10 * e)) :=
        mul_le_mul_of_nonneg_left htable (Real.rpow_nonneg hq0.le _)
      _ = 9 * (q ^ s.re * q ^ (-10 * e)) := by ring
      _ = 9 * q ^ (s.re + (-10 * e)) := by rw [← Real.rpow_add hq0]
      _ = _ := by rw [hs]; congr 1; congr 1; ring
  have hW : ‖(q : ℂ) ^ (-w)‖ ≤ q ^ (a + 6 * e) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re, hw]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hb := normalizedCompensation_norm_le_weighted P.eta ((q : ℂ) ^ s)
    ((q : ℂ) ^ (-w)) (ramifiedTableValue P q s w z j) (9 * q ^ (a + 6 * e))
    P.eta_bound (htable.trans hcut) hweighted
  linarith

/-- The j=1 common term and special term cancel the dangerous qXY part. -/
theorem row_one_error (P : PhaseData) (q : ℝ) (hq : 0 < q) (s w z : ℂ)
    (hR : 1 - coordR P q s z ≠ 0) :
    ramifiedTableValue P q s w z 0 - 1 =
      (coordR P q s z * (1 - (q : ℂ)⁻¹) +
        P.eta * (q : ℂ) ^ (-s) * (q : ℂ) ^ (-w) * (1 - (q : ℂ) * coordV q z)) /
        (1 - coordR P q s z) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  unfold ramifiedTableValue specialTerm
  rw [phaseMonomial_eq_factored q hq]
  norm_num
  field_simp [hR, hqC]
  ring

/-- An algebraic estimate for the exact valuation-one cancellation. -/
lemma row_one_weighted_scalar_bound (η L X Y q R V : ℂ) (H : ℂ) (t : ℝ)
    (hH : H - 1 = (R * (1 - q⁻¹) + η * X * Y * (1 - q * V)) / (1 - R))
    (hR : ‖R‖ ≤ 1 / 2) (hI : ‖(1 : ℂ) - q⁻¹‖ ≤ 1)
    (hV : ‖(1 : ℂ) - q * V‖ ≤ 2)
    (hLR : ‖L * R‖ ≤ t) (hLXY : ‖L * η * X * Y‖ ≤ t) :
    ‖L * (H - 1)‖ ≤ 6 * t := by
  have ht : 0 ≤ t := (norm_nonneg _).trans hLR
  have hden : 1 / 2 ≤ ‖(1 : ℂ) - R‖ := by
    have h := norm_sub_norm_le (1 : ℂ) R
    norm_num at h
    linarith
  have hdenpos : 0 < ‖(1 : ℂ) - R‖ := by linarith
  have he : L * (H - 1) =
      ((L * R) * (1 - q⁻¹) + (L * η * X * Y) * (1 - q * V)) / (1 - R) := by
    rw [hH]
    ring
  rw [he, norm_div]
  apply (div_le_iff₀ hdenpos).mpr
  have hn := norm_add_le ((L * R) * (1 - q⁻¹)) ((L * η * X * Y) * (1 - q * V))
  rw [norm_mul (L * R) (1 - q⁻¹), norm_mul (L * η * X * Y) (1 - q * V)] at hn
  have h1 := mul_le_mul hLR hI (norm_nonneg _) ht
  have h2 := mul_le_mul hLXY hV (norm_nonneg _) ht
  have hscale := mul_le_mul_of_nonneg_left hden (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) ht)
  nlinarith

/-- A valuation-one row has no conductor-deficit loss: its selected factor
is bounded by a square root, uniformly on the final dynamic contour. -/
theorem row_one_selected_bound (P : PhaseData) (q a e : ℝ)
    (hq : 2 ≤ q) (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1 / 12)
    (s w z : ℂ) (hs : s.re = a + 16 * e) (hw : w.re = 1 - a - 6 * e)
    (hz : z.re = 17 / 50) (hcut : 9 * q ^ (-10 * e) ≤ 1 / 2) :
    ‖normalizedCompensation P.eta ((q : ℂ) ^ s) ((q : ℂ) ^ (-w))
      (ramifiedTableValue P q s w z 0)‖ ≤ 13 * q ^ (1 / 2 : ℝ) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hR := coordR_norm_le_half P q a e hq ha he s z hs hz
  have hRn : ‖coordR P q s z‖ ≤ q ^ (4 - 6 * s.re - 6 * z.re) :=
    phaseMonomial_norm_le q hq0 (P.alpha ^ 2) P.alpha_sq_bound 4 s z 6 6
  have hLR : ‖(q : ℂ) ^ s * coordR P q s z‖ ≤ q ^ (6 * e) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    calc
      _ ≤ q ^ s.re * q ^ (4 - 6 * s.re - 6 * z.re) :=
        mul_le_mul_of_nonneg_left hRn (Real.rpow_nonneg hq0.le _)
      _ = q ^ (s.re + (4 - 6 * s.re - 6 * z.re)) := by rw [← Real.rpow_add hq0]
      _ ≤ q ^ (6 * e) := by
        apply Real.rpow_le_rpow_of_exponent_le hq1
        rw [hs, hz]
        linarith
  have hW : ‖(q : ℂ) ^ (-w)‖ ≤ q ^ (6 * e) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re, hw]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hLXY : ‖(q : ℂ) ^ s * P.eta * (q : ℂ) ^ (-s) * (q : ℂ) ^ (-w)‖ ≤
      q ^ (6 * e) := by
    simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left P.eta_bound (Real.rpow_nonneg hq0.le s.re))
        (Real.rpow_nonneg hq0.le (-s.re)))
      (Real.rpow_nonneg hq0.le (-w.re))
    have hp : q ^ s.re * 1 * q ^ (-s.re) * q ^ (-w.re) = q ^ (-w.re) := by
      rw [mul_one, ← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero, one_mul]
    rw [hp] at hh
    exact hh.trans (by
      rw [hw]
      exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
  have hqV : ‖(q : ℂ) * coordV q z‖ ≤ 1 := by
    have hnormq : ‖(q : ℂ)‖ = q := by simp [abs_of_pos hq0]
    have hv : ‖coordV q z‖ = q ^ (-51 / 25 : ℝ) := by
      rw [coordV, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
      congr 1
      norm_num [Complex.mul_re, hz]
    rw [norm_mul, hnormq, hv]
    calc
      q * q ^ (-51 / 25 : ℝ) = q ^ (1 : ℝ) * q ^ (-51 / 25 : ℝ) := by rw [Real.rpow_one]
      _ = q ^ ((1 : ℝ) + (-51 / 25)) := by rw [← Real.rpow_add hq0]
      _ ≤ q ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
      _ = 1 := Real.rpow_zero q
  have hV : ‖(1 : ℂ) - (q : ℂ) * coordV q z‖ ≤ 2 := by
    have hh := norm_sub_le (1 : ℂ) ((q : ℂ) * coordV q z)
    rw [norm_one] at hh
    linarith
  have hweighted := row_one_weighted_scalar_bound P.eta ((q : ℂ) ^ s)
    ((q : ℂ) ^ (-s)) ((q : ℂ) ^ (-w)) (q : ℂ) (coordR P q s z) (coordV q z)
    (ramifiedTableValue P q s w z 0) (q ^ (6 * e))
    (row_one_error P q hq0 s w z (one_sub_R_ne_zero _ hR)) hR
    (norm_one_sub_inv_le_one q hq1) hV hLR hLXY
  have hclose := (ramified_table_dynamic_bound P q a e hq ha he s w z hs hw hz 0).trans hcut
  have hb := normalizedCompensation_norm_le_weighted P.eta ((q : ℂ) ^ s)
    ((q : ℂ) ^ (-w)) (ramifiedTableValue P q s w z 0) (6 * q ^ (6 * e))
    P.eta_bound hclose hweighted
  have hexp : q ^ (6 * e) ≤ q ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  linarith

#print axioms all_rows_selected_bound
#print axioms row_one_error
#print axioms row_one_weighted_scalar_bound
#print axioms row_one_selected_bound
end HighBin.SelectedCompensation
