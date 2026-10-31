import HeckeSkeleton.HighBinSupport.SelectedCompensation

/-!
# Ramified Euler factors on the outer small-row contour

All five formulas are the actual normalized phase table used by the Euler
provider.  These estimates only use the real-part inequalities of the outer
contour and the proved phase norms.  There is no row-count, final correction
bound or L-function estimate among the premises.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.SmallRows

open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HighBin.SelectedCompensation
open scoped ComplexConjugate

private theorem weighted_phaseMonomial_norm_le
    {q : ℝ} (hq : 1 ≤ q) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (r : ℝ) (s w : ℂ) (m n : ℕ) {b : ℝ}
    (hb : r - ((m : ℝ) - 1) * s.re - (n : ℝ) * w.re ≤ b) :
    ‖(q : ℂ) ^ s * phaseMonomial q c r s w m n‖ ≤ q ^ b := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  calc
    _ ≤ q ^ s.re * q ^ (r - (m : ℝ) * s.re - (n : ℝ) * w.re) :=
      mul_le_mul_of_nonneg_left (phaseMonomial_norm_le q hq0 c hc r s w m n)
        (Real.rpow_nonneg hq0.le _)
    _ = q ^ (r - ((m : ℝ) - 1) * s.re - (n : ℝ) * w.re) := by
      rw [← Real.rpow_add hq0]
      congr 1
      ring
    _ ≤ q ^ b := Real.rpow_le_rpow_of_exponent_le hq hb

private theorem ramifiedCorrection_weighted_norm_sub_one_le
    (L B D R V : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hR : ‖R‖ ≤ 1 / 2) (hV : ‖V‖ ≤ 1 / 4)
    (hB : ‖L * B‖ ≤ 2 * t) (hD : ‖L * D‖ ≤ 2 * t) :
    ‖L * (ramifiedCorrection B D R V - 1)‖ ≤ 9 * t := by
  have h := ramifiedCorrection_norm_sub_one_le (L * B) (L * D) R V t ht hR hV hB hD
  have heq : L * (ramifiedCorrection B D R V - 1) =
      ramifiedCorrection (L * B) (L * D) R V - 1 := by
    unfold ramifiedCorrection
    ring
  rwa [heq]

private theorem small_coordR_norm_le_half (P : PhaseData) {q : ℝ} (hq : 2 ≤ q)
    (s z : ℂ) (hs : 7 / 8 ≤ s.re) (hz : 17 / 50 ≤ z.re) :
    ‖coordR P q s z‖ ≤ 1 / 2 := by
  have hq1 : 1 ≤ q := by linarith
  have hR : ‖coordR P q s z‖ ≤ q ^ (-1 : ℝ) := by
    unfold coordR
    apply phaseMonomial_norm_le_of_exponent_le q hq1 _ P.alpha_sq_bound
    norm_num
    linarith
  calc
    _ ≤ q ^ (-1 : ℝ) := hR
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
    _ = 1 / 2 := by norm_num

private theorem outer_coordV_norm_le_quarter {q : ℝ} (hq : 2 ≤ q)
    (z : ℂ) (hz : 17 / 50 ≤ z.re) : ‖coordV q z‖ ≤ 1 / 4 := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hV : ‖coordV q z‖ ≤ q ^ (-2 : ℝ) := by
    unfold coordV
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    apply Real.rpow_le_rpow_of_exponent_le hq1
    norm_num [Complex.mul_re]
    linarith
  calc
    _ ≤ q ^ (-2 : ℝ) := hV
    _ ≤ (2 : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
    _ = 1 / 4 := by norm_num

/-- Multiplication by q^s exposes the genuine square-root cost of every
ramified valuation.  The common and special terms retain their phases. -/
theorem ramified_small_weighted_error (P : PhaseData) {q : ℝ} (hq : 2 ≤ q)
    (s w z : ℂ) (hs : 7 / 8 ≤ s.re) (hw : 1 / 2 ≤ w.re)
    (hz : 17 / 50 ≤ z.re) (j : Fin 5) :
    ‖(q : ℂ) ^ s * (ramifiedTableValue P q s w z j - 1)‖ ≤
      9 * q ^ (1 / 2 : ℝ) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have ht : 0 ≤ q ^ (1 / 2 : ℝ) := Real.rpow_nonneg hq0.le _
  have hR := small_coordR_norm_le_half P hq s z hs hz
  have hV := outer_coordV_norm_le_quarter hq z hz
  have hLR : ‖(q : ℂ) ^ s * coordR P q s z‖ ≤ q ^ (1 / 2 : ℝ) := by
    unfold coordR
    apply weighted_phaseMonomial_norm_le hq1 _ P.alpha_sq_bound
    norm_num
    linarith
  have h1 : ‖(q : ℂ) ^ s * phaseMonomial q P.eta 1 s w 1 1‖ ≤
      q ^ (1 / 2 : ℝ) := by
    apply weighted_phaseMonomial_norm_le hq1 _ P.eta_bound
    norm_num
    linarith
  have h2 : ‖(q : ℂ) ^ s * phaseMonomial q P.c2 (3 / 2) s w 3 0‖ ≤
      q ^ (1 / 2 : ℝ) := by
    apply weighted_phaseMonomial_norm_le hq1 _ P.c2_bound
    norm_num
    linarith
  have h31 : ‖(q : ℂ) ^ s * phaseMonomial q P.c31 2 s w 3 1‖ ≤
      q ^ (1 / 2 : ℝ) := by
    apply weighted_phaseMonomial_norm_le hq1 _ P.c31_bound
    norm_num
    linarith
  have h32 : ‖(q : ℂ) ^ s * phaseMonomial q P.c32 2 s w 4 0‖ ≤
      q ^ (1 / 2 : ℝ) := by
    apply weighted_phaseMonomial_norm_le hq1 _ P.c32_bound
    norm_num
    linarith
  have h4 : ‖(q : ℂ) ^ s * phaseMonomial q P.c4 (5 / 2) s w 4 1‖ ≤
      q ^ (1 / 2 : ℝ) := by
    apply weighted_phaseMonomial_norm_le hq1 _ P.c4_bound
    norm_num
    linarith
  have h5 : ‖(q : ℂ) ^ s * phaseMonomial q (P.alpha ^ 2) 3 s w 6 0‖ ≤
      q ^ (1 / 2 : ℝ) := by
    apply weighted_phaseMonomial_norm_le hq1 _ P.alpha_sq_bound
    norm_num
    linarith
  have hD : ‖(q : ℂ) ^ s * specialTerm P q s w j‖ ≤ 2 * q ^ (1 / 2 : ℝ) := by
    fin_cases j
    · simpa [specialTerm] using h1.trans (by linarith : q ^ (1 / 2 : ℝ) ≤ 2 * q ^ (1 / 2 : ℝ))
    · simpa [specialTerm] using h2.trans (by linarith : q ^ (1 / 2 : ℝ) ≤ 2 * q ^ (1 / 2 : ℝ))
    · simp only [specialTerm, mul_sub]
      exact (norm_sub_le _ _).trans (by simpa only [two_mul] using add_le_add h31 h32)
    · simpa [specialTerm] using h4.trans (by linarith : q ^ (1 / 2 : ℝ) ≤ 2 * q ^ (1 / 2 : ℝ))
    · simpa [specialTerm] using h5.trans (by linarith : q ^ (1 / 2 : ℝ) ≤ 2 * q ^ (1 / 2 : ℝ))
  have hB : ‖(q : ℂ) ^ s * coordB P q s w z‖ ≤ 2 * q ^ (1 / 2 : ℝ) := by
    have heq : (q : ℂ) ^ s * coordB P q s w z =
        ((q : ℂ) ^ s * coordR P q s z -
          (q : ℂ) ^ s * phaseMonomial q P.eta 1 s w 1 1) * (1 - (q : ℂ)⁻¹) := by
      unfold coordB
      ring
    rw [heq, norm_mul]
    have hsub := (norm_sub_le ((q : ℂ) ^ s * coordR P q s z)
      ((q : ℂ) ^ s * phaseMonomial q P.eta 1 s w 1 1)).trans (add_le_add hLR h1)
    exact (mul_le_mul hsub (norm_one_sub_inv_le_one q hq1) (norm_nonneg _)
      (by positivity)).trans_eq (by ring)
  rw [ramifiedTableValue_eq_correction P q hq0 s w z j (one_sub_R_ne_zero _ hR)]
  exact ramifiedCorrection_weighted_norm_sub_one_le _ _ _ _ _ _ ht hR hV hB hD

/-- A purely scalar prime cutoff controls the unmarked denominator on the
small contour.  Its exponent is independent of B and the height. -/
theorem ramified_small_error (P : PhaseData) {q : ℝ} (hq : 2 ≤ q)
    (s w z : ℂ) (hs : 7 / 8 ≤ s.re) (hw : 1 / 2 ≤ w.re)
    (hz : 17 / 50 ≤ z.re) (j : Fin 5) :
    ‖ramifiedTableValue P q s w z j - 1‖ ≤ 9 * q ^ (-(3 / 8 : ℝ)) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have h := ramified_small_weighted_error P hq s w z hs hw hz j
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0] at h
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hq0 s.re)).mp
  apply h.trans
  calc
    9 * q ^ (1 / 2 : ℝ) ≤ 9 * q ^ (s.re - 3 / 8) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)) (by norm_num)
    _ = q ^ s.re * (9 * q ^ (-(3 / 8 : ℝ))) := by
      rw [mul_left_comm, ← Real.rpow_add hq0]
      congr 1
      congr 1
      ring

/-- Every ramified local compensation has at most a square-root cost on
the actual small-row line.  The only cutoff is a numerical inequality. -/
theorem ramified_small_selected_bound (P : PhaseData) {q : ℝ} (hq : 2 ≤ q)
    (s w z : ℂ) (hs : 7 / 8 ≤ s.re) (hw : 1 / 2 ≤ w.re)
    (hz : 17 / 50 ≤ z.re) (j : Fin 5)
    (hcut : 9 * q ^ (-(3 / 8 : ℝ)) ≤ 1 / 2) :
    ‖normalizedCompensation P.eta ((q : ℂ) ^ s) ((q : ℂ) ^ (-w))
      (ramifiedTableValue P q s w z j)‖ ≤ 19 * q ^ (1 / 2 : ℝ) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hW : ‖(q : ℂ) ^ (-w)‖ ≤ q ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have h := normalizedCompensation_norm_le_weighted P.eta ((q : ℂ) ^ s)
    ((q : ℂ) ^ (-w)) (ramifiedTableValue P q s w z j) (9 * q ^ (1 / 2 : ℝ))
    P.eta_bound ((ramified_small_error P hq s w z hs hw hz j).trans hcut)
    (ramified_small_weighted_error P hq s w z hs hw hz j)
  linarith

end HeckeSkeleton.Expansion.SmallRows

#print axioms HeckeSkeleton.Expansion.SmallRows.ramified_small_weighted_error
#print axioms HeckeSkeleton.Expansion.SmallRows.ramified_small_error
#print axioms HeckeSkeleton.Expansion.SmallRows.ramified_small_selected_bound
