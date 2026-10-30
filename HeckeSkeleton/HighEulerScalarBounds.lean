import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Scalar bounds for the five ramified Euler rows

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.

This module is independent of number-field arithmetic.  The coefficients below
are explicit parameters with explicit norm bounds.  Identifying them with the
actual local Gauss sums, and identifying the rational table with the original
Fourier series, are separate calibration obligations.

The dynamic line is Re(s)=b+16e, Re(w)=1-b-6e, Re(z)=17/50.
-/

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds

/-- The common shape of the unmarked ramified correction. -/
def ramifiedCorrection (B D R V : ℂ) : ℂ :=
  1 + (B + (1 - V) * D) / (1 - R)

/-- A uniform scalar estimate; no arithmetic assumptions are hidden here. -/
theorem ramifiedCorrection_norm_sub_one_le (B D R V : ℂ) (t : ℝ)
    (ht : 0 ≤ t) (hR : ‖R‖ ≤ 1 / 2) (hV : ‖V‖ ≤ 1 / 4)
    (hB : ‖B‖ ≤ 2 * t) (hD : ‖D‖ ≤ 2 * t) :
    ‖ramifiedCorrection B D R V - 1‖ ≤ 9 * t := by
  have hden : 1 / 2 ≤ ‖(1 : ℂ) - R‖ := by
    have h := norm_sub_norm_le (1 : ℂ) R
    norm_num at h
    linarith
  have hdenpos : 0 < ‖(1 : ℂ) - R‖ := by linarith
  have hv : ‖(1 : ℂ) - V‖ ≤ 5 / 4 := by
    have h := norm_sub_le (1 : ℂ) V
    norm_num at h
    linarith
  have hmul : ‖(1 : ℂ) - V‖ * ‖D‖ ≤ (5 / 4) * (2 * t) :=
    mul_le_mul hv hD (norm_nonneg _) (by norm_num)
  have hnum : ‖B + (1 - V) * D‖ ≤ (9 / 2) * t := by
    have h := norm_add_le B ((1 - V) * D)
    rw [norm_mul] at h
    linarith
  simp only [ramifiedCorrection, add_sub_cancel_left, norm_div]
  apply (div_le_iff₀ hdenpos).mpr
  nlinarith

/-- The geometric denominator is nonzero under the same half bound. -/
theorem one_sub_R_ne_zero (R : ℂ) (hR : ‖R‖ ≤ 1 / 2) : 1 - R ≠ 0 := by
  intro h
  have hRone : R = 1 := by linear_combination -h
  norm_num [hRone] at hR

theorem V_exponent_margin : (2 : ℝ) ≤ 51 / 25 := by norm_num

theorem R_exponent_ledger (b e : ℝ) (hb : 1 / 2 ≤ b) (he : 0 ≤ e) :
    (49 / 25 : ℝ) - 6 * b - 96 * e ≤ -26 / 25 - 96 * e ∧
      (-26 / 25 : ℝ) - 96 * e ≤ -10 * e ∧
      (49 / 25 : ℝ) - 6 * b - 96 * e ≤ -1 := by
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem D_exponent_ledger (b e : ℝ) (hb : 1 / 2 ≤ b) (he : 0 ≤ e) :
    -10 * e ≤ -10 * e ∧
      3 / 2 - 3 * b - 48 * e ≤ -10 * e ∧
      1 - 2 * b - 42 * e ≤ -10 * e ∧
      2 - 4 * b - 64 * e ≤ -10 * e ∧
      3 / 2 - 3 * b - 58 * e ≤ -10 * e ∧
      3 - 6 * b - 96 * e ≤ -10 * e := by
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- A complex power monomial, with its coefficient kept explicit. -/
def phaseMonomial (q : ℝ) (c : ℂ) (r : ℝ) (s w : ℂ) (m n : ℕ) : ℂ :=
  c * (q : ℂ) ^ ((r : ℂ) - (m : ℂ) * s - (n : ℂ) * w)

theorem phaseMonomial_eq_factored (q : ℝ) (hq : 0 < q)
    (c : ℂ) (r : ℝ) (s w : ℂ) (m n : ℕ) :
    phaseMonomial q c r s w m n =
      c * (q : ℂ) ^ (r : ℂ) * ((q : ℂ) ^ (-s)) ^ m *
        ((q : ℂ) ^ (-w)) ^ n := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  unfold phaseMonomial
  have hExp : (r : ℂ) - (m : ℂ) * s - (n : ℂ) * w =
      ((r : ℂ) + (m : ℂ) * (-s)) + (n : ℂ) * (-w) := by ring
  rw [hExp, Complex.cpow_add _ _ hqC, Complex.cpow_add _ _ hqC,
    Complex.cpow_nat_mul, Complex.cpow_nat_mul]
  ring

theorem phaseMonomial_norm_le (q : ℝ) (hq : 0 < q)
    (c : ℂ) (hc : ‖c‖ ≤ 1) (r : ℝ) (s w : ℂ) (m n : ℕ) :
    ‖phaseMonomial q c r s w m n‖ ≤
      q ^ (r - (m : ℝ) * s.re - (n : ℝ) * w.re) := by
  unfold phaseMonomial
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  calc
    _ ≤ 1 * q ^ (r - (m : ℝ) * s.re - (n : ℝ) * w.re) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hq.le _)
    _ = _ := one_mul _

theorem phaseMonomial_norm_le_of_exponent_le (q : ℝ) (hq : 1 ≤ q)
    (c : ℂ) (hc : ‖c‖ ≤ 1) (r : ℝ) (s w : ℂ) (m n : ℕ)
    (t : ℝ) (ht : r - (m : ℝ) * s.re - (n : ℝ) * w.re ≤ t) :
    ‖phaseMonomial q c r s w m n‖ ≤ q ^ t := by
  exact (phaseMonomial_norm_le q (by linarith) c hc r s w m n).trans
    (Real.rpow_le_rpow_of_exponent_le hq ht)

/-- Norm-normalized coefficients; these bounds must be established arithmetically. -/
structure PhaseData where
  eta : ℂ
  alpha : ℂ
  c2 : ℂ
  c31 : ℂ
  c32 : ℂ
  c4 : ℂ
  eta_bound : ‖eta‖ ≤ 1
  alpha_bound : ‖alpha‖ ≤ 1
  c2_bound : ‖c2‖ ≤ 1
  c31_bound : ‖c31‖ ≤ 1
  c32_bound : ‖c32‖ ≤ 1
  c4_bound : ‖c4‖ ≤ 1

theorem PhaseData.alpha_sq_bound (P : PhaseData) : ‖P.alpha ^ 2‖ ≤ 1 := by
  rw [norm_pow]
  have hn := norm_nonneg P.alpha
  have hb := P.alpha_bound
  nlinarith

/-- `j.val+1` is the ramified valuation class, from one through five. -/
def specialTerm (P : PhaseData) (q : ℝ) (s w : ℂ) (j : Fin 5) : ℂ :=
  match j.val with
  | 0 => phaseMonomial q P.eta 1 s w 1 1
  | 1 => phaseMonomial q P.c2 (3 / 2) s w 3 0
  | 2 => phaseMonomial q P.c31 2 s w 3 1 - phaseMonomial q P.c32 2 s w 4 0
  | 3 => -phaseMonomial q P.c4 (5 / 2) s w 4 1
  | _ => -phaseMonomial q (P.alpha ^ 2) 3 s w 6 0

/-- All five terms obey the required decay, uniformly in their phases. -/
theorem specialTerm_norm_le (P : PhaseData) (q b e : ℝ)
    (hq : 1 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s w : ℂ) (hs : s.re = b + 16 * e) (hw : w.re = 1 - b - 6 * e)
    (j : Fin 5) : ‖specialTerm P q s w j‖ ≤ 2 * q ^ (-10 * e) := by
  have ht : 0 ≤ q ^ (-10 * e) := Real.rpow_nonneg (by linarith) _
  have h1 : ‖phaseMonomial q P.eta 1 s w 1 1‖ ≤ q ^ (-10 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.eta_bound
    norm_num
    rw [hs, hw]
    linarith
  have h2 : ‖phaseMonomial q P.c2 (3 / 2) s w 3 0‖ ≤ q ^ (-10 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.c2_bound
    norm_num
    rw [hs]
    linarith
  have h31 : ‖phaseMonomial q P.c31 2 s w 3 1‖ ≤ q ^ (-10 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.c31_bound
    norm_num
    rw [hs, hw]
    linarith
  have h32 : ‖phaseMonomial q P.c32 2 s w 4 0‖ ≤ q ^ (-10 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.c32_bound
    norm_num
    rw [hs]
    linarith
  have h4 : ‖phaseMonomial q P.c4 (5 / 2) s w 4 1‖ ≤ q ^ (-10 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.c4_bound
    norm_num
    rw [hs, hw]
    linarith
  have h5 : ‖phaseMonomial q (P.alpha ^ 2) 3 s w 6 0‖ ≤ q ^ (-10 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.alpha_sq_bound
    norm_num
    rw [hs]
    linarith
  fin_cases j
  · simpa [specialTerm] using h1.trans (by linarith : q ^ (-10 * e) ≤ 2 * q ^ (-10 * e))
  · simpa [specialTerm] using h2.trans (by linarith : q ^ (-10 * e) ≤ 2 * q ^ (-10 * e))
  · exact (norm_sub_le _ _).trans (by simpa [two_mul] using add_le_add h31 h32)
  · simpa [specialTerm] using h4.trans (by linarith : q ^ (-10 * e) ≤ 2 * q ^ (-10 * e))
  · simpa [specialTerm] using h5.trans (by linarith : q ^ (-10 * e) ≤ 2 * q ^ (-10 * e))

def coordV (q : ℝ) (z : ℂ) : ℂ := (q : ℂ) ^ (-6 * z)

def coordR (P : PhaseData) (q : ℝ) (s z : ℂ) : ℂ :=
  phaseMonomial q (P.alpha ^ 2) 4 s z 6 6

def coordB (P : PhaseData) (q : ℝ) (s w z : ℂ) : ℂ :=
  coordR P q s z * (1 - (q : ℂ)⁻¹) -
    phaseMonomial q P.eta 1 s w 1 1 * (1 - (q : ℂ)⁻¹)

theorem coordR_eq_original (P : PhaseData) (q : ℝ) (hq : 0 < q) (s z : ℂ) :
    coordR P q s z =
      P.alpha ^ 2 * (q : ℂ) ^ 4 * ((q : ℂ) ^ (-s)) ^ 6 * coordV q z := by
  have hV : ((q : ℂ) ^ (-z)) ^ 6 = coordV q z := by
    unfold coordV
    rw [← Complex.cpow_nat_mul]
    congr 1
    push_cast
    ring
  unfold coordR
  rw [phaseMonomial_eq_factored q hq]
  norm_num [hV]

/-- This recovers the multiplicatively written common term in the finite table. -/
theorem coordB_eq_original (P : PhaseData) (q : ℝ) (hq : 0 < q) (s w z : ℂ) :
    coordB P q s w z =
      coordR P q s z * (1 - (q : ℂ)⁻¹) -
        P.eta * ((q : ℂ) - 1) * (q : ℂ) ^ (-s) * (q : ℂ) ^ (-w) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  unfold coordB
  rw [phaseMonomial_eq_factored q hq]
  norm_num
  field_simp [hqC]

theorem norm_one_sub_inv_le_one (q : ℝ) (hq : 1 ≤ q) :
    ‖(1 : ℂ) - (q : ℂ)⁻¹‖ ≤ 1 := by
  have hqpos : 0 < q := by linarith
  have hqi : 0 ≤ q⁻¹ := inv_nonneg.mpr hqpos.le
  have hqile : q⁻¹ ≤ 1 := (inv_le_one₀ hqpos).mpr hq
  rw [show (1 : ℂ) - (q : ℂ)⁻¹ = ((1 - q⁻¹ : ℝ) : ℂ) by simp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

theorem coordV_norm_le_quarter (q : ℝ) (hq : 2 ≤ q) (z : ℂ)
    (hz : z.re = 17 / 50) : ‖coordV q z‖ ≤ 1 / 4 := by
  have hqpos : 0 < q := by linarith
  have hqone : 1 ≤ q := by linarith
  unfold coordV
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
  have hre : (-6 * z).re = (-51 / 25 : ℝ) := by
    norm_num [Complex.mul_re, hz]
  rw [hre]
  calc
    q ^ (-51 / 25 : ℝ) ≤ q ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hqone (by norm_num)
    _ ≤ (2 : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
    _ = 1 / 4 := by norm_num

theorem coordR_norm_le_decay (P : PhaseData) (q b e : ℝ)
    (hq : 1 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s z : ℂ) (hs : s.re = b + 16 * e) (hz : z.re = 17 / 50) :
    ‖coordR P q s z‖ ≤ q ^ (-10 * e) := by
  unfold coordR
  apply phaseMonomial_norm_le_of_exponent_le q hq _ P.alpha_sq_bound
  norm_num
  rw [hs, hz]
  linarith

theorem coordR_norm_le_half (P : PhaseData) (q b e : ℝ)
    (hq : 2 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s z : ℂ) (hs : s.re = b + 16 * e) (hz : z.re = 17 / 50) :
    ‖coordR P q s z‖ ≤ 1 / 2 := by
  have hR : ‖coordR P q s z‖ ≤ q ^ (-1 : ℝ) := by
    unfold coordR
    apply phaseMonomial_norm_le_of_exponent_le q (by linarith) _ P.alpha_sq_bound
    norm_num
    rw [hs, hz]
    linarith
  calc
    ‖coordR P q s z‖ ≤ q ^ (-1 : ℝ) := hR
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
    _ = 1 / 2 := by norm_num

theorem coordB_norm_le (P : PhaseData) (q b e : ℝ)
    (hq : 1 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s w z : ℂ) (hs : s.re = b + 16 * e) (hw : w.re = 1 - b - 6 * e)
    (hz : z.re = 17 / 50) : ‖coordB P q s w z‖ ≤ 2 * q ^ (-10 * e) := by
  have ht : 0 ≤ q ^ (-10 * e) := Real.rpow_nonneg (by linarith) _
  have hR := coordR_norm_le_decay P q b e hq hb he s z hs hz
  have hD : ‖phaseMonomial q P.eta 1 s w 1 1‖ ≤ q ^ (-10 * e) := by
    apply phaseMonomial_norm_le_of_exponent_le q hq _ P.eta_bound
    norm_num
    rw [hs, hw]
    linarith
  have hsub : ‖coordR P q s z - phaseMonomial q P.eta 1 s w 1 1‖ ≤
      2 * q ^ (-10 * e) := (norm_sub_le _ _).trans (by linarith)
  unfold coordB
  rw [← sub_mul, norm_mul]
  calc
    _ ≤ (2 * q ^ (-10 * e)) * 1 :=
      mul_le_mul hsub (norm_one_sub_inv_le_one q hq) (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

/-- The full pointwise dynamic estimate for all five normalized ramified rows.

The hypotheses concern only q, the real parts on the dynamic line, and the
explicit phase bounds packaged by `PhaseData`.  No additional local norm
hypothesis is assumed.  This is the scalar theorem to use after arithmetic
calibration identifies the finite Euler table with these coordinates.
-/
theorem ramified_dynamic_bound (P : PhaseData) (q b e : ℝ)
    (hq : 2 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s w z : ℂ) (hs : s.re = b + 16 * e) (hw : w.re = 1 - b - 6 * e)
    (hz : z.re = 17 / 50) (j : Fin 5) :
    ‖ramifiedCorrection (coordB P q s w z) (specialTerm P q s w j)
      (coordR P q s z) (coordV q z) - 1‖ ≤ 9 * q ^ (-10 * e) := by
  have hqone : 1 ≤ q := by linarith
  exact ramifiedCorrection_norm_sub_one_le _ _ _ _ _
    (Real.rpow_nonneg (by linarith) _)
    (coordR_norm_le_half P q b e hq hb he s z hs hz)
    (coordV_norm_le_quarter q hq z hz)
    (coordB_norm_le P q b e hqone hb he s w z hs hw hz)
    (specialTerm_norm_le P q b e hqone hb he s w hs hw j)

/-- The quotient form of the five-row table, with normalized phase parameters. -/
def ramifiedTableValue (P : PhaseData) (q : ℝ) (s w z : ℂ) (j : Fin 5) : ℂ :=
  (1 - coordR P q s z / (q : ℂ) -
      P.eta * ((q : ℂ) - 1) * (q : ℂ) ^ (-s) * (q : ℂ) ^ (-w) +
      (1 - coordV q z) * specialTerm P q s w j) / (1 - coordR P q s z)

theorem ramifiedTableValue_eq_correction (P : PhaseData) (q : ℝ) (hq : 0 < q)
    (s w z : ℂ) (j : Fin 5) (hR : 1 - coordR P q s z ≠ 0) :
    ramifiedTableValue P q s w z j =
      ramifiedCorrection (coordB P q s w z) (specialTerm P q s w j)
        (coordR P q s z) (coordV q z) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  rw [coordB_eq_original P q hq]
  unfold ramifiedTableValue ramifiedCorrection
  field_simp [hqC, hR]
  ring

/-- The same uniform bound stated directly for the quotient table value. -/
theorem ramified_table_dynamic_bound (P : PhaseData) (q b e : ℝ)
    (hq : 2 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s w z : ℂ) (hs : s.re = b + 16 * e) (hw : w.re = 1 - b - 6 * e)
    (hz : z.re = 17 / 50) (j : Fin 5) :
    ‖ramifiedTableValue P q s w z j - 1‖ ≤ 9 * q ^ (-10 * e) := by
  rw [ramifiedTableValue_eq_correction P q (by linarith) s w z j
    (one_sub_R_ne_zero _ (coordR_norm_le_half P q b e hq hb he s z hs hz))]
  exact ramified_dynamic_bound P q b e hq hb he s w z hs hw hz j

#print axioms ramifiedCorrection_norm_sub_one_le
#print axioms one_sub_R_ne_zero
#print axioms V_exponent_margin
#print axioms R_exponent_ledger
#print axioms D_exponent_ledger
#print axioms phaseMonomial_eq_factored
#print axioms phaseMonomial_norm_le
#print axioms phaseMonomial_norm_le_of_exponent_le
#print axioms PhaseData.alpha_sq_bound
#print axioms specialTerm_norm_le
#print axioms coordR_eq_original
#print axioms coordB_eq_original
#print axioms norm_one_sub_inv_le_one
#print axioms coordV_norm_le_quarter
#print axioms coordR_norm_le_decay
#print axioms coordR_norm_le_half
#print axioms coordB_norm_le
#print axioms ramified_dynamic_bound
#print axioms ramifiedTableValue_eq_correction
#print axioms ramified_table_dynamic_bound

end HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds

end
