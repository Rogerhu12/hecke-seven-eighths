import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-! Coarse positive-base bounds for the literal subset compensation powers.
No high-bin estimate or contour integral is an input. -/

noncomputable section
namespace HighBinBoundary.TupleScalar

def compensationScalar (Z A B : ℝ) (s w z : ℂ) : ℂ :=
  (A : ℂ) ^ (-(3 / 2 : ℂ)) *
    ((Z ^ (17 / 48 : ℝ) / A : ℝ) : ℂ) ^ (1 / 2 - z) *
    ((Z * B : ℝ) : ℂ) ^ (s + z - 1) *
    ((Z ^ (23 / 48 : ℝ) / A : ℝ) : ℂ) ^ (w - 1)

/-- A deliberately coarse bound valid throughout the swept strip and at
all imaginary heights. A and B are the actual selected/marked ideal norms. -/
theorem compensationScalar_norm_bound (Z A B R : ℝ) (s w z : ℂ)
    (hZ : 1 ≤ Z) (hA : 1 ≤ A) (hB : 1 ≤ B) (hAR : A ≤ R) (hBR : B ≤ R)
    (hs : s.re ≤ 2) (hw0 : -1 ≤ w.re) (hw1 : w.re ≤ 1) (hz : z.re = 17 / 50) :
    ‖compensationScalar Z A B s w z‖ ≤ Z ^ 3 * R ^ 4 := by
  have hZ0 : 0 < Z := by linarith
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hR0 : 0 < R := by linarith
  have h0 : ‖(A : ℂ) ^ (-(3 / 2 : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA0]
    norm_num
    exact Real.rpow_le_one_of_one_le_of_nonpos hA (by norm_num)
  have hX : ‖((Z ^ (17 / 48 : ℝ) / A : ℝ) : ℂ) ^ (1 / 2 - z)‖ ≤ Z := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos (Real.rpow_pos_of_pos hZ0 _) hA0)]
    have hr : (1 / 2 - z).re = (4 / 25 : ℝ) := by norm_num [hz]
    rw [hr]
    calc
      _ ≤ (Z ^ (17 / 48 : ℝ)) ^ (4 / 25 : ℝ) :=
        Real.rpow_le_rpow (by positivity)
          (div_le_self (Real.rpow_nonneg hZ0.le _) hA) (by norm_num)
      _ = Z ^ ((17 / 48 : ℝ) * (4 / 25 : ℝ)) := (Real.rpow_mul hZ0.le _ _).symm
      _ ≤ Z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
      _ = Z := Real.rpow_one _
  have hZB : ‖((Z * B : ℝ) : ℂ) ^ (s + z - 1)‖ ≤ Z ^ 2 * B ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hZ0 hB0)]
    have hbase : 1 ≤ Z * B := one_le_mul hZ hB
    calc
      _ ≤ (Z * B) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase (by simp [hz]; linarith)
      _ = Z ^ 2 * B ^ 2 := by rw [Real.rpow_two, mul_pow]
  have hY : ‖((Z ^ (23 / 48 : ℝ) / A : ℝ) : ℂ) ^ (w - 1)‖ ≤ A ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos (Real.rpow_pos_of_pos hZ0 _) hA0)]
    have hr : (w - 1).re = w.re - 1 := by simp
    rw [hr, Real.div_rpow (Real.rpow_nonneg hZ0.le _) hA0.le, div_eq_mul_inv,
      ← Real.rpow_neg hA0.le]
    have hleft : (Z ^ (23 / 48 : ℝ)) ^ (w.re - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_rpow hZ (by norm_num)) (by linarith)
    have hright : A ^ (-(w.re - 1)) ≤ A ^ 2 := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le hA (by linarith)
    simpa only [one_mul] using mul_le_mul hleft hright
      (Real.rpow_nonneg hA0.le _) (by norm_num : (0 : ℝ) ≤ 1)
  unfold compensationScalar
  simp only [norm_mul]
  calc
    _ ≤ 1 * Z * (Z ^ 2 * B ^ 2) * A ^ 2 := by
      exact mul_le_mul
        (mul_le_mul (mul_le_mul h0 hX (norm_nonneg _) (by norm_num))
          hZB (norm_nonneg _) (by positivity)) hY (norm_nonneg _) (by positivity)
    _ = Z ^ 3 * A ^ 2 * B ^ 2 := by ring
    _ ≤ Z ^ 3 * R ^ 2 * R ^ 2 := by gcongr
    _ = Z ^ 3 * R ^ 4 := by ring

/-- The phases and the actual row continuation can be inserted without
altering the geometric degree. -/
theorem compensatedTerm_norm_bound (Z A B R M : ℝ) (s w z c L : ℂ)
    (hZ : 1 ≤ Z) (hA : 1 ≤ A) (hB : 1 ≤ B) (hAR : A ≤ R) (hBR : B ≤ R)
    (hs : s.re ≤ 2) (hw0 : -1 ≤ w.re) (hw1 : w.re ≤ 1) (hz : z.re = 17 / 50)
    (hc : ‖c‖ ≤ 1) (hL : ‖L‖ ≤ M) :
    ‖c * compensationScalar Z A B s w z * L‖ ≤ Z ^ 3 * R ^ 4 * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hL
  have hZ0 : 0 ≤ Z := by linarith
  have hscalar := compensationScalar_norm_bound Z A B R s w z hZ hA hB hAR hBR hs hw0 hw1 hz
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (1 * (Z ^ 3 * R ^ 4)) * M :=
      mul_le_mul (mul_le_mul hc hscalar (norm_nonneg _) (by norm_num)) hL
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

#print axioms compensationScalar_norm_bound
#print axioms compensatedTerm_norm_bound

end HighBinBoundary.TupleScalar
