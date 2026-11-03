import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact conversion from norm inequalities to the low length ledger

Every input below is a positive real norm comparison. In particular the
selected norm is kept literally, and its inverse square is restored in the
last theorem. No energy or reflected-block estimate is an input here.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.LogGeometry

def scale (Z x : ℝ) : ℝ := Real.log x / Real.log Z

theorem scale_nonneg {Z x : ℝ} (hZ : 1 < Z) (hx : 1 ≤ x) :
    0 ≤ scale Z x :=
  div_nonneg (Real.log_nonneg hx) (Real.log_pos hZ).le

theorem scale_mono {Z x y : ℝ} (hZ : 1 < Z) (hx : 0 < x) (hxy : x ≤ y) :
    scale Z x ≤ scale Z y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (Real.log_pos hZ).le

theorem scale_mul (Z : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    scale Z (x * y) = scale Z x + scale Z y := by
  unfold scale
  rw [Real.log_mul hx.ne' hy.ne', add_div]

theorem scale_div (Z : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    scale Z (x / y) = scale Z x - scale Z y := by
  unfold scale
  rw [Real.log_div hx.ne' hy.ne', sub_div]

theorem scale_pow (Z x : ℝ) (n : ℕ) :
    scale Z (x ^ n) = n * scale Z x := by
  unfold scale
  rw [Real.log_pow]
  ring

theorem scale_rpow {Z : ℝ} (hZ : 1 < Z) (a : ℝ) :
    scale Z (Z ^ a) = a := by
  unfold scale
  rw [Real.log_rpow (zero_lt_one.trans hZ)]
  exact mul_div_cancel_right₀ a (Real.log_pos hZ).ne'

theorem rpow_scale {Z x : ℝ} (hZ : 1 < Z) (hx : 0 < x) :
    Z ^ scale Z x = x := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
  unfold scale
  have he : Real.log Z * (Real.log x / Real.log Z) = Real.log x := by
    field_simp [(Real.log_pos hZ).ne']
  rw [he, Real.exp_log hx]

/-- The actual selected norm gives exactly the `-2*d` row deficit. -/
theorem selected_row_width
    {Z F H q B a d : ℝ} (hZ : 1 < Z)
    (hF : 0 < F) (hH : 0 < H) (hq : 0 < q) (hB : 0 < B)
    (hselected : Z ^ d ≤ q)
    (hrow : F * H ≤ B * Z ^ a / q ^ 2) :
    scale Z F + scale Z H ≤ a - 2 * d + scale Z B := by
  have hr := scale_mono hZ (mul_pos hF hH) hrow
  rw [scale_mul Z hF hH,
    scale_div Z (mul_pos hB (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) a))
      (sq_pos_of_pos hq),
    scale_mul Z hB (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) a),
    scale_rpow hZ a, scale_pow] at hr
  have hs := scale_mono hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) d) hselected
  rw [scale_rpow hZ d] at hs
  norm_num at hr
  linarith

/-- A dyadic upper endpoint may contribute a fixed multiplicative error. -/
theorem conductor_width
    {Z A F C : ℝ} (hZ : 1 < Z) (hA : 0 < A) (hF : 0 < F) (hC : 0 < C)
    (hconductor : A ^ 2 ≤ C * F) :
    2 * scale Z A ≤ scale Z F + scale Z C := by
  have h := scale_mono hZ (sq_pos_of_pos hA) hconductor
  rw [scale_pow, scale_mul Z hC hF] at h
  norm_num at h
  linarith

theorem window_width
    {Z L C ell : ℝ} (hZ : 1 < Z) (hL : 0 < L) (hC : 0 < C)
    (hwindow : L ≤ C * Z ^ ell) :
    scale Z L ≤ ell + scale Z C := by
  have h := scale_mono hZ hL hwindow
  rw [scale_mul Z hC (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) ell),
    scale_rpow hZ ell] at h
  linarith

/-- One tolerance pays for every fixed norm constant and every Gaussian
shift. Its definition is valid for all integer annuli, with no cutoff. -/
theorem annular_tolerance
    {Z delta C : ℝ} (hZ : 1 < Z) (hdelta : 0 ≤ delta) (hC : 0 ≤ C) (k : ℤ) :
    let eta := delta + (|(k : ℝ)| + C) / Real.log Z
    0 ≤ eta ∧ |(k : ℝ) / Real.log Z| ≤ eta ∧
      C / Real.log Z ≤ eta := by
  have hlog := (Real.log_pos hZ).le
  have hn : 0 ≤ (|(k : ℝ)| + C) / Real.log Z :=
    div_nonneg (add_nonneg (abs_nonneg _) hC) hlog
  have hk : |(k : ℝ) / Real.log Z| = |(k : ℝ)| / Real.log Z := by
    rw [abs_div, abs_of_nonneg hlog]
  dsimp
  rw [hk]
  constructor
  · linarith
  constructor
  · have h := div_le_div_of_nonneg_right
      (show |(k : ℝ)| ≤ |(k : ℝ)| + C by linarith) hlog
    linarith
  · have h := div_le_div_of_nonneg_right
      (show C ≤ |(k : ℝ)| + C by linarith [abs_nonneg (k : ℝ)]) hlog
    linarith

/-- Restore the target's literal selected-ideal denominator. Replacing q
by a power of Z without this upper comparison would lose the required form. -/
theorem restore_selected_norm
    {Z q D C E a d eps : ℝ} (hZ : 0 < Z) (hq : 0 < q)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hselected : q ≤ D * Z ^ d)
    (henergy : E ≤ C * Z ^ (a - 2 * d + eps)) :
    E ≤ C * D ^ 2 * Z ^ (a + eps) / q ^ 2 := by
  have hq2 : q ^ 2 ≤ (D * Z ^ d) ^ 2 :=
    pow_le_pow_left₀ hq.le hselected 2
  have hpower : Z ^ (a - 2 * d + eps) * (Z ^ d) ^ 2 = Z ^ (a + eps) := by
    rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ]
    congr 1
    ring
  apply (le_div_iff₀ (sq_pos_of_pos hq)).mpr
  calc
    E * q ^ 2 ≤ (C * Z ^ (a - 2 * d + eps)) * q ^ 2 :=
      mul_le_mul_of_nonneg_right henergy (sq_nonneg q)
    _ ≤ (C * Z ^ (a - 2 * d + eps)) * (D * Z ^ d) ^ 2 :=
      mul_le_mul_of_nonneg_left hq2 (mul_nonneg hC (Real.rpow_nonneg hZ.le _))
    _ = C * D ^ 2 * Z ^ (a + eps) := by
      rw [mul_pow]
      calc
        _ = C * D ^ 2 * (Z ^ (a - 2 * d + eps) * (Z ^ d) ^ 2) := by ring
        _ = _ := by rw [hpower]

#print axioms selected_row_width
#print axioms annular_tolerance
#print axioms restore_selected_norm

end HeckeSkeleton.LowEnergy.LogGeometry
