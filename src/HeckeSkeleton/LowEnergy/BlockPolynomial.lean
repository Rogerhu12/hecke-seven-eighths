import HeckeSkeleton.LowEnergy.ExponentTail
import HeckeSkeleton.LowEnergy.CommonMellinTail
import Mathlib.Tactic.GCongr

/-!
# The literal hybrid polynomial gives the reflected paper exponent

This algebraic bridge keeps the inverse squarefree/cube-column mass and the
square of the small/large kernel scalar. The O/2 weight belongs to the later
powerful-ideal sum: solving for one fixed powerful ideal retains N(f)^(-1/2).
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.BlockPolynomial
open HeckeSkeleton.LowEnergy.Numerics
open HeckeSkeleton.LowEnergy.CommonMellinTail

theorem row_polynomial_le {Z H v b : ℝ} (hZ : 1 ≤ Z) :
    Z ^ H + Z ^ v * Z ^ b ≤ 2 * Z ^ max H (v + b) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  rw [← Real.rpow_add hZ0]
  have hH := Real.rpow_le_rpow_of_exponent_le hZ (le_max_left H (v + b))
  have hNB := Real.rpow_le_rpow_of_exponent_le hZ (le_max_right H (v + b))
  linarith

theorem cubic_polynomial_le {Z v z : ℝ} (hZ : 1 ≤ Z) :
    Z ^ v + Z ^ z + (Z ^ v * Z ^ z) ^ (2 / 3 : ℝ) ≤
      3 * Z ^ (v + z - saving v z) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have huV : saving v z ≤ v := min_le_left _ _
  have huZ : saving v z ≤ z := (min_le_right _ _).trans (min_le_left _ _)
  have huC : saving v z ≤ (v + z) / 3 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hN := Real.rpow_le_rpow_of_exponent_le hZ
    (show v ≤ v + z - saving v z by linarith)
  have hL := Real.rpow_le_rpow_of_exponent_le hZ
    (show z ≤ v + z - saving v z by linarith)
  have hC := Real.rpow_le_rpow_of_exponent_le hZ
    (show (v + z) * (2 / 3 : ℝ) ≤ v + z - saving v z by linarith)
  rw [← Real.rpow_add hZ0, ← Real.rpow_mul hZ0.le]
  linarith

def weightedReflectedPolynomial (Z O H S B0 z v b T : ℝ) : ℝ :=
  Z ^ (O / 2 - S - B0 - v - 2 * b) *
    (Z ^ H + Z ^ v * Z ^ b) * Z ^ b *
    (Z ^ v + Z ^ z + (Z ^ v * Z ^ z) ^ (2 / 3 : ℝ)) *
    scalar (Z ^ (v + 3 * b - T)) ^ 2

/-- Exact polynomial specialization after coefficient normalization.
No retained dual range is assumed. -/
theorem weighted_polynomial_le {Z O H S B0 z v b T : ℝ} (hZ : 1 ≤ Z) :
    weightedReflectedPolynomial Z O H S B0 z v b T ≤
      6 * Z ^ fullPaperExponent O H S B0 z v b T := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  unfold weightedReflectedPolynomial
  calc
    _ ≤ Z ^ (O / 2 - S - B0 - v - 2 * b) *
        (2 * Z ^ max H (v + b)) * Z ^ b *
        (3 * Z ^ (v + z - saving v z)) *
        scalar (Z ^ (v + 3 * b - T)) ^ 2 := by
      gcongr
      · exact row_polynomial_le hZ
      · exact cubic_polynomial_le hZ
    _ = 6 * Z ^ fullPaperExponent O H S B0 z v b T := by
      rw [scalar_sq_exponent Z T v b hZ]
      calc
        _ = 6 * (Z ^ (O / 2 - S - B0 - v - 2 * b) *
            Z ^ max H (v + b) * Z ^ b * Z ^ (v + z - saving v z) *
            Z ^ (-max (T - v - 3 * b) 0 / 2 - 4 * max (v + 3 * b - T) 0)) := by ring
        _ = _ := by
          repeat rw [← Real.rpow_add hZ0]
          congr 2
          unfold fullPaperExponent paperExponent
          ring

/-- The four-scale loss is retained even on arbitrarily large dual dyads. -/
theorem weighted_polynomial_with_sieve_loss
    {Z O H S B0 z v b T delta : ℝ} (hZ : 1 ≤ Z) :
    (Z ^ H * Z ^ v * Z ^ b * Z ^ z) ^ delta *
        weightedReflectedPolynomial Z O H S B0 z v b T ≤
      6 * Z ^ (fullPaperExponent O H S B0 z v b T + delta * (H + v + b + z)) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have h := mul_le_mul_of_nonneg_left
    (weighted_polynomial_le (O := O) (H := H) (S := S) (B0 := B0)
      (z := z) (v := v) (b := b) (T := T) hZ)
    (show 0 ≤ (Z ^ H * Z ^ v * Z ^ b * Z ^ z) ^ delta by positivity)
  apply h.trans_eq
  repeat rw [← Real.rpow_add hZ0]
  rw [← Real.rpow_mul hZ0.le]
  calc
    _ = 6 * (Z ^ ((H + v + b + z) * delta) *
        Z ^ fullPaperExponent O H S B0 z v b T) := by ring
    _ = _ := by
      rw [← Real.rpow_add hZ0]
      congr 2
      ring

/-- The complete low-scale numeric conclusion, including the raw sieve loss
on unbounded dual dyads and the actual two-sided kernel scalar. -/
theorem low_weighted_polynomial
    {Z d O H A N S B0 z v b ell theta T eta delta : ℝ}
    (hZ : 1 ≤ Z) (hd : 0 ≤ d) (hd' : d ≤ (1 / 6 : ℝ))
    (hO : 0 ≤ O) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hS : 0 ≤ S) (hB : 0 ≤ B0) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta) (hdelta' : delta ≤ 1)
    (hwidth : O + H ≤ (5 / 6 : ℝ) - 2 * d + eta)
    (hconductor : 2 * A ≤ O + eta) (hNA : N ≤ A)
    (hslot : z ≤ ell + eta) (hell : ell ≤ (1 / 6 : ℝ) - d + eta)
    (htheta : |theta| ≤ eta)
    (hT : T = 2 * H + 2 * A + 2 * z - 1 - ell - theta - N - 3 * B0) :
    (Z ^ H * Z ^ v * Z ^ b * Z ^ z) ^ delta *
        weightedReflectedPolynomial Z O H S B0 z v b T ≤
      6 * Z ^ ((5 / 6 : ℝ) - 2 * d + 2 * delta + 21 * eta -
        2 * max (v + 3 * b - T) 0) := by
  have he := low_full_ramified_exponent_with_sieve_loss (e := 0)
    hd hd' hO hA hN hS hB hv hb heta (by linarith) hdelta hdelta'
    hwidth hconductor hNA hslot hell htheta hT
  have he' : fullPaperExponent O H S B0 z v b T + delta * (H + v + b + z) ≤
      (5 / 6 : ℝ) - 2 * d + 2 * delta + 21 * eta -
        2 * max (v + 3 * b - T) 0 := by
    simpa only [fullRamifiedExponent, fullPaperExponent,
      ramifiedExponent_zero, add_zero] using he
  exact (weighted_polynomial_with_sieve_loss hZ).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he') (by norm_num))

/-- For one fixed powerful ideal, the inverse half norm remains available
for the genuine Rankin sum. It must not be replaced by a second row count. -/
theorem remove_powerful_weight {Z O H S B0 z v b T : ℝ} (hZ : 0 < Z) :
    weightedReflectedPolynomial Z 0 H S B0 z v b T =
      Z ^ (-O / 2) * weightedReflectedPolynomial Z O H S B0 z v b T := by
  unfold weightedReflectedPolynomial
  have he : Z ^ (-O / 2) * Z ^ (O / 2 - S - B0 - v - 2 * b) =
      Z ^ (0 / 2 - S - B0 - v - 2 * b) := by
    rw [← Real.rpow_add hZ]
    congr 1
    ring
  calc
    _ = (Z ^ (-O / 2) * Z ^ (O / 2 - S - B0 - v - 2 * b)) *
        (Z ^ H + Z ^ v * Z ^ b) * Z ^ b *
        (Z ^ v + Z ^ z + (Z ^ v * Z ^ z) ^ (2 / 3 : ℝ)) *
        scalar (Z ^ (v + 3 * b - T)) ^ 2 := by rw [he]
    _ = _ := by ring

#print axioms weighted_polynomial_le
#print axioms weighted_polynomial_with_sieve_loss
#print axioms low_weighted_polynomial
#print axioms remove_powerful_weight

end HeckeSkeleton.LowEnergy.BlockPolynomial
