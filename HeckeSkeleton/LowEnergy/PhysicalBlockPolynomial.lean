import HeckeSkeleton.LowEnergy.BlockPolynomial
import HeckeSkeleton.LowEnergy.LogGeometry

/-!
# Actual physical scales in the low block polynomial

The variables in this file are positive real ideal norms.  The kernel scale
is the physical scale after cancellation of one active marked norm.  The
dyadic upper endpoints are twice the lower endpoints, so their effect is
one uniform constant; the unbounded dual small-power loss is retained.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.PhysicalBlockPolynomial

open HeckeSkeleton.LowEnergy.LogGeometry
open HeckeSkeleton.LowEnergy.BlockPolynomial
open HeckeSkeleton.LowEnergy.CommonMellinTail

def sievePolynomial (K N B L delta : ℝ) : ℝ :=
  (K * N * B * L) ^ delta * (K + N * B) * B *
    (N + L + (N * L) ^ (2 / 3 : ℝ))

theorem sievePolynomial_nonneg {K N B L delta : ℝ}
    (hK : 0 ≤ K) (hN : 0 ≤ N) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    0 ≤ sievePolynomial K N B L delta := by
  unfold sievePolynomial
  positivity

/-- Replacing all four lower endpoints by their dyadic upper endpoints
costs at most 512, uniformly for every sieve exponent at most one. -/
theorem doubled_sievePolynomial_le {K N B L delta : ℝ}
    (hK : 0 ≤ K) (hN : 0 ≤ N) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hdelta : delta ≤ 1) :
    sievePolynomial (2 * K) (2 * N) (2 * B) (2 * L) delta ≤
      512 * sievePolynomial K N B L delta := by
  have h16 : (16 : ℝ) ^ delta ≤ 16 := by
    calc
      _ ≤ (16 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hdelta
      _ = _ := by norm_num
  have hprod : ((2 * K) * (2 * N) * (2 * B) * (2 * L)) ^ delta ≤
      16 * (K * N * B * L) ^ delta := by
    rw [show (2 * K) * (2 * N) * (2 * B) * (2 * L) =
      16 * (K * N * B * L) by ring, Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_right h16 (by positivity)
  have hrow : 2 * K + (2 * N) * (2 * B) ≤ 4 * (K + N * B) := by
    nlinarith
  have h4 : (4 : ℝ) ^ (2 / 3 : ℝ) ≤ 4 := by
    calc
      _ ≤ (4 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have hcross : ((2 * N) * (2 * L)) ^ (2 / 3 : ℝ) ≤
      4 * (N * L) ^ (2 / 3 : ℝ) := by
    rw [show (2 * N) * (2 * L) = 4 * (N * L) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  have hcubic : 2 * N + 2 * L + ((2 * N) * (2 * L)) ^ (2 / 3 : ℝ) ≤
      4 * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by linarith
  unfold sievePolynomial
  calc
    _ ≤ (16 * (K * N * B * L) ^ delta) * (4 * (K + N * B)) *
        (2 * B) * (4 * (N + L + (N * L) ^ (2 / 3 : ℝ))) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hprod hrow (by positivity) (by positivity)) (by positivity))
        hcubic (by positivity) (by positivity)
    _ = _ := by ring

def physicalScale (Z shift inactive active linear cube K L N B : ℝ) : ℝ :=
  (Z * Real.exp shift * inactive * (linear * cube ^ 3) / active ^ 2) *
    N * B ^ 3 / (K ^ 2 * L)

def threshold (Z shift inactive active linear cube K L : ℝ) : ℝ :=
  2 * scale Z K + 2 * scale Z active + 2 * scale Z L - 1 -
    scale Z (inactive * L) - shift / Real.log Z -
    scale Z linear - 3 * scale Z cube

theorem scale_self {Z : ℝ} (hZ : 1 < Z) : scale Z Z = 1 := by
  unfold scale
  exact div_self (Real.log_pos hZ).ne'

theorem scale_exp (Z shift : ℝ) : scale Z (Real.exp shift) = shift / Real.log Z := by
  simp [scale]

/-- Exact physical kernel argument. The active marked norm occurs once
in the denominator, while the inactive marked norm remains in the scale. -/
theorem physicalScale_eq_rpow
    {Z shift inactive active linear cube K L N B : ℝ}
    (hZ : 1 < Z) (hi : 0 < inactive) (ha : 0 < active)
    (hn : 0 < linear) (hb : 0 < cube) (hK : 0 < K) (hL : 0 < L)
    (hN : 0 < N) (hB : 0 < B) :
    physicalScale Z shift inactive active linear cube K L N B =
      Z ^ (scale Z N + 3 * scale Z B -
        threshold Z shift inactive active linear cube K L) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hp : 0 < physicalScale Z shift inactive active linear cube K L N B := by
    unfold physicalScale
    positivity
  have hs : scale Z (physicalScale Z shift inactive active linear cube K L N B) =
      scale Z N + 3 * scale Z B -
        threshold Z shift inactive active linear cube K L := by
    unfold physicalScale threshold
    rw [scale_div Z (by positivity) (by positivity),
      scale_mul Z (by positivity) (by positivity),
      scale_mul Z (by positivity) hN,
      scale_div Z (by positivity) (by positivity),
      scale_mul Z (by positivity) (by positivity),
      scale_mul Z (by positivity) hi,
      scale_mul Z hZ0 (Real.exp_pos shift),
      scale_mul Z hn (by positivity),
      scale_mul Z (by positivity) hL,
      scale_mul Z hi hL,
      scale_pow, scale_pow, scale_pow, scale_pow, scale_self hZ, scale_exp]
    ring
  rw [← hs, rpow_scale hZ hp]

/-- The squared frozen coefficient and both column normalizations are
exactly the negative norm powers used in the numerical exponent lemma. -/
theorem charged_weight_le
    {Z small cube N B Cf : ℝ} (hZ : 1 < Z)
    (hs : 0 < small) (hc : 0 < cube) (hN : 0 < N) (hB : 0 < B)
    (hcharge : Cf ^ 2 ≤ (small * cube)⁻¹) :
    Cf ^ 2 / (N * B ^ 2) ≤
      Z ^ (-scale Z small - scale Z cube - scale Z N - 2 * scale Z B) := by
  have hp : 0 < (small * cube)⁻¹ / (N * B ^ 2) := by positivity
  have hscl : scale Z ((small * cube)⁻¹ / (N * B ^ 2)) =
      -scale Z small - scale Z cube - scale Z N - 2 * scale Z B := by
    rw [scale_div Z (by positivity) (by positivity), inv_eq_one_div,
      scale_div Z zero_lt_one (mul_pos hs hc), scale_mul Z hs hc,
      scale_mul Z hN (by positivity), scale_pow]
    simp only [scale, Real.log_one, zero_div]
    ring
  rw [← hscl, rpow_scale hZ hp]
  exact div_le_div_of_nonneg_right hcharge (by positivity)

/-- With the literal norm charges and physical argument, a dyadic block
is bounded by the paper polynomial. No row-energy estimate is a hypothesis. -/
theorem physical_polynomial_le
    {Z shift inactive active linear cube small K L N B Cf delta : ℝ}
    (hZ : 1 < Z) (hi : 0 < inactive) (ha : 0 < active)
    (hn : 0 < linear) (hb : 0 < cube) (hs : 0 < small)
    (hK : 0 < K) (hL : 0 < L) (hN : 0 < N) (hB : 0 < B)
    (hdelta : delta ≤ 1) (hcharge : Cf ^ 2 ≤ (small * cube)⁻¹) :
    (Cf ^ 2 / (N * B ^ 2)) *
        sievePolynomial (2 * K) (2 * N) (2 * B) (2 * L) delta *
        scalar (physicalScale Z shift inactive active linear cube K L N B) ^ 2 ≤
      512 * (Z ^ scale Z K * Z ^ scale Z N * Z ^ scale Z B * Z ^ scale Z L) ^ delta *
        weightedReflectedPolynomial Z 0 (scale Z K) (scale Z small) (scale Z cube)
          (scale Z L) (scale Z N) (scale Z B)
          (threshold Z shift inactive active linear cube K L) := by
  have hw := charged_weight_le hZ hs hb hN hB hcharge
  have hp := doubled_sievePolynomial_le hK.le hN.le hB.le hL.le hdelta
  have hp0 := sievePolynomial_nonneg (delta := delta) (by linarith : 0 ≤ 2 * K)
    (by linarith : 0 ≤ 2 * N) (by linarith : 0 ≤ 2 * B) (by linarith : 0 ≤ 2 * L)
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul hw hp hp0 (by positivity))
    (sq_nonneg (scalar (physicalScale Z shift inactive active linear cube K L N B)))
  apply h.trans_eq
  rw [physicalScale_eq_rpow hZ hi ha hn hb hK hL hN hB]
  unfold weightedReflectedPolynomial sievePolynomial
  simp only [zero_div, zero_sub]
  simp only [rpow_scale hZ hK, rpow_scale hZ hN, rpow_scale hZ hB, rpow_scale hZ hL]
  ring

/-- The complete numerical block estimate from literal norm comparisons.
The only inequalities assumed here are the row cutoff, window sizes,
conductor radical bound and actual frozen coefficient charge. -/
theorem physical_low_polynomial
    {Z shift inactive active linear cube small K L N B Cf delta F q d eta Ccut Cwin : ℝ}
    (hZ : 1 < Z) (hi : 1 ≤ inactive) (ha : 1 ≤ active)
    (hn : 1 ≤ linear) (hb : 1 ≤ cube) (hs : 1 ≤ small)
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hF : 1 ≤ F) (hq : 0 < q) (hCcut : 0 < Ccut) (hCwin : 0 < Cwin)
    (hd : 0 ≤ d) (hd' : d ≤ (1 / 6 : ℝ))
    (hdelta : 0 ≤ delta) (hdelta' : delta ≤ 1) (heta : 0 ≤ eta)
    (hcharge : Cf ^ 2 ≤ (small * cube)⁻¹)
    (hconductor : active ^ 2 ≤ F) (hlinear : linear ≤ active)
    (hselected : Z ^ d ≤ q)
    (hrow : F * K ≤ Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2)
    (hwindow : inactive * L ≤ Cwin * Z ^ ((1 / 6 : ℝ) - d))
    (hcuterr : scale Z Ccut ≤ eta) (hwinerr : scale Z Cwin ≤ eta)
    (hshift : |shift / Real.log Z| ≤ eta) :
    (Cf ^ 2 / (N * B ^ 2)) *
        sievePolynomial (2 * K) (2 * N) (2 * B) (2 * L) delta *
        scalar (physicalScale Z shift inactive active linear cube K L N B) ^ 2 ≤
      3072 * F ^ (-1 / 2 : ℝ) *
        Z ^ ((5 / 6 : ℝ) - 2 * d + 2 * delta + 21 * eta -
          2 * max (scale Z N + 3 * scale Z B -
            threshold Z shift inactive active linear cube K L) 0) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hi0 : 0 < inactive := zero_lt_one.trans_le hi
  have ha0 : 0 < active := zero_lt_one.trans_le ha
  have hn0 : 0 < linear := zero_lt_one.trans_le hn
  have hb0 : 0 < cube := zero_lt_one.trans_le hb
  have hs0 : 0 < small := zero_lt_one.trans_le hs
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  have hwidth : scale Z F + scale Z K ≤ (5 / 6 : ℝ) - 2 * d + eta := by
    have h := selected_row_width hZ hF0 hK0 hq hCcut hselected hrow
    linarith
  have hcond : 2 * scale Z active ≤ scale Z F + eta := by
    have h := scale_mono hZ (sq_pos_of_pos ha0) hconductor
    rw [scale_pow] at h
    norm_num at h
    linarith
  have hNA : scale Z linear ≤ scale Z active := scale_mono hZ hn0 hlinear
  have hslot : scale Z L ≤ scale Z (inactive * L) + eta := by
    have hIL : L ≤ inactive * L := by nlinarith
    have h := scale_mono hZ hL0 hIL
    linarith
  have hell : scale Z (inactive * L) ≤ (1 / 6 : ℝ) - d + eta := by
    have h := window_width hZ (mul_pos hi0 hL0) hCwin hwindow
    linarith
  have hnum := low_weighted_polynomial
    (O := scale Z F) (H := scale Z K) (A := scale Z active)
    (N := scale Z linear) (S := scale Z small) (B0 := scale Z cube)
    (z := scale Z L) (v := scale Z N) (b := scale Z B)
    (ell := scale Z (inactive * L)) (theta := shift / Real.log Z)
    (T := threshold Z shift inactive active linear cube K L)
    hZ.le hd hd' (scale_nonneg hZ hF) (scale_nonneg hZ ha)
    (scale_nonneg hZ hn) (scale_nonneg hZ hs) (scale_nonneg hZ hb)
    (scale_nonneg hZ hN) (scale_nonneg hZ hB) heta hdelta hdelta'
    hwidth hcond hNA hslot hell hshift rfl
  have hraw := physical_polynomial_le hZ hi0 ha0 hn0 hb0 hs0 hK0 hL0 hN0 hB0
    hdelta' hcharge
  rw [remove_powerful_weight (O := scale Z F) hZ0] at hraw
  have hhalf : Z ^ (-scale Z F / 2) = F ^ (-1 / 2 : ℝ) := by
    rw [show -scale Z F / 2 = scale Z F * (-1 / 2 : ℝ) by ring,
      Real.rpow_mul hZ0.le, rpow_scale hZ hF0]
  calc
    _ ≤ 512 * (Z ^ scale Z K * Z ^ scale Z N * Z ^ scale Z B * Z ^ scale Z L) ^ delta *
        (Z ^ (-scale Z F / 2) *
          weightedReflectedPolynomial Z (scale Z F) (scale Z K) (scale Z small)
            (scale Z cube) (scale Z L) (scale Z N) (scale Z B)
            (threshold Z shift inactive active linear cube K L)) := hraw
    _ = (512 * Z ^ (-scale Z F / 2)) *
        ((Z ^ scale Z K * Z ^ scale Z N * Z ^ scale Z B * Z ^ scale Z L) ^ delta *
          weightedReflectedPolynomial Z (scale Z F) (scale Z K) (scale Z small)
            (scale Z cube) (scale Z L) (scale Z N) (scale Z B)
            (threshold Z shift inactive active linear cube K L)) := by ring
    _ ≤ (512 * Z ^ (-scale Z F / 2)) *
        (6 * Z ^ ((5 / 6 : ℝ) - 2 * d + 2 * delta + 21 * eta -
          2 * max (scale Z N + 3 * scale Z B -
            threshold Z shift inactive active linear cube K L) 0)) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = _ := by rw [hhalf]; ring

#print axioms doubled_sievePolynomial_le
#print axioms physicalScale_eq_rpow
#print axioms charged_weight_le
#print axioms physical_polynomial_le
#print axioms physical_low_polynomial

end HeckeSkeleton.LowEnergy.PhysicalBlockPolynomial
