import HeckeSkeleton.LowEnergy.Exponent

/-!
# Dual tails with the actual positive Mellin line

The line `Re w = 2` supplies `Y^-2` at large arguments. Squaring its scalar
subtracts four times the positive excess dual width. The retained numerical
lemma applies with that excess as its tolerance and leaves a strict geometric
gain. No restriction on the size of `eta` is used, so shifted Gaussian annuli
can use `eta = delta + (|k|+C)/log Z` without a central-annulus cutoff.
-/

set_option autoImplicit false
namespace HeckeSkeleton.LowEnergy.Numerics

noncomputable def fullPaperExponent (O H S B z v b T : ℝ) : ℝ :=
  paperExponent O H S B z v b T - 4 * max (v + 3 * b - T) 0

noncomputable def fullRamifiedExponent (O H S B z v b e T : ℝ) : ℝ :=
  ramifiedExponent O H S B z v b e T - 4 * max (v + 3 * b + e - T) 0

theorem low_full_exponent
    {d O H A N S B z v b ell theta T eta : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ (1 / 6 : ℝ))
    (hO : 0 ≤ O) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hS : 0 ≤ S) (hB : 0 ≤ B) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (heta : 0 ≤ eta)
    (hwidth : O + H ≤ (5 / 6 : ℝ) - 2 * d + eta)
    (hconductor : 2 * A ≤ O + eta) (hNA : N ≤ A)
    (hslot : z ≤ ell + eta) (hell : ell ≤ (1 / 6 : ℝ) - d + eta)
    (htheta : |theta| ≤ eta)
    (hT : T = 2 * H + 2 * A + 2 * z - 1 - ell - theta - N - 3 * B) :
    fullPaperExponent O H S B z v b T ≤
      (5 / 6 : ℝ) - 2 * d + 8 * eta - 3 * max (v + 3 * b - T) 0 := by
  have h := low_exponent_with_errors hd hd' hO hA hN hS hB hv hb heta
    (le_max_right (v + 3 * b - T) 0) hwidth hconductor hNA hslot hell htheta hT
    (show v + 3 * b ≤ T + max (v + 3 * b - T) 0 by
      linarith [le_max_left (v + 3 * b - T) 0])
  unfold fullPaperExponent
  linarith

theorem low_full_ramified_exponent
    {d O H A N S B z v b e ell theta T eta : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ (1 / 6 : ℝ))
    (hO : 0 ≤ O) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hS : 0 ≤ S) (hB : 0 ≤ B) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (heta : 0 ≤ eta) (he : -eta ≤ e)
    (hwidth : O + H ≤ (5 / 6 : ℝ) - 2 * d + eta)
    (hconductor : 2 * A ≤ O + eta) (hNA : N ≤ A)
    (hslot : z ≤ ell + eta) (hell : ell ≤ (1 / 6 : ℝ) - d + eta)
    (htheta : |theta| ≤ eta)
    (hT : T = 2 * H + 2 * A + 2 * z - 1 - ell - theta - N - 3 * B) :
    fullRamifiedExponent O H S B z v b e T ≤
      (5 / 6 : ℝ) - 2 * d + 10 * eta - 3 * max (v + 3 * b + e - T) 0 := by
  have h := low_ramified_exponent_with_errors hd hd' hO hA hN hS hB hv hb heta
    (le_max_right (v + 3 * b + e - T) 0) he hwidth hconductor hNA hslot hell htheta hT
    (show v + 3 * b + e ≤ T + max (v + 3 * b + e - T) 0 by
      linarith [le_max_left (v + 3 * b + e - T) 0])
  unfold fullRamifiedExponent
  linarith

/-- The small-power factor in the raw hybrid sieve is paid before summing
the unbounded dual lengths.  Its width has at most one copy of the excess
dual width; all other terms are controlled by the physical low ledger. -/
theorem hybrid_small_power_width
    {d O H A N B z v b e ell theta T eta : ℝ}
    (hd : 0 ≤ d) (hO : 0 ≤ O) (hN : 0 ≤ N)
    (hB : 0 ≤ B) (hb : 0 ≤ b) (he : -eta ≤ e)
    (hwidth : O + H ≤ (5 / 6 : ℝ) - 2 * d + eta)
    (hconductor : 2 * A ≤ O + eta)
    (hslot : z ≤ ell + eta) (hell : ell ≤ (1 / 6 : ℝ) - d + eta)
    (htheta : |theta| ≤ eta)
    (hT : T = 2 * H + 2 * A + 2 * z - 1 - ell - theta - N - 3 * B) :
    H + v + b + z ≤ (11 / 6 : ℝ) + 11 * eta + max (v + 3 * b + e - T) 0 := by
  have hdual := low_dual_length_with_errors hwidth hconductor hslot hell
    (abs_le.mp htheta).1 hN hB hT
  have hexcess := le_max_left (v + 3 * b + e - T) 0
  linarith

/-- A sieve epsilon at most one consumes one unit of the four-power
positive-line decay. After the retained-range loss, two units remain,
which gives a full geometric factor after the energy square root. -/
theorem low_full_ramified_exponent_with_sieve_loss
    {d O H A N S B z v b e ell theta T eta delta : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ (1 / 6 : ℝ))
    (hO : 0 ≤ O) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hS : 0 ≤ S) (hB : 0 ≤ B) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (heta : 0 ≤ eta) (he : -eta ≤ e)
    (hdelta : 0 ≤ delta) (hdelta' : delta ≤ 1)
    (hwidth : O + H ≤ (5 / 6 : ℝ) - 2 * d + eta)
    (hconductor : 2 * A ≤ O + eta) (hNA : N ≤ A)
    (hslot : z ≤ ell + eta) (hell : ell ≤ (1 / 6 : ℝ) - d + eta)
    (htheta : |theta| ≤ eta)
    (hT : T = 2 * H + 2 * A + 2 * z - 1 - ell - theta - N - 3 * B) :
    fullRamifiedExponent O H S B z v b e T + delta * (H + v + b + z) ≤
      (5 / 6 : ℝ) - 2 * d + 2 * delta + 21 * eta -
        2 * max (v + 3 * b + e - T) 0 := by
  have hbase := low_full_ramified_exponent hd hd' hO hA hN hS hB hv hb
    heta he hwidth hconductor hNA hslot hell htheta hT
  have htotal := hybrid_small_power_width (v := v) hd hO hN hB hb he hwidth hconductor
    hslot hell htheta hT
  have hmul := mul_le_mul_of_nonneg_left htotal hdelta
  have hrest : 0 ≤ 11 * eta + max (v + 3 * b + e - T) 0 := by positivity
  have hsmall := mul_le_mul_of_nonneg_right hdelta' hrest
  nlinarith

theorem low_full_exponent_with_sieve_loss
    {d O H A N S B z v b ell theta T eta delta : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ (1 / 6 : ℝ))
    (hO : 0 ≤ O) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hS : 0 ≤ S) (hB : 0 ≤ B) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta) (hdelta' : delta ≤ 1)
    (hwidth : O + H ≤ (5 / 6 : ℝ) - 2 * d + eta)
    (hconductor : 2 * A ≤ O + eta) (hNA : N ≤ A)
    (hslot : z ≤ ell + eta) (hell : ell ≤ (1 / 6 : ℝ) - d + eta)
    (htheta : |theta| ≤ eta)
    (hT : T = 2 * H + 2 * A + 2 * z - 1 - ell - theta - N - 3 * B) :
    fullPaperExponent O H S B z v b T + delta * (H + v + b + z) ≤
      (5 / 6 : ℝ) - 2 * d + 2 * delta + 21 * eta -
        2 * max (v + 3 * b - T) 0 := by
  have h := low_full_ramified_exponent_with_sieve_loss (e := 0)
    hd hd' hO hA hN hS hB hv hb heta (by linarith) hdelta hdelta'
    hwidth hconductor hNA hslot hell htheta hT
  simpa only [fullRamifiedExponent, ramifiedExponent_zero, add_zero,
    fullPaperExponent] using h

#print axioms low_full_exponent
#print axioms low_full_ramified_exponent
#print axioms hybrid_small_power_width
#print axioms low_full_ramified_exponent_with_sieve_loss
#print axioms low_full_exponent_with_sieve_loss

end HeckeSkeleton.LowEnergy.Numerics
