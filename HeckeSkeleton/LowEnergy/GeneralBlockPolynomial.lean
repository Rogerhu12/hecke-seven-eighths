import HeckeSkeleton.LowEnergy.PhysicalBlockPolynomial

/-!
# The general marked-energy threshold and exponent

Here X is an independent completed scale.  Both powers of the active
marked norm are retained in the conductor.  The threshold is precisely
2H + 2A₀ + 2zₐ - N* - N₀ - 3B₀, with all letters obtained from actual
positive norms.  There is no low-scale or empty-puncture specialization.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralBlockPolynomial

open HeckeSkeleton.LowEnergy.LogGeometry
open HeckeSkeleton.LowEnergy.BlockPolynomial
open HeckeSkeleton.LowEnergy.PhysicalBlockPolynomial
open HeckeSkeleton.LowEnergy.CommonMellinTail
open HeckeSkeleton.LowEnergy.Numerics

/-- The threshold for an independent completed scale. -/
def threshold (Z X active linear cube K L : ℝ) : ℝ :=
  2 * scale Z K + 2 * scale Z active + 2 * scale Z L -
    scale Z X - scale Z linear - 3 * scale Z cube

def kernelScale (X active linear cube K L N B : ℝ) : ℝ :=
  (X * (linear * cube ^ 3) / active ^ 2) * N * B ^ 3 / (K ^ 2 * L ^ 2)

theorem kernelScale_eq_rpow
    {Z X active linear cube K L N B : ℝ}
    (hZ : 1 < Z) (hX : 0 < X) (ha : 0 < active)
    (hn : 0 < linear) (hb : 0 < cube) (hK : 0 < K) (hL : 0 < L)
    (hN : 0 < N) (hB : 0 < B) :
    kernelScale X active linear cube K L N B =
      Z ^ (scale Z N + 3 * scale Z B - threshold Z X active linear cube K L) := by
  have hp : 0 < kernelScale X active linear cube K L N B := by
    unfold kernelScale
    positivity
  have hs : scale Z (kernelScale X active linear cube K L N B) =
      scale Z N + 3 * scale Z B - threshold Z X active linear cube K L := by
    unfold kernelScale threshold
    rw [scale_div Z (by positivity) (by positivity),
      scale_mul Z (by positivity) (by positivity),
      scale_mul Z (by positivity) hN,
      scale_div Z (by positivity) (by positivity),
      scale_mul Z hX (by positivity), scale_mul Z hn (by positivity),
      scale_mul Z (by positivity) (by positivity),
      scale_pow, scale_pow, scale_pow, scale_pow, scale_pow]
    ring
  rw [← hs, rpow_scale hZ hp]

/-- Literal local charges, four dyadic scales, and the common kernel give
exactly the general reflected polynomial, retaining the full dual tail. -/
theorem general_polynomial_le
    {Z X active linear cube small K L N B Cf delta : ℝ}
    (hZ : 1 < Z) (hX : 0 < X) (ha : 0 < active)
    (hn : 0 < linear) (hb : 0 < cube) (hs : 0 < small)
    (hK : 0 < K) (hL : 0 < L) (hN : 0 < N) (hB : 0 < B)
    (hdelta : delta ≤ 1) (hcharge : Cf ^ 2 ≤ (small * cube)⁻¹) :
    (Cf ^ 2 / (N * B ^ 2)) *
        sievePolynomial (2 * K) (2 * N) (2 * B) (2 * L) delta *
        scalar (kernelScale X active linear cube K L N B) ^ 2 ≤
      512 * (Z ^ scale Z K * Z ^ scale Z N * Z ^ scale Z B * Z ^ scale Z L) ^ delta *
        weightedReflectedPolynomial Z 0 (scale Z K) (scale Z small) (scale Z cube)
          (scale Z L) (scale Z N) (scale Z B)
          (threshold Z X active linear cube K L) := by
  have hw := charged_weight_le hZ hs hb hN hB hcharge
  have hp := doubled_sievePolynomial_le hK.le hN.le hB.le hL.le hdelta
  have hp0 := sievePolynomial_nonneg (delta := delta)
    (by linarith : 0 ≤ 2 * K) (by linarith : 0 ≤ 2 * N)
    (by linarith : 0 ≤ 2 * B) (by linarith : 0 ≤ 2 * L)
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul hw hp hp0 (by positivity))
    (sq_nonneg (scalar (kernelScale X active linear cube K L N B)))
  apply h.trans_eq
  rw [kernelScale_eq_rpow hZ hX ha hn hb hK hL hN hB]
  unfold weightedReflectedPolynomial sievePolynomial
  simp only [zero_div, zero_sub]
  simp only [rpow_scale hZ hK, rpow_scale hZ hN, rpow_scale hZ hB, rpow_scale hZ hL]
  ring

/-- The displayed exponent is (can-Eref) with O=0, plus the explicit
four-scale sieve loss and the additional positive-line saving. -/
theorem general_exponent_le
    {Z X active linear cube small K L N B Cf delta : ℝ}
    (hZ : 1 < Z) (hX : 0 < X) (ha : 0 < active)
    (hn : 0 < linear) (hb : 0 < cube) (hs : 0 < small)
    (hK : 0 < K) (hL : 0 < L) (hN : 0 < N) (hB : 0 < B)
    (hdelta : delta ≤ 1) (hcharge : Cf ^ 2 ≤ (small * cube)⁻¹) :
    (Cf ^ 2 / (N * B ^ 2)) *
        sievePolynomial (2 * K) (2 * N) (2 * B) (2 * L) delta *
        scalar (kernelScale X active linear cube K L N B) ^ 2 ≤
      3072 * Z ^
        (fullPaperExponent 0 (scale Z K) (scale Z small) (scale Z cube)
          (scale Z L) (scale Z N) (scale Z B)
          (threshold Z X active linear cube K L) +
          delta * (scale Z K + scale Z N + scale Z B + scale Z L)) := by
  have hp := general_polynomial_le hZ hX ha hn hb hs hK hL hN hB hdelta hcharge
  have he := weighted_polynomial_with_sieve_loss (O := 0) (H := scale Z K)
    (S := scale Z small) (B0 := scale Z cube) (z := scale Z L)
    (v := scale Z N) (b := scale Z B)
    (T := threshold Z X active linear cube K L) (delta := delta) hZ.le
  calc
    _ ≤ 512 * (Z ^ scale Z K * Z ^ scale Z N * Z ^ scale Z B * Z ^ scale Z L) ^ delta *
        weightedReflectedPolynomial Z 0 (scale Z K) (scale Z small) (scale Z cube)
          (scale Z L) (scale Z N) (scale Z B)
          (threshold Z X active linear cube K L) := hp
    _ = 512 * ((Z ^ scale Z K * Z ^ scale Z N * Z ^ scale Z B * Z ^ scale Z L) ^ delta *
        weightedReflectedPolynomial Z 0 (scale Z K) (scale Z small) (scale Z cube)
          (scale Z L) (scale Z N) (scale Z B)
          (threshold Z X active linear cube K L)) := by ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 512)
      convert h using 1 <;> ring

/-- A common finite width budget fixes the sieve loss before all blocks. -/
theorem exists_sieve_loss (W eps : ℝ) (hW : 0 ≤ W) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ H v b z : ℝ, H + v + b + z ≤ W →
        delta * (H + v + b + z) ≤ eps := by
  let delta := min 1 (eps / (W + 1))
  have hd : 0 < delta := lt_min zero_lt_one (div_pos heps (by linarith))
  refine ⟨delta, hd, min_le_left _ _, ?_⟩
  intro H v b z hsum
  have hdelta : delta * (W + 1) ≤ eps :=
    (le_div_iff₀ (by linarith : 0 < W + 1)).mp (min_le_right _ _)
  have hmul := mul_le_mul_of_nonneg_left hsum hd.le
  nlinarith

#print axioms kernelScale_eq_rpow
#print axioms general_polynomial_le
#print axioms general_exponent_le
#print axioms exists_sieve_loss

end HeckeSkeleton.LowEnergy.GeneralBlockPolynomial
