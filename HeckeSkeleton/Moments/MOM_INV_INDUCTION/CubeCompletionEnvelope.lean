import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletion
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionBlocks

/-!
# Uniform small powers for the genuine cube decomposition

The divisor cap and the squared finite dyadic count each receive an
arbitrarily small exponent, chosen before all source data. The estimates
use only the fixed node capacity and the actual norm ceiling; no ideal
divisor count is compared with the ideal norm pointwise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionEnvelope

open scoped NumberField Classical

variable (K : Type) [Field K] [NumberField K]

theorem small_power_exponent (A pi N : ℝ) (hA : 0 ≤ A) (hpi : 0 < pi) (hN : N ≤ A) :
    2 * N * (pi / (2 * (A + 1))) ≤ pi := by
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (A + 1))).mpr
  nlinarith

theorem exists_cap_square_bound (A pi : ℝ) (hA : 0 ≤ A) (hpi : 0 < pi) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z N : ℝ), 1 ≤ Z → 0 ≤ N → N ≤ A →
      ∀ B : Finset (Ideal (𝓞 K)),
      (∀ b ∈ B, (b.absNorm : ℝ) ≤ 4 * Z ^ N) →
      cubeCoefficientCap B ^ 2 ≤ C * Z ^ pi := by
  let delta := pi / (2 * (A + 1))
  have hdelta : 0 < delta := div_pos hpi (by positivity)
  obtain ⟨C, hC, hbound⟩ := exists_cubeCoefficientCap_bound (K := K) delta hdelta
  let Ccap := C ^ 2 * (4 : ℝ) ^ (2 * delta)
  refine ⟨max 1 Ccap, le_max_left _ _, ?_⟩
  intro Z N hZ hN0 hN B hb
  have hz0 := zero_lt_one.trans_le hZ
  have hp := Real.rpow_pos_of_pos hz0 N
  have hp1 := Real.one_le_rpow hZ hN0
  have h := pow_le_pow_left₀ (cubeCoefficientCap_pos B).le
    (hbound B (4 * Z ^ N) (by linarith) hb) 2
  have heq : (C * (4 * Z ^ N) ^ delta) ^ 2 = Ccap * Z ^ (2 * N * delta) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 4 * Z ^ N),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hp.le,
      ← Real.rpow_mul hz0.le]
    dsimp only [Ccap]
    rw [show delta * (2 : ℝ) = 2 * delta by ring,
      show N * (2 * delta) = 2 * N * delta by ring]
    ring
  rw [heq] at h
  calc
    _ ≤ Ccap * Z ^ (2 * N * delta) := h
    _ ≤ max 1 Ccap * Z ^ pi := by
      gcongr
      · exact le_max_right (1 : ℝ) Ccap
      · exact small_power_exponent A pi N hA hpi hN

theorem exists_count_square_bound (A pi : ℝ) (hA : 0 ≤ A) (hpi : 0 < pi) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z N : ℝ), 1 ≤ Z → 0 ≤ N → N ≤ A →
      (CubeCompletionBlocks.count (2 * Z ^ N) : ℝ) ^ 2 ≤ C * Z ^ pi := by
  let delta := pi / (2 * (A + 1))
  have hdelta : 0 < delta := div_pos hpi (by positivity)
  obtain ⟨C, hC, hbound⟩ := CubeCompletionBlocks.exists_count_small_power delta hdelta
  let Ccount := C ^ 2 * (2 : ℝ) ^ (2 * delta)
  refine ⟨max 1 Ccount, le_max_left _ _, ?_⟩
  intro Z N hZ hN0 hN
  have hz0 := zero_lt_one.trans_le hZ
  have hp := Real.rpow_pos_of_pos hz0 N
  have hp1 := Real.one_le_rpow hZ hN0
  have h := pow_le_pow_left₀ (Nat.cast_nonneg _)
    (hbound (2 * Z ^ N) (by linarith)) 2
  have heq : (C * (2 * Z ^ N) ^ delta) ^ 2 = Ccount * Z ^ (2 * N * delta) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 2 * Z ^ N),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hp.le,
      ← Real.rpow_mul hz0.le]
    dsimp only [Ccount]
    rw [show delta * (2 : ℝ) = 2 * delta by ring,
      show N * (2 * delta) = 2 * N * delta by ring]
    ring
  rw [heq] at h
  calc
    _ ≤ Ccount * Z ^ (2 * N * delta) := h
    _ ≤ max 1 Ccount * Z ^ pi := by
      gcongr
      · exact le_max_right (1 : ℝ) Ccount
      · exact small_power_exponent A pi N hA hpi hN

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionEnvelope
