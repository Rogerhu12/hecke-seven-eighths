import HeckeSkeleton.Moments.MOM_INV_STEP.Normalization

/-!
# Uniform elementary budgets for the actual second principal terms

These identities consume the physical row and original inverse-column
lengths, rather than an assumed canonical energy estimate.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep.PrincipalScaleBudget

/-- The second physical principal has the trivial row times column
scale. After the first true prefactor this is below the parent F. -/
theorem second_principal_exponent
    (M r ell V delta A B R j t : ℝ) :
    firstKappa M r ell V delta A B R +
      firstPhysicalHeight M r ell V delta B j + (r - A - B - t) =
      (r + 3 * ell + V) - ell - 2 * B - R / 2 - j - t := by
  unfold firstKappa firstPhysicalHeight
  ring

/-- Account for the first exponential enclosure, the retained first
frequency radius, and a three-eta column enclosure. -/
theorem second_principal_budget
    (Z : ℝ) (hZ : 1 ≤ Z)
    (M r ell V delta A B R j t eta tau pi loss : ℝ)
    (hell : 0 ≤ ell) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hj : 0 ≤ j) (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hloss : loss ≤ pi) :
    Z ^ firstKappa M r ell V delta A B R *
      Real.exp ((9 / 2 : ℝ) * (eta * Real.log Z)) *
      Z ^ (firstPhysicalHeight M r ell V delta B j + 12 * eta + tau +
        (r - A - B - t + 3 * eta) + loss) ≤
      Z ^ (r + 3 * ell + V + 26 * eta + tau + pi) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have he : Real.exp ((9 / 2 : ℝ) * (eta * Real.log Z)) =
      Z ^ ((9 / 2 : ℝ) * eta) := by
    rw [Real.rpow_def_of_pos hz]
    congr 1
    ring
  rw [he, ← Real.rpow_add hz, ← Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hi := second_principal_exponent M r ell V delta A B R j t
  linarith

/-- The density and coefficient small-power exponents are fixed before
the physical lengths range through their common bounded box. -/
theorem exists_uniform_inverse_principal_losses
    (Hmax Umax loss : ℝ) (hHmax : 0 ≤ Hmax) (hUmax : 0 ≤ Umax)
    (hloss : 0 < loss) :
    ∃ eps rowEps : ℝ, 0 < eps ∧ 0 < rowEps ∧
      ∀ H U : ℝ, H ≤ Hmax → U ≤ Umax →
        rowEps * H + 2 * eps * U ≤ loss ∧ 4 * eps * U ≤ loss := by
  let eps := loss / (8 * (Umax + 1))
  let rowEps := loss / (2 * (Hmax + 1))
  have heps : 0 < eps := div_pos hloss (by positivity)
  have hrow : 0 < rowEps := div_pos hloss (by positivity)
  have heps_eq : 8 * eps * (Umax + 1) = loss := by
    have hh := div_mul_cancel₀ loss
      (show 8 * (Umax + 1) ≠ 0 by positivity)
    change eps * (8 * (Umax + 1)) = loss at hh
    nlinarith
  have hrow_eq : 2 * rowEps * (Hmax + 1) = loss := by
    have hh := div_mul_cancel₀ loss
      (show 2 * (Hmax + 1) ≠ 0 by positivity)
    change rowEps * (2 * (Hmax + 1)) = loss at hh
    nlinarith
  refine ⟨eps, rowEps, heps, hrow, ?_⟩
  intro H U hH hU
  have hh := mul_le_mul_of_nonneg_left hH hrow.le
  have hu := mul_le_mul_of_nonneg_left hU heps.le
  constructor <;> nlinarith

theorem physical_power_identity (Z H U eps rowEps : ℝ) (hZ : 0 < Z) :
    Z ^ (-H - U) * Z ^ ((1 + rowEps) * H) *
      (2 * Z ^ U) ^ (1 + 2 * eps) =
      2 ^ (1 + 2 * eps) * Z ^ (rowEps * H + 2 * eps * U) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (Real.rpow_nonneg hZ.le _), ← Real.rpow_mul hZ.le]
  calc
    _ = 2 ^ (1 + 2 * eps) *
        (Z ^ (-H - U) * Z ^ ((1 + rowEps) * H) * Z ^ (U * (1 + 2 * eps))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
      congr 2
      ring

theorem zero_power_identity (Z H U eps : ℝ) (hZ : 0 < Z) :
    Z ^ (-H - U) * Z ^ H * (2 * Z ^ U) ^ (1 + 4 * eps) =
      2 ^ (1 + 4 * eps) * Z ^ (4 * eps * U) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (Real.rpow_nonneg hZ.le _), ← Real.rpow_mul hZ.le]
  calc
    _ = 2 ^ (1 + 4 * eps) *
        (Z ^ (-H - U) * Z ^ H * Z ^ (U * (1 + 4 * eps))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
      congr 2
      ring

end HeckeSkeleton.Moments.MOMInvStep.PrincipalScaleBudget

end

