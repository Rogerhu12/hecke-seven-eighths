import HeckeSkeleton.HighBinSupport.HighNormFormScalar
/-! A fixed internal power height repairs the order of height thresholds.
These are scalar facts about max(T,Z^kappa). They assert no prime estimate. -/

noncomputable section
namespace HighBinVerified.NormForm

def internalHeight (Z T kappa : ℝ) : ℝ := max T (Z ^ kappa)

theorem le_internalHeight (Z T kappa : ℝ) : T ≤ internalHeight Z T kappa :=
  le_max_left _ _

theorem power_le_internalHeight (Z T kappa : ℝ) :
    Z ^ kappa ≤ internalHeight Z T kappa := le_max_right _ _

theorem internalHeight_idempotent (Z T kappa : ℝ) :
    internalHeight Z (internalHeight Z T kappa) kappa = internalHeight Z T kappa :=
  max_eq_left (le_max_right _ _)

/-- One fixed internal exponent suffices for every smaller external height. -/
theorem internalHeight_eq_power_of_ceiling (Z T kappa ceiling : ℝ)
    (hZ : 1 ≤ Z) (hT : T ≤ Z ^ ceiling) (hceiling : ceiling ≤ kappa) :
    internalHeight Z T kappa = Z ^ kappa :=
  max_eq_right (hT.trans (Real.rpow_le_rpow_of_exponent_le hZ hceiling))

theorem internalHeight_le_power_mul (Z T kappa : ℝ)
    (hZ : 1 ≤ Z) (hT : 0 ≤ T) (hkappa : 0 ≤ kappa) :
    internalHeight Z T kappa ≤ Z ^ kappa * (1 + T) := by
  have hp : 1 ≤ Z ^ kappa := Real.one_le_rpow hZ hkappa
  have hp0 : 0 ≤ Z ^ kappa := zero_le_one.trans hp
  apply max_le
  · calc
      T = 1 * T := (one_mul _).symm
      _ ≤ Z ^ kappa * T := mul_le_mul_of_nonneg_right hp hT
      _ ≤ Z ^ kappa * (1 + T) :=
        mul_le_mul_of_nonneg_left (by linarith) hp0
  · simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + T by linarith) hp0

/-- A fixed degree costs exactly kappa*A additional powers of Z. -/
theorem internalHeight_rpow_bound (Z T kappa A : ℝ)
    (hZ : 1 ≤ Z) (hT : 0 ≤ T) (hkappa : 0 ≤ kappa) (hA : 0 ≤ A) :
    internalHeight Z T kappa ^ A ≤ Z ^ (kappa * A) * (1 + T) ^ A := by
  have hp0 : 0 ≤ Z ^ kappa := Real.rpow_nonneg (zero_le_one.trans hZ) _
  calc
    _ ≤ (Z ^ kappa * (1 + T)) ^ A := Real.rpow_le_rpow
      (hp0.trans (power_le_internalHeight Z T kappa))
      (internalHeight_le_power_mul Z T kappa hZ hT hkappa) hA
    _ = _ := by
      rw [Real.mul_rpow hp0 (by linarith), ← Real.rpow_mul (zero_le_one.trans hZ)]

theorem internalHeight_rpow_absorb (Z T kappa A loss : ℝ)
    (hZ : 1 ≤ Z) (hT : 0 ≤ T) (hkappa : 0 ≤ kappa) (hA : 0 ≤ A)
    (hloss : kappa * A ≤ loss) :
    internalHeight Z T kappa ^ A ≤ Z ^ loss * (1 + T) ^ A := by
  exact (internalHeight_rpow_bound Z T kappa A hZ hT hkappa hA).trans
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hZ hloss)
      (Real.rpow_nonneg (by linarith) _))

/-- The same absorption with an arbitrary existing scale exponent. -/
theorem scale_mul_internalHeight_rpow_absorb (Z T kappa A r loss : ℝ)
    (hZ : 1 ≤ Z) (hT : 0 ≤ T) (hkappa : 0 ≤ kappa) (hA : 0 ≤ A)
    (hloss : kappa * A ≤ loss) :
    Z ^ r * internalHeight Z T kappa ^ A ≤ Z ^ (r + loss) * (1 + T) ^ A := by
  calc
    _ ≤ Z ^ r * (Z ^ loss * (1 + T) ^ A) := mul_le_mul_of_nonneg_left
      (internalHeight_rpow_absorb Z T kappa A loss hZ hT hkappa hA hloss)
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)
    _ = _ := by
      rw [Real.rpow_add (zero_lt_one.trans_le hZ)]
      ring

end HighBinVerified.NormForm

#print axioms HighBinVerified.NormForm.internalHeight_idempotent
#print axioms HighBinVerified.NormForm.internalHeight_eq_power_of_ceiling
#print axioms HighBinVerified.NormForm.internalHeight_rpow_absorb
#print axioms HighBinVerified.NormForm.scale_mul_internalHeight_rpow_absorb
