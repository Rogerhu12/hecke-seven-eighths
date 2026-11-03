import HeckeSkeleton.ThetaLocal.ExteriorUnitSums

/-! # Unit phases and uniform bounds for the exterior digit tables -/

namespace HeckeSkeleton.ThetaLocal.ResidueField

open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

theorem character_unit_power_periodic (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (t : Fˣ) (n : ℕ) : χ t ^ (n % 6) = χ t ^ n := by
  have h := congrArg (fun η : MulChar F ℂ => η (t : F)) (pow_mod_orderOf χ n)
  simpa only [hχ, MulChar.pow_apply_coe] using h

/-- The unit exponent at depth zero is exactly `(8-j) mod 6`. -/
theorem depth_zero_unit_phase (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (j : Fin 6) (t : Fˣ) :
    χ t ^ 4 * (χ⁻¹ ^ j.val * χ ^ 4) t = χ t ^ ((8 - j.val) % 6) := by
  have hc : χ ^ 4 * (χ⁻¹ ^ j.val * χ ^ 4) = χ ^ (8 - j.val) := by
    fin_cases j <;> norm_num <;> group
  have h := congrArg (fun η : MulChar F ℂ => η (t : F)) hc
  calc
    _ = χ t ^ (8 - j.val) := by
      simpa only [MulChar.mul_apply, MulChar.pow_apply_coe] using h
    _ = _ := (character_unit_power_periodic χ hχ t _).symm

/-- The finite sum separates into the project's scalar and exponent.
The scalar is evaluated at `t=1`; the dependence on `t` is proved. -/
theorem unitWeylSum_phase_separation (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (j : Fin 6) (e : ℕ) (t : Fˣ) :
    unitWeylSum χ ψ (sphericalDigit χ ψ) (digitMask χ ψ j) e t =
      localWeylScalar χ ψ j e * χ t ^ localWeylExponent j e := by
  have hχ6 : χ ^ 6 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hχ4 : χ ^ 4 ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by decide : (4 : ℕ) ≠ 0)
    simpa [hχ] using (show (4 : ℕ) < 6 by decide)
  rw [unitWeylSum_eq_finiteWeylSum, digitMask_eq_ordinaryDigit]
  by_cases he : e = 0
  · subst e
    by_cases hj : j.val = 0
    · have hj' : j = 0 := Fin.ext hj
      subst j
      simp only [Fin.val_zero]
      rw [ordinary_zero_eq_neg_mark,
        mark_digit_zero χ hχ6 ψ _ (sphericalDigit_zero χ ψ),
        localWeylScalar_zero_zero χ hχ6 ψ]
      rw [gauss_normalization]
      norm_num [localWeylExponent]
    · rw [ordinary_digit_table_zero χ ψ _ (sphericalDigit_zero χ ψ) j.val hj,
        localWeylScalar_zero_nonzero χ hχ6 ψ j hj,
        effective_character_inverse χ hχ6 j, ← localTau_eq_digitTau]
      have hp := depth_zero_unit_phase χ hχ j t
      calc
        _ = (gaussSum (χ ^ ((j.val + 2) % 6)) ψ / localTau χ ψ j) *
            (χ t ^ 4 * (χ⁻¹ ^ j.val * χ ^ 4) t) := by ring
        _ = _ := by rw [hp]; rfl
  · by_cases hj : j.val = 0
    · rw [hj, ordinary_zero_eq_neg_mark, mark_digit_positive χ hχ4 ψ _ e he,
        localWeylScalar_positive χ hχ ψ j e he]
      simp [hj]
    · rw [ordinary_digit_table_positive_sextic χ hχ ψ _ j.val hj j.isLt e he,
        localWeylScalar_positive χ hχ ψ j e he,
        card_units_complex, ← localTau_eq_digitTau]
      by_cases hj4 : j.val = 4
      · simp only [if_pos hj4, localWeylExponent, if_neg he]
        rw [character_unit_power_periodic χ hχ]
        ring
      · simp [hj4]

/-- Every depth-zero ordinary scalar has modulus at most one. -/
theorem localWeylScalar_zero_norm_le (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (j : Fin 6) :
    ‖localWeylScalar χ ψ j 0‖ ≤ 1 := by
  have hχ6 : χ ^ 6 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hcard : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < Real.sqrt (Fintype.card F : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsqrt : 1 ≤ Real.sqrt (Fintype.card F : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ (Fintype.card F : ℝ) by positivity)
    nlinarith [Real.sqrt_nonneg (Fintype.card F : ℝ)]
  by_cases hj : j.val = 0
  · have hj' : j = 0 := Fin.ext hj
    subst j
    rw [localWeylScalar_zero_zero χ hχ6 ψ, norm_mul, norm_neg, norm_inv,
      gammaTwo_norm χ hχ ψ hψ, mul_one]
    have hn : ‖(Real.sqrt (Fintype.card F : ℝ) : ℂ)‖ = Real.sqrt (Fintype.card F : ℝ) := by
      simp [Real.sqrt_nonneg]
    rw [hn]
    exact inv_le_one_of_one_le₀ hsqrt
  · rw [localWeylScalar_zero_nonzero χ hχ6 ψ j hj, norm_div,
      localTau_norm χ hχ ψ hψ j hj]
    by_cases hn : (j.val + 2) % 6 = 0
    · have hψne : ψ ≠ 1 := by simpa using hψ (one_ne_zero : (1 : F) ≠ 0)
      rw [hn, pow_zero, gaussSum_one_left hψne]
      simp only [norm_neg, norm_one, one_div]
      exact inv_le_one_of_one_le₀ hsqrt
    · have hc : χ ^ ((j.val + 2) % 6) ≠ 1 := by
        apply pow_ne_one_of_lt_orderOf hn
        rw [hχ]
        exact Nat.mod_lt _ (by decide)
      rw [gauss_sum_norm _ hc ψ hψ, div_self (ne_of_gt hpos)]

/-- At positive valuation the surviving scalar is bounded by
`sqrt(q)` times the spherical coefficient. -/
theorem localWeylScalar_positive_norm_le (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (j : Fin 6) (e : ℕ) (he : e ≠ 0) :
    ‖localWeylScalar χ ψ j e‖ ≤
      Real.sqrt (Fintype.card F : ℝ) * ‖sphericalDigit χ ψ e‖ := by
  rw [localWeylScalar_positive χ hχ ψ j e he]
  by_cases hj : j.val = 4
  · rw [if_pos hj, norm_mul, norm_div, localTau_norm χ hχ ψ hψ j (by omega)]
    have hcard : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
    have hn : ‖(Fintype.card F : ℂ) - 1‖ = (Fintype.card F : ℝ) - 1 := by
      simpa using Complex.norm_of_nonneg (show 0 ≤ (Fintype.card F : ℝ) - 1 by linarith)
    rw [hn]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hpos : 0 < Real.sqrt (Fintype.card F : ℝ) := Real.sqrt_pos.mpr (by positivity)
    apply (div_le_iff₀ hpos).mpr
    have hs := Real.sq_sqrt (show 0 ≤ (Fintype.card F : ℝ) by positivity)
    nlinarith
  · rw [if_neg hj, norm_zero]
    positivity

theorem sphericalDigit_three_mul (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (k : ℕ) :
    sphericalDigit χ ψ (3 * k) = (Fintype.card F : ℂ)⁻¹ ^ k := by
  have hm : (3 * k) % 3 = 0 := by omega
  have hd : (3 * k) / 3 = k := by omega
  simp [sphericalDigit, hm, hd]

theorem sphericalDigit_three_mul_add_one (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (k : ℕ) :
    sphericalDigit χ ψ (3 * k + 1) =
      (Fintype.card F : ℂ)⁻¹ ^ k *
        (Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹ * gammaTwo χ ψ := by
  have hm : (3 * k + 1) % 3 = 1 := by omega
  have hd : (3 * k + 1) / 3 = k := by omega
  simp [sphericalDigit, hm, hd]

theorem sphericalDigit_three_mul_norm (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (k : ℕ) :
    ‖sphericalDigit χ ψ (3 * k)‖ = (Fintype.card F : ℝ)⁻¹ ^ k := by
  rw [sphericalDigit_three_mul, norm_pow, norm_inv, Complex.norm_natCast]

theorem sphericalDigit_three_mul_add_one_norm (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (k : ℕ) :
    ‖sphericalDigit χ ψ (3 * k + 1)‖ =
      (Fintype.card F : ℝ)⁻¹ ^ k * (Real.sqrt (Fintype.card F : ℝ))⁻¹ := by
  rw [sphericalDigit_three_mul_add_one]
  simp only [norm_mul, norm_pow, norm_inv, Complex.norm_natCast,
    gammaTwo_norm χ hχ ψ hψ, mul_one]
  simp [Real.sqrt_nonneg]

/-- The manuscript's frozen majorant at valuations congruent to one modulo three. -/
theorem localWeylScalar_three_mul_add_one_norm_le (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (j : Fin 6) (k : ℕ) :
    ‖localWeylScalar χ ψ j (3 * k + 1)‖ ≤ (Fintype.card F : ℝ)⁻¹ ^ k := by
  have hq : Real.sqrt (Fintype.card F : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos))
  calc
    _ ≤ Real.sqrt (Fintype.card F : ℝ) * ‖sphericalDigit χ ψ (3 * k + 1)‖ :=
      localWeylScalar_positive_norm_le χ hχ ψ hψ j _ (by omega)
    _ = Real.sqrt (Fintype.card F : ℝ) *
        ((Fintype.card F : ℝ)⁻¹ ^ k * (Real.sqrt (Fintype.card F : ℝ))⁻¹) := by
      rw [sphericalDigit_three_mul_add_one_norm χ hχ ψ hψ]
    _ = _ := by rw [mul_left_comm, mul_inv_cancel₀ hq, mul_one]

/-- The manuscript's frozen majorant at positive valuations divisible by three. -/
theorem localWeylScalar_three_mul_succ_norm_le (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (j : Fin 6) (k : ℕ) :
    ‖localWeylScalar χ ψ j (3 * (k + 1))‖ ≤
      Real.sqrt (Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ (k + 1) := by
  have h := localWeylScalar_positive_norm_le χ hχ ψ hψ j (3 * (k + 1)) (by omega)
  rwa [sphericalDigit_three_mul_norm] at h

end
end HeckeSkeleton.ThetaLocal.ResidueField
