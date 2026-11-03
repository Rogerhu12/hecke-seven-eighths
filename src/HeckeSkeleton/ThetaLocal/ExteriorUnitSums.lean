import HeckeSkeleton.ThetaLocal.ExteriorFiniteSums

/-!
# Exterior local tables in the project's unit-sum convention

The five definitions `localTau`, `digitMask`, `sphericalDigit`,
`localWeylScalar`, and `localWeylExponent` reproduce the formulas in
`HeckeGeneral/Analysis/MarkedThetaReflection.lean`, with one residue field
and its two characters as parameters.  The transfer from the project's
actual arithmetic characters requires checking their primitivity, sextic
order, Gauss normalization, and residue cardinality.

All assertions here evaluate explicit finite sums.  They do not assert
that a newly defined sum is already an actual Whittaker coefficient.
-/

namespace HeckeSkeleton.ThetaLocal.ResidueField

open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] [Fintype F]

/-- A finite sum over units equals the sum over the whole field if its zero term vanishes. -/
theorem sum_units_eq_sum (f : F → ℂ) (hf : f 0 = 0) :
    (∑ x : Fˣ, f x) = ∑ x : F, f x := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f 0, hf, zero_add]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)

def localTau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : Fin 6) : ℂ :=
  ∑ x : Fˣ, χ x ^ (-(j.val : ℤ)) * ψ x

def digitMask (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : Fin 6) (x : F) : ℂ :=
  if j.val = 0 then
    if x = 0 then 1 - (Fintype.card F : ℂ)⁻¹ else -(Fintype.card F : ℂ)⁻¹
  else (localTau χ ψ j)⁻¹ * χ x ^ (-(j.val : ℤ))

/-- The genuinely normalized finite Gauss sum, rather than a free coefficient. -/
def gammaTwo (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  (Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹ * gaussSum (χ ^ 2) ψ

def sphericalDigit (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (e : ℕ) : ℂ :=
  if e % 3 = 0 then (Fintype.card F : ℂ)⁻¹ ^ (e / 3)
  else if e % 3 = 1 then
    (Fintype.card F : ℂ)⁻¹ ^ (e / 3) *
      (Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹ * gammaTwo χ ψ
  else 0

def localWeylScalar (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : Fin 6) (e : ℕ) : ℂ :=
  sphericalDigit χ ψ e * ∑ x : Fˣ,
    digitMask χ ψ j x * χ x ^ 4 * (if e = 0 then ψ ((x⁻¹ : Fˣ) : F) else 1)

def localWeylExponent (j : Fin 6) (e : ℕ) : ℕ :=
  if e = 0 then (8 - j.val) % 6 else (4 + 2 * e) % 6

/-- The complete finite Weyl sum at an arbitrary unit argument. -/
def unitWeylSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (W : ℕ → ℂ) (β : F → ℂ) (e : ℕ) (t : Fˣ) : ℂ :=
  W e * χ t ^ (4 + 2 * e) * ∑ v : Fˣ,
    β v * χ v ^ 4 * (if e = 0 then ψ ((t : F) / v) else 1)

def markedWeylValue (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (e : ℕ) (t : Fˣ) : ℂ :=
  unitWeylSum χ ψ (sphericalDigit χ ψ) uniformDigit e t

theorem localTau_eq_digitTau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : Fin 6) :
    localTau χ ψ j = digitTau χ ψ j.val := by
  unfold localTau digitTau gaussSum
  calc
    _ = ∑ x : Fˣ, (χ⁻¹ ^ j.val) x * ψ x := by
      apply Finset.sum_congr rfl
      intro x _
      simp [MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv', zpow_neg, inv_pow]
    _ = _ := sum_units_eq_sum (fun v : F => (χ⁻¹ ^ j.val) v * ψ v)
      (by simp [MulChar.map_zero])

theorem digitMask_eq_ordinaryDigit (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : Fin 6) :
    digitMask χ ψ j = ordinaryDigit χ ψ j.val := by
  funext x
  by_cases hj : j.val = 0
  · simp [digitMask, ordinaryDigit, hj]
  · simp [digitMask, ordinaryDigit, hj, localTau_eq_digitTau,
      MulChar.pow_apply' χ hj, MulChar.pow_apply' χ⁻¹ hj,
      MulChar.inv_apply_eq_inv', zpow_neg, inv_pow]

theorem sphericalDigit_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    sphericalDigit χ ψ 0 = 1 := by simp [sphericalDigit]

theorem sphericalDigit_vanishes (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (e : ℕ) (he : e % 3 = 2) : sphericalDigit χ ψ e = 0 := by
  simp [sphericalDigit, he]

theorem unitWeylSum_eq_finiteWeylSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (W : ℕ → ℂ) (β : F → ℂ) (e : ℕ) (t : Fˣ) :
    unitWeylSum χ ψ W β e t = finiteWeylSum χ ψ W β e t := by
  unfold unitWeylSum finiteWeylSum
  congr 1
  rw [sum_units_eq_sum (fun v : F =>
      β v * χ v ^ 4 * (if e = 0 then ψ ((t : F) / v) else 1))
    (by simp [MulChar.map_zero])]
  simp only [MulChar.pow_apply' χ (by decide : (4 : ℕ) ≠ 0)]

theorem localWeylScalar_eq_unitWeylSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : Fin 6) (e : ℕ) :
    localWeylScalar χ ψ j e =
      unitWeylSum χ ψ (sphericalDigit χ ψ) (digitMask χ ψ j) e 1 := by
  simp [localWeylScalar, unitWeylSum, one_div]

theorem localWeylScalar_eq_finiteWeylSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : Fin 6) (e : ℕ) :
    localWeylScalar χ ψ j e =
      finiteWeylSum χ ψ (sphericalDigit χ ψ) (ordinaryDigit χ ψ j.val) e 1 := by
  rw [localWeylScalar_eq_unitWeylSum, unitWeylSum_eq_finiteWeylSum,
    digitMask_eq_ordinaryDigit]

theorem sqrt_card_squared :
    (Real.sqrt (Fintype.card F : ℝ) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
  exact_mod_cast Real.sq_sqrt (show 0 ≤ (Fintype.card F : ℝ) by positivity)

/-- The normalization in the task: `q⁻¹ G(χ²) = q⁻¹ᐟ² γ₂`. -/
theorem gauss_normalization (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    (Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ 2) ψ =
      (Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹ * gammaTwo χ ψ := by
  unfold gammaTwo
  rw [← sqrt_card_squared (F := F), pow_two, mul_inv_rev]
  ring

/-- Exact active-mark table in the same unit-sum convention as the project. -/
theorem markedWeylValue_table (χ : MulChar F ℂ) (hχ6 : χ ^ 6 = 1)
    (hχ4 : χ ^ 4 ≠ 1) (ψ : AddChar F ℂ) (e : ℕ) (t : Fˣ) :
    markedWeylValue χ ψ e t =
      if e = 0 then (Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹ * gammaTwo χ ψ * χ t ^ 2
      else 0 := by
  rw [markedWeylValue, unitWeylSum_eq_finiteWeylSum,
    mark_digit_table χ hχ6 hχ4 ψ _ (sphericalDigit_zero χ ψ)]
  by_cases he : e = 0 <;> simp [he, gauss_normalization]

/-- Residue cardinality in the ordinary positive-valuation table. -/
theorem card_units_complex : (Fintype.card Fˣ : ℂ) = (Fintype.card F : ℂ) - 1 := by
  rw [Fintype.card_units, Nat.cast_sub (show 1 ≤ Fintype.card F from Fintype.card_pos)]
  simp

/-- The inversion of the effective character gives precisely `χ^(j-4)` modulo six. -/
theorem effective_character_inverse (χ : MulChar F ℂ) (hχ6 : χ ^ 6 = 1) (j : Fin 6) :
    (χ⁻¹ ^ j.val * χ ^ 4)⁻¹ = χ ^ ((j.val + 2) % 6) := by
  apply inv_eq_of_mul_eq_one_right
  fin_cases j <;> norm_num <;> group <;> simpa using hχ6

/-- Ordinary table at valuation zero for every nonzero row exponent. -/
theorem localWeylScalar_zero_nonzero (χ : MulChar F ℂ) (hχ6 : χ ^ 6 = 1)
    (ψ : AddChar F ℂ) (j : Fin 6) (hj : j.val ≠ 0) :
    localWeylScalar χ ψ j 0 =
      gaussSum (χ ^ ((j.val + 2) % 6)) ψ / localTau χ ψ j := by
  rw [localWeylScalar_eq_finiteWeylSum,
    ordinary_digit_table_zero χ ψ _ (sphericalDigit_zero χ ψ) j.val hj,
    effective_character_inverse χ hχ6 j, ← localTau_eq_digitTau]
  simp only [Units.val_one, MulChar.map_one, one_pow, mul_one]
  ring

/-- Ordinary exponent-zero scalar at valuation zero. -/
theorem localWeylScalar_zero_zero (χ : MulChar F ℂ) (hχ6 : χ ^ 6 = 1)
    (ψ : AddChar F ℂ) :
    localWeylScalar χ ψ 0 0 =
      -(Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹ * gammaTwo χ ψ := by
  rw [localWeylScalar_eq_finiteWeylSum]
  simp only [Fin.val_zero]
  rw [ordinary_zero_eq_neg_mark,
    mark_digit_zero χ hχ6 ψ _ (sphericalDigit_zero χ ψ)]
  simp only [Units.val_one, MulChar.map_one, one_pow, mul_one, gauss_normalization]
  ring

/-- At positive valuation only ordinary exponent four remains. -/
theorem localWeylScalar_positive (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (j : Fin 6) (e : ℕ) (he : e ≠ 0) :
    localWeylScalar χ ψ j e =
      if j.val = 4 then
        ((Fintype.card F : ℂ) - 1) / localTau χ ψ j * sphericalDigit χ ψ e
      else 0 := by
  rw [localWeylScalar_eq_finiteWeylSum]
  by_cases hj : j.val = 0
  · have hχ4 : χ ^ 4 ≠ 1 := by
      apply pow_ne_one_of_lt_orderOf (by decide : (4 : ℕ) ≠ 0)
      simpa [hχ] using (show (4 : ℕ) < 6 by decide)
    rw [hj, ordinary_zero_eq_neg_mark, mark_digit_positive χ hχ4 ψ _ e he]
    simp [hj]
  · rw [ordinary_digit_table_positive_sextic χ hχ ψ _ j.val hj j.isLt e he,
      card_units_complex, ← localTau_eq_digitTau]
    by_cases hj4 : j.val = 4 <;> simp [hj4] <;> ring

theorem localWeylScalar_support (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : Fin 6) (e : ℕ) (he : e % 3 = 2) :
    localWeylScalar χ ψ j e = 0 := by
  rw [localWeylScalar, sphericalDigit_vanishes χ ψ e he, zero_mul]

theorem localTau_ne_zero (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (j : Fin 6) (hj : j.val ≠ 0) :
    localTau χ ψ j ≠ 0 := by
  rw [localTau_eq_digitTau]
  apply digit_tau_ne_zero χ ψ hψ j.val
  apply pow_ne_one_of_lt_orderOf hj
  simpa [orderOf_inv, hχ] using j.isLt

theorem localTau_norm (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (j : Fin 6) (hj : j.val ≠ 0) :
    ‖localTau χ ψ j‖ = Real.sqrt (Fintype.card F : ℝ) := by
  rw [localTau_eq_digitTau]
  apply gauss_sum_norm _ _ ψ hψ
  apply pow_ne_one_of_lt_orderOf hj
  simpa [orderOf_inv, hχ] using j.isLt

theorem gammaTwo_norm (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) : ‖gammaTwo χ ψ‖ = 1 := by
  have hχ2 : χ ^ 2 ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by decide : (2 : ℕ) ≠ 0)
    simpa [hχ] using (show (2 : ℕ) < 6 by decide)
  have hq : Real.sqrt (Fintype.card F : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos))
  rw [gammaTwo, norm_mul, norm_inv, gauss_sum_norm _ hχ2 ψ hψ]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_mul_cancel₀ hq]

/-- The row-prime coefficient is a unit complex number. -/
theorem row_prime_scalar_norm (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖localWeylScalar χ ψ 1 0‖ = 1 := by
  have hχ6 : χ ^ 6 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hχ3 : χ ^ 3 ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by decide : (3 : ℕ) ≠ 0)
    simpa [hχ] using (show (3 : ℕ) < 6 by decide)
  rw [localWeylScalar_zero_nonzero χ hχ6 ψ 1 (by decide)]
  change ‖gaussSum (χ ^ 3) ψ / localTau χ ψ 1‖ = 1
  rw [norm_div, gauss_sum_norm _ hχ3 ψ hψ, localTau_norm χ hχ ψ hψ 1 (by decide)]
  exact div_self (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)))

end
end HeckeSkeleton.ThetaLocal.ResidueField
