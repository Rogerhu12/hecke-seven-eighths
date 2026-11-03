import FiniteAffineCorrelationBound
import Mathlib.NumberTheory.JacobiSum.Basic

/-! Source-only, uncompiled. Exact genuine finite-field affine correlation.
The trivial character is MulChar's zero extension, including at frequency zero. -/
noncomputable section
namespace HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators ComplexConjugate
variable {F : Type*} [Field F] [Fintype F]

private def fieldAffineFibreEquiv (n₁ n₂ k : F) (h₁ : n₁ ≠ 0) :
    F ≃ {p : F × F // n₂ * p.1 - n₁ * p.2 = k} where
  toFun x := ⟨(x, (n₂ * x - k) / n₁), by
    dsimp
    field_simp [h₁] <;> ring⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      apply (div_eq_iff h₁).mpr
      linear_combination p.property

theorem affineCorrelation_mulChar_eq_sum (χ : MulChar F ℂ)
    (n₁ n₂ k : F) (h₁ : n₁ ≠ 0) :
    affineCorrelation χ n₁ n₂ k =
      ∑ x : F, χ x * conj (χ ((n₂ * x - k) / n₁)) := by
  rw [affineCorrelation_eq_sum_fibre]
  symm
  exact Fintype.sum_equiv (fieldAffineFibreEquiv n₁ n₂ k h₁) _ _ (fun _ => rfl)

/-- The sign comes from y = -(k/n₁)(1-t), not from changing the fibre relation. -/
theorem affineCorrelation_mulChar_eq_jacobiSum (χ : MulChar F ℂ)
    (n₁ n₂ k : F) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (hk : k ≠ 0) :
    affineCorrelation χ n₁ n₂ k = χ (-n₁ / n₂) * jacobiSum χ χ⁻¹ := by
  rw [affineCorrelation_mulChar_eq_sum χ n₁ n₂ k h₁]
  calc
    _ = ∑ t : F, χ ((k / n₂) * t) *
        conj (χ ((n₂ * ((k / n₂) * t) - k) / n₁)) :=
      (Equiv.sum_comp (Equiv.mulLeft₀ (k / n₂) (div_ne_zero hk h₂)) _).symm
    _ = ∑ t : F, χ (-n₁ / n₂) * (χ t * χ⁻¹ (1 - t)) := by
      apply Finset.sum_congr rfl
      intro t _
      have hy : (n₂ * ((k / n₂) * t) - k) / n₁ =
          (-k / n₁) * (1 - t) := by field_simp [h₁, h₂] <;> ring
      rw [hy, starRingEnd_apply, MulChar.star_apply', map_mul, map_mul]
      have hc : χ (k / n₂) * χ⁻¹ (-k / n₁) = χ (-n₁ / n₂) := by
        rw [MulChar.inv_apply', ← map_mul]
        congr 1
        field_simp [h₁, h₂, hk] <;> ring
      calc
        _ = (χ (k / n₂) * χ⁻¹ (-k / n₁)) * (χ t * χ⁻¹ (1 - t)) := by ring
        _ = _ := by rw [hc]
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem affineCorrelation_mulChar_zero (χ : MulChar F ℂ)
    (n₁ n₂ : F) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) :
    affineCorrelation χ n₁ n₂ 0 = χ (n₁ / n₂) * ((Fintype.card F : ℂ) - 1) := by
  rw [affineCorrelation_mulChar_eq_sum χ n₁ n₂ 0 h₁]
  have he (x : F) : χ x * conj (χ ((n₂ * x - 0) / n₁)) =
      χ (n₁ / n₂) * (1 : MulChar F ℂ) x := by
    have hy : (n₂ * x - 0) / n₁ = (n₂ / n₁) * x := by ring
    rw [hy, starRingEnd_apply, MulChar.star_apply', map_mul]
    have hc : χ⁻¹ (n₂ / n₁) = χ (n₁ / n₂) := by
      rw [MulChar.inv_apply']
      congr 1
      field_simp [h₁, h₂] <;> ring
    rw [hc]
    calc
      _ = χ (n₁ / n₂) * ((χ * χ⁻¹) x) := by rw [MulChar.mul_apply]; ring
      _ = _ := by simp
  simp_rw [he]
  rw [← Finset.mul_sum, MulChar.sum_one_eq_card_units]
  have hcard := Fintype.card_eq_card_units_add_one (α := F)
  have hcast : (Fintype.card F : ℂ) = (Fintype.card Fˣ : ℂ) + 1 := by
    exact_mod_cast hcard
  rw [hcast]
  ring

theorem affineCorrelation_mulChar_nonzero (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (n₁ n₂ k : F) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (hk : k ≠ 0) :
    affineCorrelation χ n₁ n₂ k = -χ (n₁ / n₂) := by
  rw [affineCorrelation_mulChar_eq_jacobiSum χ n₁ n₂ k h₁ h₂ hk,
    jacobiSum_nontrivial_inv hχ, mul_neg, ← map_mul]
  congr 1
  ring

theorem affineCorrelation_trivial_nonzero
    (n₁ n₂ k : F) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (hk : k ≠ 0) :
    affineCorrelation (1 : MulChar F ℂ) n₁ n₂ k = (Fintype.card F : ℂ) - 2 := by
  rw [affineCorrelation_mulChar_eq_jacobiSum (1 : MulChar F ℂ) n₁ n₂ k h₁ h₂ hk,
    inv_one, jacobiSum_one_one, MulChar.one_apply (isUnit_iff_ne_zero.mpr
      (div_ne_zero (neg_ne_zero.mpr h₁) h₂)), one_mul]

/-- With the first column zero, the second variable still ranges over the
whole field. The fixed first coordinate keeps its original zero mask. -/
theorem affineCorrelation_mulChar_first_zero (χ : MulChar F ℂ)
    (n₂ k : F) (h₂ : n₂ ≠ 0) :
    affineCorrelation χ 0 n₂ k = χ (k / n₂) * conj (∑ x : F, χ x) := by
  have hbez : n₂⁻¹ * n₂ - (0 : F) * 0 = 1 := by simp [h₂]
  rw [affineCorrelation_eq_sum_parameter χ 0 n₂ n₂⁻¹ 0 hbez k]
  simp only [zero_mul, zero_add, add_zero]
  have hx : n₂⁻¹ * k = k / n₂ := by ring
  rw [hx, ← Finset.mul_sum]
  have hs : (∑ t : F, χ (n₂ * t)) = ∑ x : F, χ x :=
    Equiv.sum_comp (Equiv.mulLeft₀ n₂ h₂) χ
  rw [← map_sum, hs]

/-- The minus sign is forced by n₂*x - n₁*y = k. -/
theorem affineCorrelation_mulChar_second_zero (χ : MulChar F ℂ)
    (n₁ k : F) (h₁ : n₁ ≠ 0) :
    affineCorrelation χ n₁ 0 k = (∑ x : F, χ x) * conj (χ (-k / n₁)) := by
  rw [affineCorrelation_mulChar_eq_sum χ n₁ 0 k h₁]
  simp only [zero_mul, zero_sub]
  rw [Finset.sum_mul]

theorem affineCorrelation_mulChar_first_zero_nontrivial
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) (n₂ k : F) (h₂ : n₂ ≠ 0) :
    affineCorrelation χ 0 n₂ k = 0 := by
  rw [affineCorrelation_mulChar_first_zero χ n₂ k h₂,
    MulChar.sum_eq_zero_of_ne_one hχ, map_zero, mul_zero]

theorem affineCorrelation_mulChar_second_zero_nontrivial
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) (n₁ k : F) (h₁ : n₁ ≠ 0) :
    affineCorrelation χ n₁ 0 k = 0 := by
  rw [affineCorrelation_mulChar_second_zero χ n₁ k h₁,
    MulChar.sum_eq_zero_of_ne_one hχ, zero_mul]

private theorem complex_card_units_eq :
    (Fintype.card Fˣ : ℂ) = (Fintype.card F : ℂ) - 1 := by
  have h := Fintype.card_eq_card_units_add_one (α := F)
  have hc : (Fintype.card F : ℂ) = (Fintype.card Fˣ : ℂ) + 1 := by
    exact_mod_cast h
  rw [hc]
  ring

theorem affineCorrelation_trivial_first_zero
    (n₂ k : F) (h₂ : n₂ ≠ 0) :
    affineCorrelation (1 : MulChar F ℂ) 0 n₂ k =
      if k = 0 then 0 else (Fintype.card F : ℂ) - 1 := by
  rw [affineCorrelation_mulChar_first_zero (1 : MulChar F ℂ) n₂ k h₂,
    MulChar.sum_one_eq_card_units]
  by_cases hk : k = 0
  · subst k
    simp [MulChar.map_zero]
  · rw [if_neg hk, MulChar.one_apply (isUnit_iff_ne_zero.mpr (div_ne_zero hk h₂))]
    simpa using complex_card_units_eq (F := F)

theorem affineCorrelation_trivial_second_zero
    (n₁ k : F) (h₁ : n₁ ≠ 0) :
    affineCorrelation (1 : MulChar F ℂ) n₁ 0 k =
      if k = 0 then 0 else (Fintype.card F : ℂ) - 1 := by
  rw [affineCorrelation_mulChar_second_zero (1 : MulChar F ℂ) n₁ k h₁,
    MulChar.sum_one_eq_card_units]
  by_cases hk : k = 0
  · subst k
    simp [MulChar.map_zero]
  · rw [if_neg hk, MulChar.one_apply (isUnit_iff_ne_zero.mpr
      (div_ne_zero (neg_ne_zero.mpr hk) h₁))]
    simpa using complex_card_units_eq (F := F)

end HeckeGeneral.Arithmetic.PeriodicFourier
