module

public import HeckeSkeleton.Moments.MOM_INV_STEP.CubeAlgebra
public import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# The primitive digit of the actual first source

The two cube exponents are kept separately until the conjugate product is
formed. Their signed difference becomes their sum modulo six. A zero digit
produces the principal character's zero mask, including at the zero residue.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.LocalDigits

open CubeAlgebra
open scoped BigOperators Classical

theorem three_mul_parity_cast (m : ℕ) :
    (3 : ZMod 6) * (bit (parity m) : ZMod 6) = 3 * (m : ZMod 6) := by
  rw [bit_parity]
  have h := congrArg (fun n : ℕ => (n : ZMod 6)) (Nat.mod_add_div m 2)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
  calc
    _ = 3 * (m % 2 : ℕ) + (6 : ZMod 6) * (m / 2 : ℕ) := by norm_num
    _ = 3 * (m : ZMod 6) := by rw [← h]; ring

theorem conductorExponent_eq_valuation_digit (ε₁ ε₂ : Bool) (v₁ v₂ : ℕ) :
    conductorExponent (parity (v₁ + v₂)) ε₁ ε₂ =
      (bit ε₁ : ZMod 6) - (bit ε₂ : ZMod 6) + 3 * ((v₁ + v₂ : ℕ) : ZMod 6) := by
  rw [conductorExponent, three_mul_parity_cast]

theorem pair_digit (ε₁ ε₂ : Bool) (v₁ v₂ : ℕ) :
    (bit ε₁ + 3 * v₁ + 5 * (bit ε₂ + 3 * v₂)) % 6 =
      (conductorExponent (parity (v₁ + v₂)) ε₁ ε₂).val := by
  have hm := Nat.mod_lt (v₁ + v₂) (by decide : 0 < 2)
  cases ε₁ <;> cases ε₂ <;> by_cases h : (v₁ + v₂) % 2 = 1 <;>
    norm_num [conductorExponent, bit, parity, h] <;> omega

variable {F : Type*} [Field F] [Fintype F]

private theorem character_pair_reduction (χ : MulChar F ℂ) (h6 : χ ^ 6 = 1)
    (c d : ℕ) (x : F) :
    (χ ^ c) x * star ((χ ^ d) x) = (χ ^ ((c + 5 * d) % 6)) x := by
  have h5 : χ ^ 5 = χ⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using h6
  rw [MulChar.star_apply', ← MulChar.mul_apply]
  congr 1
  have hmod : χ ^ ((c + 5 * d) % 6) = χ ^ (c + 5 * d) := by
    conv_rhs => rw [← Nat.mod_add_div (c + 5 * d) 6, pow_add, pow_mul, h6,
      one_pow, mul_one]
  rw [hmod, pow_add, pow_mul, h5, inv_pow]

/-- The scalar expression arising from the expanded cube/squarefree source,
with the prime in the cube support. Scalar zeroth powers are handled before
applying the multiplicative-character identity. -/
theorem local_source_reduction_of_supported (χ : MulChar F ℂ) (h6 : χ ^ 6 = 1)
    (ε₁ ε₂ : Bool) (v₁ v₂ : ℕ)
    (hv : 0 < bit ε₁ + bit ε₂ + v₁ + v₂) (x : F) :
    χ x ^ (bit ε₁ + 3 * v₁) * star (χ x ^ (bit ε₂ + 3 * v₂)) =
      (χ ^ (conductorExponent (parity (v₁ + v₂)) ε₁ ε₂).val) x := by
  by_cases hx : x = 0
  · by_cases hv₁ : 0 < bit ε₁ + 3 * v₁
    · have he : bit ε₁ + 3 * v₁ ≠ 0 := by omega
      simp [hx, MulChar.map_zero, he]
    · have he : bit ε₂ + 3 * v₂ ≠ 0 := by omega
      simp [hx, MulChar.map_zero, he]
  · have hpow (n : ℕ) : (χ ^ n) x = χ x ^ n := by
      simpa using MulChar.pow_apply_coe χ n (Units.mk0 x hx)
    have h := character_pair_reduction χ h6 (bit ε₁ + 3 * v₁) (bit ε₂ + 3 * v₂) x
    rw [hpow (bit ε₁ + 3 * v₁), hpow (bit ε₂ + 3 * v₂), pair_digit] at h
    exact h

theorem local_source_reduction (χ : MulChar F ℂ) (h6 : χ ^ 6 = 1)
    (ε₁ ε₂ : Bool) (v₁ v₂ : ℕ) (hv : 0 < v₁ + v₂) (x : F) :
    χ x ^ (bit ε₁ + 3 * v₁) * star (χ x ^ (bit ε₂ + 3 * v₂)) =
      (χ ^ (conductorExponent (parity (v₁ + v₂)) ε₁ ε₂).val) x :=
  local_source_reduction_of_supported χ h6 ε₁ ε₂ v₁ v₂ (by omega) x

theorem local_source_split (χ : MulChar F ℂ) (h6 : χ ^ 6 = 1)
    (ε₁ ε₂ : Bool) (v₁ v₂ : ℕ) (hv : 0 < v₁ + v₂) (x : F) :
    χ x ^ (bit ε₁ + 3 * v₁) * star (χ x ^ (bit ε₂ + 3 * v₂)) =
      if conductorExponent (parity (v₁ + v₂)) ε₁ ε₂ = 0 then
        (if x = 0 then 0 else 1)
      else (χ ^ (conductorExponent (parity (v₁ + v₂)) ε₁ ε₂).val) x := by
  rw [local_source_reduction χ h6 ε₁ ε₂ v₁ v₂ hv x]
  by_cases hd : conductorExponent (parity (v₁ + v₂)) ε₁ ε₂ = 0
  · rw [hd]
    simp only [ZMod.val_zero, pow_zero, ite_true]
    by_cases hx : x = 0
    · simp [hx, MulChar.map_zero]
    · simpa only [hx, ite_false] using
        (MulChar.one_apply (R' := ℂ) (isUnit_iff_ne_zero.mpr hx))
  · simp only [hd, ite_false]

theorem local_conductor_principal_iff (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ε₁ ε₂ : Bool) (v₁ v₂ : ℕ) :
    χ ^ (conductorExponent (parity (v₁ + v₂)) ε₁ ε₂).val = 1 ↔
      conductorExponent (parity (v₁ + v₂)) ε₁ ε₂ = 0 := by
  constructor
  · intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hχ] at hd
    have hl := (conductorExponent (parity (v₁ + v₂)) ε₁ ε₂).val_lt
    apply (ZMod.val_eq_zero _).mp
    obtain ⟨k, hk⟩ := hd
    omega
  · intro h
    simp only [h, ZMod.val_zero, pow_zero]

/-- The local zero Fourier coefficient is zero exactly in the active
case. The principal local coefficient is retained as the number of units. -/
theorem local_zero_frequency (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ε₁ ε₂ : Bool) (v₁ v₂ : ℕ) (hv : 0 < v₁ + v₂) :
    (∑ x : F, χ x ^ (bit ε₁ + 3 * v₁) * star (χ x ^ (bit ε₂ + 3 * v₂))) =
      if conductorExponent (parity (v₁ + v₂)) ε₁ ε₂ = 0 then
        (Fintype.card Fˣ : ℂ) else 0 := by
  classical
  have h6 : χ ^ 6 = 1 := by
    rw [← hχ]
    exact pow_orderOf_eq_one χ
  simp_rw [local_source_reduction χ h6 ε₁ ε₂ v₁ v₂ hv]
  split_ifs with hd
  · simp only [hd, ZMod.val_zero, pow_zero]
    exact MulChar.sum_one_eq_card_units
  · apply MulChar.sum_eq_zero_of_ne_one
    exact fun h => hd ((local_conductor_principal_iff χ hχ ε₁ ε₂ v₁ v₂).mp h)

/-- The cube-support source is the active finite character product times
the exact complementary zero mask. No coprimality zero is discarded. -/
theorem finite_source_split {ι : Type*} {E : ι → Type*}
    [∀ i, Field (E i)] [∀ i, Fintype (E i)]
    (B : Finset ι) (χ : ∀ i, MulChar (E i) ℂ) (h6 : ∀ i, χ i ^ 6 = 1)
    (ε₁ ε₂ : ι → Bool) (v₁ v₂ : ι → ℕ)
    (hv : ∀ i ∈ B, 0 < bit (ε₁ i) + bit (ε₂ i) + v₁ i + v₂ i) (x : ∀ i, E i) :
    let t := fun i => conductorExponent (parity (v₁ i + v₂ i)) (ε₁ i) (ε₂ i)
    (∏ i ∈ B, χ i (x i) ^ (bit (ε₁ i) + 3 * v₁ i) *
      star (χ i (x i) ^ (bit (ε₂ i) + 3 * v₂ i))) =
    (if ∃ i ∈ B, t i = 0 ∧ x i = 0 then 0 else 1) *
      ∏ i ∈ B.filter (fun i => t i ≠ 0), (χ i ^ (t i).val) (x i) := by
  classical
  dsimp only
  let t := fun i => conductorExponent (parity (v₁ i + v₂ i)) (ε₁ i) (ε₂ i)
  let f := fun i => (χ i ^ (t i).val) (x i)
  have hlocal :
      (∏ i ∈ B, χ i (x i) ^ (bit (ε₁ i) + 3 * v₁ i) *
        star (χ i (x i) ^ (bit (ε₂ i) + 3 * v₂ i))) = ∏ i ∈ B, f i := by
    apply Finset.prod_congr rfl
    intro i hi
    exact local_source_reduction_of_supported (χ i) (h6 i) (ε₁ i) (ε₂ i)
      (v₁ i) (v₂ i) (hv i hi) (x i)
  have hprincipal : (∏ i ∈ B.filter (fun i => t i = 0), f i) =
      if ∃ i ∈ B, t i = 0 ∧ x i = 0 then 0 else 1 := by
    by_cases hz : ∃ i ∈ B, t i = 0 ∧ x i = 0
    · rw [if_pos hz]
      obtain ⟨i, hi, ht, hx⟩ := hz
      apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hi, ht⟩)
      simp only [f, hx, MulChar.map_zero]
    · rw [if_neg hz]
      apply Finset.prod_eq_one
      intro i hi
      obtain ⟨hi, ht⟩ := Finset.mem_filter.mp hi
      have hx : x i ≠ 0 := fun hx => hz ⟨i, hi, ht, hx⟩
      simp only [f, ht, ZMod.val_zero, pow_zero]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not B (fun i => t i = 0) f,
    hprincipal]

end HeckeSkeleton.Moments.MOM_INV_STEP.LocalDigits

end
