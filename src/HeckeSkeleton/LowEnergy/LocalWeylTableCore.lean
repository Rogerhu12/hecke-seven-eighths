import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# The finite-field local Weyl table

The table is proved from literal finite sums, exact order six, and a primitive
additive character.  In particular its minimum-valuation bounds are not supplied
as analytic hypotheses.  The project adapter supplies these finite-field data
from its actual exterior residue field and actual theta additive character.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.LocalWeylTableCore

open scoped Classical BigOperators ComplexConjugate

variable {F : Type*} [Field F] [Fintype F]

theorem gauss_norm (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hs : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    have hr := congrArg Complex.re h
    simpa [Complex.mul_conj', pow_two] using hr
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card F by positivity)
  have hn := norm_nonneg (gaussSum χ ψ)
  have hr := Real.sqrt_nonneg (Fintype.card F : ℝ)
  nlinarith

theorem sum_units_eq (f : F → ℂ) (hf : f 0 = 0) :
    (∑ u : Fˣ, f u) = ∑ x : F, f x := by
  apply Finset.sum_bij_ne_zero (fun (u : Fˣ) _ _ => (u : F))
  · intro u _ _
    exact Finset.mem_univ _
  · intro u _ _ v _ _ h
    exact Units.ext h
  · intro x _ hx
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      exact hx hf
    exact ⟨Units.mk0 x hx0, Finset.mem_univ _, hx, rfl⟩
  · intro u _ _
    rfl

theorem char_unit_ne_zero (χ : MulChar F ℂ) (u : Fˣ) : χ u ≠ 0 :=
  ((Units.isUnit u).map χ.toMonoidHom).ne_zero

theorem char_zpow_unit (χ : MulChar F ℂ) (z : ℤ) (u : Fˣ) :
    (χ ^ z) u = χ u ^ z := by
  rw [MulChar.zpow_apply_coe]
  exact (χ.toMonoidHom.comp (Units.coeHom F)).map_zpow u z

theorem sum_unit_zpow_addChar (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (z : ℤ) :
    (∑ u : Fˣ, χ u ^ z * ψ u) = gaussSum (χ ^ z) ψ := by
  calc
    _ = ∑ u : Fˣ, (χ ^ z) u * ψ u := by
      apply Finset.sum_congr rfl
      intro u _
      rw [char_zpow_unit]
    _ = _ := by
      unfold gaussSum
      exact sum_units_eq (fun x : F => (χ ^ z) x * ψ x) (by
        rw [MulChar.map_zero, zero_mul])

theorem sum_unit_zpow (χ : MulChar F ℂ) (z : ℤ) (hz : χ ^ z ≠ 1) :
    (∑ u : Fˣ, χ u ^ z) = 0 := by
  calc
    _ = ∑ u : Fˣ, (χ ^ z) u := by
      apply Finset.sum_congr rfl
      intro u _
      rw [char_zpow_unit]
    _ = ∑ x : F, (χ ^ z) x := sum_units_eq _ (MulChar.map_zero _)
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hz

/-- Inversion is a bijection of the actual residue units. -/
theorem sum_unit_zpow_inverse_addChar (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (z : ℤ) :
    (∑ u : Fˣ, χ u ^ z * ψ ((u⁻¹ : Fˣ) : F)) = gaussSum (χ ^ (-z)) ψ := by
  calc
    _ = ∑ u : Fˣ, χ (u⁻¹ : Fˣ) ^ z * ψ (((u⁻¹)⁻¹ : Fˣ) : F) :=
      (Equiv.sum_comp (Equiv.inv Fˣ)
        (fun u : Fˣ => χ u ^ z * ψ ((u⁻¹ : Fˣ) : F))).symm
    _ = ∑ u : Fˣ, χ u ^ (-z) * ψ u := by
      apply Finset.sum_congr rfl
      intro u _
      have hi : χ (u⁻¹ : Fˣ) = (χ u)⁻¹ :=
        (χ.toMonoidHom.comp (Units.coeHom F)).map_inv u
      rw [hi]
      simp only [inv_inv, inv_zpow, zpow_neg]
    _ = _ := sum_unit_zpow_addChar χ ψ (-z)

variable (χ : MulChar F ℂ) (ψ : AddChar F ℂ)

def tau (j : Fin 6) : ℂ := ∑ u : Fˣ, χ u ^ (-(j.val : ℤ)) * ψ u

def mask (j : Fin 6) (u : Fˣ) : ℂ :=
  if j.val = 0 then -(Fintype.card F : ℂ)⁻¹
  else (tau χ ψ j)⁻¹ * χ u ^ (-(j.val : ℤ))

def spherical (γ : ℂ) (e : ℕ) : ℂ :=
  if e % 3 = 0 then (Fintype.card F : ℂ)⁻¹ ^ (e / 3)
  else if e % 3 = 1 then
    (Fintype.card F : ℂ)⁻¹ ^ (e / 3) *
      (Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹ * γ
  else 0

def localScalar (γ : ℂ) (j : Fin 6) (e : ℕ) : ℂ :=
  spherical (F := F) γ e *
    ∑ u : Fˣ, mask χ ψ j u * χ u ^ 4 *
      (if e = 0 then ψ ((u⁻¹ : Fˣ) : F) else 1)

theorem tau_eq_gauss (j : Fin 6) :
    tau χ ψ j = gaussSum (χ ^ (-(j.val : ℤ))) ψ :=
  sum_unit_zpow_addChar χ ψ _

theorem char_power_ne_one (hχ : orderOf χ = 6) (z : ℤ) (hz : ¬(6 : ℤ) ∣ z) :
    χ ^ z ≠ 1 := by
  intro h
  have hd := (orderOf_dvd_iff_zpow_eq_one).mpr h
  rw [hχ] at hd
  exact hz hd

theorem tau_norm (hχ : orderOf χ = 6) (hψ : ψ.IsPrimitive)
    (j : Fin 6) (hj : j.val ≠ 0) :
    ‖tau χ ψ j‖ = Real.sqrt (Fintype.card F : ℝ) := by
  rw [tau_eq_gauss]
  apply gauss_norm ψ hψ
  apply char_power_ne_one χ hχ
  rintro ⟨a, ha⟩
  have hlt := j.isLt
  omega

theorem mixed_power (j : Fin 6) (u : Fˣ) :
    χ u ^ (-(j.val : ℤ)) * χ u ^ 4 = χ u ^ ((4 : ℤ) - j.val) := by
  rw [← zpow_natCast (χ u) 4, ← zpow_add₀ (char_unit_ne_zero χ u)]
  congr 1
  omega

theorem localScalar_zero_nonzero_digit (γ : ℂ) (j : Fin 6) (hj : j.val ≠ 0) :
    localScalar χ ψ γ j 0 =
      (tau χ ψ j)⁻¹ * gaussSum (χ ^ ((j.val : ℤ) - 4)) ψ := by
  simp only [localScalar, spherical, Nat.zero_mod, Nat.zero_div, pow_zero,
    ite_true, one_mul, mask, if_neg hj]
  calc
    _ = (tau χ ψ j)⁻¹ *
        ∑ u : Fˣ, χ u ^ ((4 : ℤ) - j.val) * ψ ((u⁻¹ : Fˣ) : F) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [← mixed_power χ j u]
      ring
    _ = _ := by
      rw [sum_unit_zpow_inverse_addChar]
      rw [show -((4 : ℤ) - j.val) = (j.val : ℤ) - 4 by omega]

theorem localScalar_zero_zero_digit (γ : ℂ) :
    localScalar χ ψ γ ⟨0, by decide⟩ 0 =
      -(Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ (-4 : ℤ)) ψ := by
  simp only [localScalar, spherical, Nat.zero_mod, Nat.zero_div, pow_zero,
    ite_true, one_mul, mask]
  calc
    _ = -(Fintype.card F : ℂ)⁻¹ *
        ∑ u : Fˣ, χ u ^ (4 : ℤ) * ψ ((u⁻¹ : Fˣ) : F) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      norm_num [mul_assoc]
    _ = _ := by rw [sum_unit_zpow_inverse_addChar]

theorem positive_local_sum (hχ : orderOf χ = 6) (j : Fin 6) :
    (∑ u : Fˣ, mask χ ψ j u * χ u ^ 4) =
      if j.val = 4 then (Fintype.card Fˣ : ℂ) * (tau χ ψ j)⁻¹ else 0 := by
  by_cases hj0 : j.val = 0
  · have hj4 : j.val ≠ 4 := by omega
    rw [if_neg hj4]
    simp only [mask, if_pos hj0, ← Finset.mul_sum]
    have hs : (∑ u : Fˣ, χ (u : F) ^ (4 : ℕ)) = 0 := by
      calc
        _ = ∑ u : Fˣ, χ (u : F) ^ (4 : ℤ) := by
          apply Finset.sum_congr rfl
          intro u _
          norm_num
        _ = 0 := sum_unit_zpow χ (4 : ℤ)
          (char_power_ne_one χ hχ 4 (by norm_num))
    rw [hs, mul_zero]
  · simp only [mask, if_neg hj0]
    calc
      _ = (tau χ ψ j)⁻¹ * ∑ u : Fˣ, χ u ^ ((4 : ℤ) - j.val) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        rw [← mixed_power χ j u]
        ring
      _ = _ := by
        by_cases hj4 : j.val = 4
        · simp [hj4, mul_comm]
        · rw [if_neg hj4, sum_unit_zpow, mul_zero]
          apply char_power_ne_one χ hχ
          rintro ⟨a, ha⟩
          have hlt := j.isLt
          omega

theorem localScalar_positive (hχ : orderOf χ = 6) (γ : ℂ)
    (j : Fin 6) (e : ℕ) (he : 0 < e) :
    localScalar χ ψ γ j e =
      spherical (F := F) γ e *
        (if j.val = 4 then (Fintype.card Fˣ : ℂ) * (tau χ ψ j)⁻¹ else 0) := by
  simp only [localScalar, if_neg (Nat.ne_of_gt he), mul_one]
  rw [positive_local_sum χ ψ hχ]

theorem localScalar_positive_eq_zero (hχ : orderOf χ = 6) (γ : ℂ)
    (j : Fin 6) (e : ℕ) (he : 0 < e) (hj : j.val ≠ 4) :
    localScalar χ ψ γ j e = 0 := by
  rw [localScalar_positive χ ψ hχ γ j e he, if_neg hj, mul_zero]

theorem localScalar_zero_norm (hχ : orderOf χ = 6) (hψ : ψ.IsPrimitive)
    (γ : ℂ) (j : Fin 6) :
    ‖localScalar χ ψ γ j 0‖ =
      if j.val = 0 ∨ j.val = 4 then (Real.sqrt (Fintype.card F : ℝ))⁻¹ else 1 := by
  have hq : (0 : ℝ) < Fintype.card F := by positivity
  have hs : 0 < Real.sqrt (Fintype.card F : ℝ) := Real.sqrt_pos.mpr hq
  have hs2 := Real.sq_sqrt hq.le
  by_cases hj0 : j.val = 0
  · have hj : j = ⟨0, by decide⟩ := Fin.ext hj0
    subst j
    rw [localScalar_zero_zero_digit χ ψ γ, norm_mul, norm_neg, norm_inv]
    rw [gauss_norm ψ hψ _ (char_power_ne_one χ hχ (-4) (by norm_num))]
    simp only [Complex.norm_natCast]
    change (Fintype.card F : ℝ)⁻¹ * Real.sqrt (Fintype.card F : ℝ) =
      (Real.sqrt (Fintype.card F : ℝ))⁻¹
    have hq0 : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt hq
    field_simp [hq0, ne_of_gt hs]
    nlinarith
  · rw [localScalar_zero_nonzero_digit χ ψ γ j hj0, norm_mul, norm_inv,
      tau_norm χ ψ hχ hψ j hj0]
    by_cases hj4 : j.val = 4
    · have hψne : ψ ≠ 1 := by simpa using hψ (one_ne_zero : (1 : F) ≠ 0)
      rw [show (j.val : ℤ) - 4 = 0 by omega, zpow_zero, gaussSum_one_left hψne]
      simp [hj4]
    · rw [gauss_norm ψ hψ _ (char_power_ne_one χ hχ _ (by
          rintro ⟨a, ha⟩
          have hlt := j.isLt
          omega))]
      simp [hj0, hj4, ne_of_gt hs]

theorem card_units_le : (Fintype.card Fˣ : ℝ) ≤ Fintype.card F := by
  exact_mod_cast (Nat.le.intro (Fintype.card_eq_card_units_add_one (α := F)).symm)

theorem localScalar_one_norm_le (hχ : orderOf χ = 6) (hψ : ψ.IsPrimitive)
    (γ : ℂ) (hγ : ‖γ‖ = 1) (j : Fin 6) : ‖localScalar χ ψ γ j 1‖ ≤ 1 := by
  by_cases hj4 : j.val = 4
  · have hj0 : j.val ≠ 0 := by omega
    rw [localScalar_positive χ ψ hχ γ j 1 (by decide), if_pos hj4]
    norm_num [spherical, norm_mul, norm_inv, hγ, tau_norm χ ψ hχ hψ j hj0,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hq : (0 : ℝ) < Fintype.card F := by positivity
    have hs : 0 < Real.sqrt (Fintype.card F : ℝ) := Real.sqrt_pos.mpr hq
    have hs2 := Real.sq_sqrt hq.le
    have hcard := card_units_le (F := F)
    field_simp [ne_of_gt hs]
    nlinarith
  · rw [localScalar_positive_eq_zero χ ψ hχ γ j 1 (by decide) hj4, norm_zero]
    norm_num

theorem localScalar_three_norm_le (hχ : orderOf χ = 6) (hψ : ψ.IsPrimitive)
    (γ : ℂ) (j : Fin 6) :
    ‖localScalar χ ψ γ j 3‖ ≤ (Real.sqrt (Fintype.card F : ℝ))⁻¹ := by
  by_cases hj4 : j.val = 4
  · have hj0 : j.val ≠ 0 := by omega
    rw [localScalar_positive χ ψ hχ γ j 3 (by decide), if_pos hj4]
    norm_num [spherical, norm_mul, norm_inv, tau_norm χ ψ hχ hψ j hj0]
    have hq : (0 : ℝ) < Fintype.card F := by positivity
    have hs : 0 < Real.sqrt (Fintype.card F : ℝ) := Real.sqrt_pos.mpr hq
    have hcard := card_units_le (F := F)
    have hratio : (Fintype.card F : ℝ)⁻¹ * (Fintype.card Fˣ : ℝ) ≤ 1 :=
      (inv_mul_le_iff₀ hq).mpr (by simpa only [mul_one] using hcard)
    simpa only [one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr hs.le)
  · rw [localScalar_positive_eq_zero χ ψ hχ γ j 3 (by decide) hj4, norm_zero]
    positivity

#print axioms localScalar_zero_norm
#print axioms localScalar_positive_eq_zero
#print axioms localScalar_one_norm_le
#print axioms localScalar_three_norm_le

end HeckeSkeleton.LowEnergy.LocalWeylTableCore
