import ThetaGlobal.ReflectedAbsoluteCore

/-!
# Uniform bounds for finite-digit Weyl coefficients

This Mathlib-only module isolates the exact elementary algebra used at an
exterior prime.  Digit weights can be arbitrary fixed complex numbers; their
norms are summed explicitly.  No local Weyl identity is assumed or proved.
The result bounds the finite-sum expression that defines `localWeylScalar`
in the project, uniformly in its nonnegative valuation index.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedLocalBounds

open ThetaGlobal.ReflectedAbsolute
open scoped BigOperators

theorem norm_real_inv_le_one {r : ℝ} (hr : 1 ≤ r) : ‖(r : ℂ)⁻¹‖ ≤ 1 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  exact (inv_le_one₀ hr0).mpr hr

theorem norm_real_sqrt_inv_le_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(Real.sqrt r : ℂ)⁻¹‖ ≤ 1 := by
  apply norm_real_inv_le_one
  exact (Real.le_sqrt (by norm_num) (le_trans zero_le_one hr)).mpr (by simpa using hr)

def sphericalCoefficient (q : ℝ) (γ : ℂ) (e : ℕ) : ℂ :=
  if e % 3 = 0 then (q : ℂ)⁻¹ ^ (e / 3)
  else if e % 3 = 1 then (q : ℂ)⁻¹ ^ (e / 3) * (Real.sqrt q : ℂ)⁻¹ * γ
  else 0

theorem norm_sphericalCoefficient_le_one {q : ℝ} (hq : 1 ≤ q)
    {γ : ℂ} (hγ : ‖γ‖ = 1) (e : ℕ) : ‖sphericalCoefficient q γ e‖ ≤ 1 := by
  have hp := pow_le_one₀ (n := e / 3) (norm_nonneg ((q : ℂ)⁻¹))
    (norm_real_inv_le_one hq)
  have hs := norm_real_sqrt_inv_le_one hq
  unfold sphericalCoefficient
  split_ifs
  · simpa only [norm_pow] using hp
  · rw [norm_mul, norm_mul, norm_pow, hγ, mul_one]
    exact (mul_le_mul hp hs (norm_nonneg _) zero_le_one).trans (by norm_num)
  · simp

def finiteWeylCoefficient {Ω : Type*} [Fintype Ω]
    (q : ℝ) (γ : ℂ) (digit character phase : Ω → ℂ) (e : ℕ) : ℂ :=
  sphericalCoefficient q γ e *
    ∑ x, digit x * character x ^ 4 * (if e = 0 then phase x else 1)

def finiteWeylBound {Ω : Type*} [Fintype Ω] (digit phase : Ω → ℂ) : ℝ :=
  ∑ x, ‖digit x‖ * (1 + ‖phase x‖)

theorem finiteWeylBound_nonneg {Ω : Type*} [Fintype Ω] (digit phase : Ω → ℂ) :
    0 ≤ finiteWeylBound digit phase := by
  unfold finiteWeylBound
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (norm_nonneg _) (by positivity))

theorem norm_finiteWeylCoefficient_le {Ω : Type*} [Fintype Ω]
    {q : ℝ} (hq : 1 ≤ q) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (digit character phase : Ω → ℂ) (hcharacter : ∀ x, ZeroOrUnitNorm (character x))
    (e : ℕ) :
    ‖finiteWeylCoefficient q γ digit character phase e‖ ≤ finiteWeylBound digit phase := by
  let g : Ω → ℂ := fun x => digit x * character x ^ 4 * (if e = 0 then phase x else 1)
  have hg (x : Ω) : ‖g x‖ ≤ ‖digit x‖ * (1 + ‖phase x‖) := by
    have hchar := ((hcharacter x).pow 4).norm_le
    have hphase : ‖(if e = 0 then phase x else 1)‖ ≤ 1 + ‖phase x‖ := by
      split_ifs
      · linarith [norm_nonneg (phase x)]
      · rw [norm_one]
        exact le_add_of_nonneg_right (norm_nonneg (phase x))
    dsimp only [g]
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (‖digit x‖ * 1) * (1 + ‖phase x‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hchar (norm_nonneg _)) hphase
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  change ‖sphericalCoefficient q γ e * ∑ x, g x‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖∑ x, g x‖ := mul_le_mul_of_nonneg_right
      (norm_sphericalCoefficient_le_one hq hγ e) (norm_nonneg _)
    _ = ‖∑ x, g x‖ := one_mul _
    _ ≤ ∑ x, ‖g x‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun x _ => hg x)

theorem norm_one_sub_real_inverse_le_one {q : ℝ} (hq : 1 ≤ q) :
    ‖1 - (q : ℂ)⁻¹‖ ≤ 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hi : q⁻¹ ≤ 1 := (inv_le_one₀ hq0).mpr hq
  have hid : 1 - (q : ℂ)⁻¹ = ((1 - q⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hid, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hi)]
  exact sub_le_self _ (inv_nonneg.mpr hq0.le)

end ThetaGlobal.ReflectedLocalBounds
