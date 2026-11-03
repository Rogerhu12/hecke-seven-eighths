import Mathlib.Analysis.Complex.Basic
import HeckeSkeleton.LowHybrid.CommonTactics

/-!
# Zero-preserving sextic phase identities

These identities use a monoid-homomorphism-valued symbol, reciprocity, and
the sixth-power collision mask as explicit hypotheses.  They are the algebraic
interface needed to transport the frozen-valuation results to the actual
`idealSymbol`; the concrete arithmetic adapter is not supplied here.
-/

namespace HeckeSkeleton.LowFrozenCube

open scoped Classical

section Scalar

/-- On sixth roots of unity extended by zero, the inverse square is the fourth
power.  The zero case is retained. -/
theorem inverse_square_eq_fourth (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1) :
    (z⁻¹) ^ 2 = z ^ 4 := by
  rcases hz with hz | hz
  · simp [hz]
  · have hne : z ≠ 0 := by
      intro h
      simp [h] at hz
    apply mul_left_cancel₀ (pow_ne_zero 2 hne)
    calc
      z ^ 2 * (z⁻¹) ^ 2 = (z * z⁻¹) ^ 2 := by ring
      _ = 1 := by simp [hne]
      _ = z ^ 6 := hz.symm
      _ = z ^ 2 * z ^ 4 := by ring

/-- The analogous identity for the inverse fourth power. -/
theorem inverse_fourth_eq_square (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1) :
    (z⁻¹) ^ 4 = z ^ 2 := by
  rcases hz with hz | hz
  · simp [hz]
  · have hne : z ≠ 0 := by
      intro h
      simp [h] at hz
    apply mul_left_cancel₀ (pow_ne_zero 4 hne)
    calc
      z ^ 4 * (z⁻¹) ^ 4 = (z * z⁻¹) ^ 4 := by ring
      _ = 1 := by simp [hne]
      _ = z ^ 6 := hz.symm
      _ = z ^ 4 * z ^ 2 := by ring

/-- The signed-exponent form used by the cubic sieve. -/
theorem zpow_neg_two_eq_fourth (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1) :
    z ^ (-2 : ℤ) = z ^ 4 := by
  simpa only [zpow_neg, zpow_ofNat, inv_pow] using inverse_square_eq_fourth z hz

theorem zpow_neg_four_eq_square (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1) :
    z ^ (-4 : ℤ) = z ^ 2 := by
  simpa only [zpow_neg, zpow_ofNat, inv_pow] using inverse_fourth_eq_square z hz

end Scalar

section Symbol

variable {A : Type*} [CommMonoid A]
variable (χ : A → A →* ℂ) (Cop : A → A → Prop)

/-- The sixth-power mask already implies the zero-or-root-of-unity condition. -/
theorem sextic_symbol_zero_or_root
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0) (a b : A) :
    χ a b = 0 ∨ (χ a b) ^ 6 = 1 := by
  by_cases hab : Cop a b
  · right
    simpa [hab] using h6 a b
  · left
    have hz : (χ a b) ^ 6 = 0 := by simpa [hab] using h6 a b
    exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hz

theorem symbol_zpow_neg_two
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0) (a b : A) :
    (χ a b) ^ (-2 : ℤ) = (χ a b) ^ 4 :=
  zpow_neg_two_eq_fourth _ (sextic_symbol_zero_or_root χ Cop h6 a b)

theorem symbol_zpow_neg_four
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0) (a b : A) :
    (χ a b) ^ (-4 : ℤ) = (χ a b) ^ 2 :=
  zpow_neg_four_eq_square _ (sextic_symbol_zero_or_root χ Cop h6 a b)

/-- The row/active-mark mixed phase is exactly the collision mask. -/
theorem row_mark_phase (hrec : ∀ a b, χ a b = χ b a)
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0) (d P : A) :
    (χ d P) ^ 4 * (χ P d) ^ 2 = if Cop d P then (1 : ℂ) else 0 := by
  rw [hrec P d]
  calc
    (χ d P) ^ 4 * (χ d P) ^ 2 = (χ d P) ^ 6 := by ring
    _ = _ := h6 d P

/-- Row/column reciprocity gives the quadratic phase, including common-prime zeros. -/
theorem row_column_phase (hrec : ∀ a b, χ a b = χ b a) (d c : A) :
    χ d c * (χ c d) ^ 2 = (χ d c) ^ 3 := by
  rw [hrec c d]
  ring

/-- Mark/column reciprocity gives the inverse cubic phase, written as a fourth power. -/
theorem mark_column_phase (hrec : ∀ a b, χ a b = χ b a) (P c : A) :
    (χ P c) ^ 2 * (χ c P) ^ 2 = (χ P c) ^ 4 := by
  rw [hrec c P]
  ring

/-- A frozen cube has no remaining phase against a coprime mark or column. -/
theorem frozen_cube_square_phase
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (P x : A) (hPx : Cop P x) :
    (χ P (x ^ 3)) ^ 2 = 1 := by
  rw [map_pow]
  calc
    ((χ P x) ^ 3) ^ 2 = (χ P x) ^ 6 := by ring
    _ = 1 := by simpa [hPx] using h6 P x

/-- The collision mask is unchanged by adjoining the frozen supported part. -/
theorem full_cube_symbol_mask
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (P x n : A) (hPx : Cop P x) :
    (if Cop P (x * n) then (1 : ℂ) else 0) =
      if Cop P n then (1 : ℂ) else 0 := by
  rw [← h6 P (x * n), map_mul, mul_pow, h6 P x, if_pos hPx, one_mul, h6 P n]

/-- The only surviving frozen-cube row phase joins the complete cube variable. -/
theorem frozen_cube_row_phase (d c x n : A) :
    (χ d x) ^ 3 * (χ d (c * n)) ^ 3 =
      (χ d (c * (x * n))) ^ 3 := by
  simp only [map_mul]
  ring

/-- Exact pointwise transport into the quadratic--cubic hybrid summand. -/
theorem frozen_cube_hybrid_summand
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (d P c x n : A) (hPx : Cop P x) :
    ((χ d x) ^ 3 * (χ d (c * n)) ^ 3) * (χ P c) ^ 4 *
        (if Cop P n then (1 : ℂ) else 0) =
      (χ d (c * (x * n))) ^ 3 * (χ P c) ^ 4 *
        (if Cop P (x * n) then (1 : ℂ) else 0) := by
  rw [frozen_cube_row_phase χ, full_cube_symbol_mask χ Cop h6 P x n hPx]

end Symbol

end HeckeSkeleton.LowFrozenCube
