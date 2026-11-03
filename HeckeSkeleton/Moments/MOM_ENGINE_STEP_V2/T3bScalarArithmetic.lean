import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The numerical two-stage scalar cancellation

The complete first and second frozen ideals compensate the two actual
scale products. The first lower scale bound is used before any positive
tilt. Since the actual pool norm is between one and the complete first
frozen norm, its tilt is paid together with the first scale tilt.
The estimate uses the full permitted range `0 ≤ δ ≤ 1/2`.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

/-- The central, untilted part preserves one full inverse second norm. -/
theorem twoStage_scalar_core_sq_le
    (Z A B S₁ S₂ N₁ N₂ a b C₁ C₂ : ℝ)
    (hZ : 0 < Z) (hB : 1 ≤ B) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (ha : a ^ 2 ≤ C₁ / N₁) (hb : b ^ 2 ≤ C₂ / N₂)
    (hlower : Z ^ A ≤ B * (S₁ * N₁)) (hsecond : S₂ * N₂ ≤ B * S₁) :
    ((a * S₁ ^ (-1 : ℝ) * b) * Real.sqrt S₂) ^ 2 ≤
      C₁ * C₂ * B ^ 2 / (Z ^ A * N₂ ^ 2) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hprod : a ^ 2 * b ^ 2 ≤ C₁ * C₂ / (N₁ * N₂) := by
    calc
      _ ≤ (C₁ / N₁) * (C₂ / N₂) :=
        mul_le_mul ha hb (sq_nonneg _) (div_nonneg hC₁ hN₁.le)
      _ = _ := by ring
  have hscale : S₂ ≤ B * S₁ / N₂ := (le_div_iff₀ hN₂).mpr hsecond
  have hinverse : B / (S₁ * N₁) ≤ B ^ 2 / Z ^ A := by
    apply (div_le_div_iff₀ (mul_pos hS₁ hN₁) (Real.rpow_pos_of_pos hZ A)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlower hB0]
  calc
    _ = a ^ 2 * b ^ 2 * S₂ / S₁ ^ 2 := by
      simp only [mul_pow, Real.rpow_neg_one, inv_pow, Real.sq_sqrt hS₂.le]
      ring
    _ ≤ (C₁ * C₂ / (N₁ * N₂) * (B * S₁ / N₂)) / S₁ ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul hprod hscale hS₂.le
          (div_nonneg (mul_nonneg hC₁ hC₂) (mul_nonneg hN₁.le hN₂.le)))
        (sq_nonneg _)
    _ = (C₁ * C₂ / N₂ ^ 2) * (B / (S₁ * N₁)) := by
      field_simp [hS₁.ne', hN₁.ne', hN₂.ne']
      <;> ring
    _ ≤ (C₁ * C₂ / N₂ ^ 2) * (B ^ 2 / Z ^ A) :=
      mul_le_mul_of_nonneg_left hinverse
        (div_nonneg (mul_nonneg hC₁ hC₂) (sq_nonneg _))
    _ = _ := by ring

theorem twoStage_scalar_core_le
    (Z A B S₁ S₂ N₁ N₂ a b C₁ C₂ : ℝ)
    (hZ : 0 < Z) (hB : 1 ≤ B) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (ha : a ^ 2 ≤ C₁ / N₁) (hb : b ^ 2 ≤ C₂ / N₂)
    (hlower : Z ^ A ≤ B * (S₁ * N₁)) (hsecond : S₂ * N₂ ≤ B * S₁) :
    (a * S₁ ^ (-1 : ℝ) * b) * Real.sqrt S₂ ≤
      Real.sqrt (C₁ * C₂) * B * Z ^ (-A / 2) / N₂ := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    _ ≤ C₁ * C₂ * B ^ 2 / (Z ^ A * N₂ ^ 2) :=
      twoStage_scalar_core_sq_le Z A B S₁ S₂ N₁ N₂ a b C₁ C₂
        hZ hB hS₁ hS₂ hN₁ hN₂ hC₁ hC₂ ha hb hlower hsecond
    _ = _ := by
      simp only [div_pow, mul_pow, Real.sq_sqrt (mul_nonneg hC₁ hC₂)]
      rw [← Real.rpow_mul_natCast hZ.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (-A / 2) * (2 : ℝ) = -A by ring, Real.rpow_neg hZ.le]
      ring

/-- The actual pool power fits inside the complete first frozen norm.
No assumption that the first remaining scale is at least one is used. -/
theorem twoStage_tilt_le
    (Z A B S₁ N₁ Q δ u : ℝ)
    (hZ : 0 < Z) (hB : 1 ≤ B) (hS₁ : 0 < S₁) (hN₁ : 0 < N₁)
    (hQ : 1 ≤ Q) (hQN₁ : Q ≤ N₁) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hu : u ≤ Q ^ δ) (hupper : S₁ * N₁ ≤ B * Z ^ A) :
    u * S₁ ^ (2 * δ) ≤ B * Z ^ (2 * δ * A) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hN₁one : 1 ≤ N₁ := hQ.trans hQN₁
  have hu' : u ≤ N₁ ^ (2 * δ) :=
    hu.trans ((Real.rpow_le_rpow hQ0 hQN₁ hδ).trans
      (Real.rpow_le_rpow_of_exponent_le hN₁one (by linarith)))
  have hBtilt : B ^ (2 * δ) ≤ B := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hB (show 2 * δ ≤ 1 by linarith))
  calc
    _ ≤ N₁ ^ (2 * δ) * S₁ ^ (2 * δ) :=
      mul_le_mul_of_nonneg_right hu' (Real.rpow_nonneg hS₁.le _)
    _ = (S₁ * N₁) ^ (2 * δ) := by
      rw [Real.mul_rpow hS₁.le hN₁.le]
      ring
    _ ≤ (B * Z ^ A) ^ (2 * δ) :=
      Real.rpow_le_rpow (mul_nonneg hS₁.le hN₁.le) hupper (by linarith)
    _ = B ^ (2 * δ) * Z ^ (2 * δ * A) := by
      rw [Real.mul_rpow hB0.le (Real.rpow_nonneg hZ.le _), ← Real.rpow_mul hZ.le]
      congr 1
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hBtilt (Real.rpow_nonneg hZ.le _)

/-- The complete original two-stage scalar bound. Both squared frozen
norm estimates and all three scale inequalities retain their real values. -/
theorem twoStage_scalar_sqrt_le
    (Z A B S₁ S₂ N₁ N₂ Q δ a b u C₁ C₂ : ℝ)
    (hZ : 0 < Z) (hB : 1 ≤ B) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hQ : 1 ≤ Q) (hQN₁ : Q ≤ N₁)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hu0 : 0 ≤ u) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (ha : a ^ 2 ≤ C₁ / N₁) (hb : b ^ 2 ≤ C₂ / N₂) (hu : u ≤ Q ^ δ)
    (hlower : Z ^ A ≤ B * (S₁ * N₁)) (hupper : S₁ * N₁ ≤ B * Z ^ A)
    (hsecond : S₂ * N₂ ≤ B * S₁) :
    (a * u * S₁ ^ (-1 + 2 * δ) * b) * Real.sqrt S₂ ≤
      Real.sqrt (C₁ * C₂) * B ^ 2 * Z ^ (-A / 2 + 2 * δ * A) / N₂ := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hcore := twoStage_scalar_core_le Z A B S₁ S₂ N₁ N₂ a b C₁ C₂
    hZ hB hS₁ hS₂ hN₁ hN₂ ha0 hb0 hC₁ hC₂ ha hb hlower hsecond
  have htilt := twoStage_tilt_le Z A B S₁ N₁ Q δ u
    hZ hB hS₁ hN₁ hQ hQN₁ hδ hδhalf hu hupper
  calc
    _ = ((a * S₁ ^ (-1 : ℝ) * b) * Real.sqrt S₂) * (u * S₁ ^ (2 * δ)) := by
      rw [Real.rpow_add hS₁]
      ring
    _ ≤ (Real.sqrt (C₁ * C₂) * B * Z ^ (-A / 2) / N₂) *
        (B * Z ^ (2 * δ * A)) :=
      mul_le_mul hcore htilt
        (mul_nonneg hu0 (Real.rpow_nonneg hS₁.le _)) (by positivity)
    _ = _ := by
      rw [Real.rpow_add hZ]
      ring

/-- The nominal width and row factors cancel at the original first
selected allowance, before its unchanged physical outer weight is paid. -/
theorem nominal_scalar_exponent
    (A c w q R E Krow g g₂ t₂ V b₂ p₂ wo boundary ell δ : ℝ) :
    (-A - 2 * b₂ + 4 * δ * A) - (A - c - w - b₂) +
        (Krow + g) + (g₂ - t₂) +
        (2 * (A - c - w) - Krow - g - g₂ - V +
          (q + R + E + wo + t₂ + V) + b₂ - p₂ + w + boundary + ell) =
      -c + q + R + E + wo - p₂ + boundary + ell + 4 * δ * A := by
  ring

theorem nominal_scalar_selected_allowance
    (A c w q R E Krow g g₂ t₂ V b₂ p₂ wo boundary ell δ : ℝ) :
    (-A - 2 * b₂ + 4 * δ * A) - (A - c - w - b₂) +
        (Krow + g) + (g₂ - t₂) +
        (2 * (A - c - w) - Krow - g - g₂ - V +
          (q + R + E + wo + t₂ + V) + b₂ - p₂ + w + boundary + ell) =
      (A + q + R + E - c + boundary) - A + wo + ell - p₂ + 4 * δ * A := by
  ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.twoStage_scalar_sqrt_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.nominal_scalar_selected_allowance
