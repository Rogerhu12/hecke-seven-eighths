import HeckeGeneral.Analysis.IdealDirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Logarithmic weights on the genuine number-field ideal series

All indices are nonzero integral ideals of the actual ring of integers.
Polynomial powers of log norm are absorbed by an arbitrarily small power
of the norm. The resulting majorant converges by the proved ideal-counting
theorem; logarithmic summability is not an analytic input.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField Ideal
open scoped nonZeroDivisors Topology

/-- An explicit power bound for a logarithmic weight. -/
theorem logPower_mul_rpow_bound {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε)
    (k : ℕ) (σ : ℝ) :
    Real.log x ^ k * x ^ (-σ) ≤ (ε⁻¹) ^ k * x ^ (ε * (k : ℝ) - σ) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpow := pow_le_pow_left₀ (Real.log_nonneg hx)
    (Real.log_le_rpow_div hxpos.le hε) k
  calc
    Real.log x ^ k * x ^ (-σ) ≤ (x ^ ε / ε) ^ k * x ^ (-σ) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hxpos.le _)
    _ = (ε⁻¹) ^ k * x ^ (ε * (k : ℝ) - σ) := by
      rw [div_eq_mul_inv, mul_pow, ← Real.rpow_mul_natCast hxpos.le,
        sub_eq_add_neg, Real.rpow_add hxpos]
      ring

variable (K : Type*) [Field K] [NumberField K]

/-- The signed logarithmic term naturally occurring in repeated derivatives. -/
def idealLogTerm (a : NonzeroIdeal K → ℂ) (k : ℕ) (s : ℂ) (I : NonzeroIdeal K) : ℂ :=
  (-(Real.log (idealNorm K I) : ℂ)) ^ k * dirichletTerm (idealNorm K) a s I

/-- The total sum of the logarithmically weighted terms. Its convergence is proved below. -/
def idealLogSeries (a : NonzeroIdeal K → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑' I, idealLogTerm K a k s I

@[simp] theorem idealLogTerm_zero (a : NonzeroIdeal K → ℂ) (s : ℂ) (I : NonzeroIdeal K) :
    idealLogTerm K a 0 s I = dirichletTerm (idealNorm K) a s I := by
  simp [idealLogTerm]

@[simp] theorem idealLogSeries_zero (a : NonzeroIdeal K → ℂ) (s : ℂ) :
    idealLogSeries K a 0 s = idealDirichletSeries K a s := by
  simp only [idealLogSeries, idealLogTerm_zero, idealDirichletSeries, dirichletSeries]

theorem norm_idealLogTerm (a : NonzeroIdeal K → ℂ) (k : ℕ) (s : ℂ) (I : NonzeroIdeal K) :
    ‖idealLogTerm K a k s I‖ =
      Real.log (idealNorm K I) ^ k * (‖a I‖ * idealNorm K I ^ (-s.re)) := by
  rw [idealLogTerm, norm_mul, norm_pow, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (one_le_idealNorm K I)),
    norm_dirichletTerm (idealNorm K) a s I (idealNorm_pos K I)]

theorem norm_idealLogTerm_le (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (s : ℂ) (I : NonzeroIdeal K) :
    ‖idealLogTerm K a k s I‖ ≤
      Real.log (idealNorm K I) ^ k * idealNorm K I ^ (-s.re) := by
  rw [norm_idealLogTerm]
  have hb : ‖a I‖ * idealNorm K I ^ (-s.re) ≤ idealNorm K I ^ (-s.re) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (ha I) (Real.rpow_nonneg (idealNorm_pos K I).le _)
  exact mul_le_mul_of_nonneg_left
    hb
    (pow_nonneg (Real.log_nonneg (one_le_idealNorm K I)) k)

/-- Every logarithmic power is summable in the open convergence half-plane. -/
theorem summable_ideal_logPower_rpow (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : NonzeroIdeal K =>
      Real.log (idealNorm K I) ^ k * idealNorm K I ^ (-σ)) := by
  let τ : ℝ := (1 + σ) / 2
  let ε : ℝ := (σ - τ) / (k + 1)
  have hτ : 1 < τ := by dsimp [τ]; linarith
  have hgap : 0 < σ - τ := by dsimp [τ]; linarith
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hε : 0 < ε := div_pos hgap hk
  have hεk : ε * (k : ℝ) ≤ σ - τ := by
    have hcancel : ε * (k + 1) = σ - τ := div_mul_cancel₀ _ hk.ne'
    nlinarith
  have hmajor : Summable (fun I : NonzeroIdeal K =>
      (ε⁻¹) ^ k * idealNorm K I ^ (-τ)) :=
    (summable_nonzeroIdeal_norm_rpow K hτ).mul_left _
  apply Summable.of_nonneg_of_le
    (fun I => mul_nonneg (pow_nonneg (Real.log_nonneg (one_le_idealNorm K I)) k)
      (Real.rpow_nonneg (idealNorm_pos K I).le _)) ?_ hmajor
  intro I
  calc
    _ ≤ (ε⁻¹) ^ k * idealNorm K I ^ (ε * (k : ℝ) - σ) :=
      logPower_mul_rpow_bound (one_le_idealNorm K I) hε k σ
    _ ≤ (ε⁻¹) ^ k * idealNorm K I ^ (-τ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (one_le_idealNorm K I) (by linarith))
        (pow_nonneg (inv_nonneg.mpr hε.le) k)

theorem absolutelySummable_idealLogTerm (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I => ‖idealLogTerm K a k s I‖) :=
  Summable.of_nonneg_of_le (fun _I => norm_nonneg _)
    (norm_idealLogTerm_le K a ha k s) (summable_ideal_logPower_rpow K k hs)

theorem hasSum_idealLogTerm (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (idealLogTerm K a k s) (idealLogSeries K a k s) :=
  (absolutelySummable_idealLogTerm K a ha k hs).of_norm.hasSum

/-- A single summable bound works throughout every strictly smaller half-plane. -/
theorem norm_idealLogTerm_le_on_halfPlane (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re)
    (I : NonzeroIdeal K) :
    ‖idealLogTerm K a k s I‖ ≤
      Real.log (idealNorm K I) ^ k * idealNorm K I ^ (-σ) := by
  exact (norm_idealLogTerm_le K a ha k s I).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (one_le_idealNorm K I) (neg_le_neg hs))
      (pow_nonneg (Real.log_nonneg (one_le_idealNorm K I)) k))

end HeckeGeneral.Analysis
