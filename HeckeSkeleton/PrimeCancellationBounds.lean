import PrimeCancellationUniformity
import Mathlib.Tactic.GCongr

/-!
# Uniform numerical budgets for the prime-slot wiring

The contour consumes half of the fixed exponent margin.  A fixed logarithmic
power consumes the other half, independently of the later height parameter.
The number of slots is bounded before all scales and profiles are selected.
-/

noncomputable section
open scoped BigOperators

namespace HeckeSkeleton.PrimeCancellationBounds

/-- The explicit numerical expression used by the analytic core. Keeping
this scalar definition here lets the budget lemmas compile independently of
the complex-analysis import closure; it is definitionally equal to the
core's `PrimeCancellation.PairedProfiles.uniformConstant`. -/
def numericPrimeConstant (δ C degreeBound H : ℝ) : ℝ :=
  24 * C * H / δ ^ 2 + degreeBound * (1 + Real.sqrt 2) +
    2 * degreeBound * Real.exp 4

theorem numericPrimeConstant_mul_le (δ C d H f : ℝ)
    (hd : 0 ≤ d) (hf : 1 ≤ f) :
    numericPrimeConstant δ C d (H * f) ≤ numericPrimeConstant δ C d H * f := by
  have ht : 0 ≤ d * (1 + Real.sqrt 2) + 2 * d * Real.exp 4 := by positivity
  have hb := mul_le_mul_of_nonneg_left hf ht
  calc
    numericPrimeConstant δ C d (H * f) =
        (24 * C * H / δ ^ 2) * f + (d * (1 + Real.sqrt 2) + 2 * d * Real.exp 4) := by
      unfold numericPrimeConstant
      ring
    _ ≤ (24 * C * H / δ ^ 2) * f +
        (d * (1 + Real.sqrt 2) + 2 * d * Real.exp 4) * f := by linarith
    _ = numericPrimeConstant δ C d H * f := by unfold numericPrimeConstant; ring

theorem logarithmic_mask_budget (D X : ℝ) (hD : 0 ≤ D) (hX : 1 ≤ X) :
    (D + Real.log X) / Real.log 2 ≤
      ((D + 1) / Real.log 2) * (1 + Real.log X) := by
  have hlog := Real.log_nonneg hX
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  apply (div_le_iff₀ htwo).mpr
  have hid : ((D + 1) / Real.log 2) * (1 + Real.log X) * Real.log 2 =
      (D + 1) * (1 + Real.log X) := by field_simp
  rw [hid]
  nlinarith [mul_nonneg hD hlog]

theorem conductor_height_budget (C D A Q X T q : ℝ) (k : ℕ)
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hX : 1 ≤ X) (hT : 1 ≤ T) (hq : 0 ≤ q)
    (hQ : Real.log Q ≤ D * (1 + Real.log X) * (1 + T) ^ q) :
    1 + Real.log C + (5 / 8 : ℝ) * Real.log Q + A + 3 * (k : ℝ) ≤
      (1 + Real.log C + (5 / 8 : ℝ) * D + A + 3 * (k : ℝ)) *
        ((1 + Real.log X) * (1 + T) ^ q) := by
  have hbase : 0 ≤ 1 + Real.log C + A + 3 * (k : ℝ) := by
    have := Real.log_nonneg hC
    positivity
  have hf : 1 ≤ (1 + Real.log X) * (1 + T) ^ q :=
    one_le_mul_of_one_le_of_one_le (by linarith [Real.log_nonneg hX])
      (Real.one_le_rpow (by linarith) hq)
  have hfixed := mul_le_mul_of_nonneg_left hf hbase
  nlinarith

theorem profile_budget (δ C d H B W X T q a S : ℝ)
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hW : 0 ≤ W) (hX : 1 ≤ X) (hT : 1 ≤ T) (hq : 0 ≤ q)
    (hS : 0 ≤ S) (hSb : S ≤ W * (1 + T) ^ a) :
    (numericPrimeConstant δ C d (H * ((1 + Real.log X) * (1 + T) ^ q)) +
        B * ((1 + Real.log X) * (1 + T) ^ q)) * S ≤
      max 1 ((numericPrimeConstant δ C d H + B) * W) *
        (1 + Real.log X) * (1 + T) ^ (q + a) := by
  let f := (1 + Real.log X) * (1 + T) ^ q
  have hf : 1 ≤ f := one_le_mul_of_one_le_of_one_le (by linarith [Real.log_nonneg hX])
    (Real.one_le_rpow (by linarith) hq)
  have hconst : 0 ≤ numericPrimeConstant δ C d H + B :=
    by unfold numericPrimeConstant; positivity
  have hcoef : numericPrimeConstant δ C d (H * f) + B * f ≤
      (numericPrimeConstant δ C d H + B) * f := by
    simpa only [add_mul] using add_le_add
      (numericPrimeConstant_mul_le δ C d H f hd hf) (le_refl (B * f))
  calc
    _ ≤ ((numericPrimeConstant δ C d H + B) * f) * (W * (1 + T) ^ a) :=
      mul_le_mul hcoef hSb hS (mul_nonneg hconst (zero_le_one.trans hf))
    _ = ((numericPrimeConstant δ C d H + B) * W) *
        (1 + Real.log X) * (1 + T) ^ (q + a) := by
      rw [Real.rpow_add (by linarith : 0 < 1 + T)]
      dsimp only [f]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith : 0 ≤ 1 + T) _)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _)
        (by linarith [Real.log_nonneg hX])

/-- A common per-slot constant is raised only to the fixed slot ceiling. -/
theorem finite_slot_budget (n J : ℕ) (C X T a : ℝ)
    (hn : n ≤ J) (hC : 1 ≤ C) (hX : 1 ≤ X) (hT : 1 ≤ T) (ha : 0 ≤ a) :
    ((C * (1 + Real.log X) * (1 + T) ^ a) ^ 2) ^ n ≤
      C ^ (2 * J) * (1 + Real.log X) ^ (2 * J) *
        (1 + T) ^ (a * (2 * J : ℕ)) := by
  have hx : 1 ≤ 1 + Real.log X := by linarith [Real.log_nonneg hX]
  have ht : 1 ≤ (1 + T) ^ a := Real.one_le_rpow (by linarith) ha
  have hc : 1 ≤ C * (1 + Real.log X) * (1 + T) ^ a :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hx) ht
  calc
    ((C * (1 + Real.log X) * (1 + T) ^ a) ^ 2) ^ n ≤
        ((C * (1 + Real.log X) * (1 + T) ^ a) ^ 2) ^ J :=
      pow_le_pow_right₀ (one_le_pow₀ hc) hn
    _ = _ := by
      rw [← pow_mul, mul_pow, mul_pow, ← Real.rpow_mul_natCast (by linarith : 0 ≤ 1 + T)]

/-- The logarithmic loss is absorbed in the base itself. No comparison
between a shell base and the external parameter is needed. -/
theorem absorb_slot_logarithms (J : ℕ) (Crows C X T a κ z lam : ℝ)
    (hrows : 0 ≤ Crows) (hC : 0 ≤ C) (hX : 1 ≤ X) (hT : 1 ≤ T)
    (hlam : 0 < lam) :
    (Crows * (C ^ (2 * J) * (1 + Real.log X) ^ (2 * J) *
      (1 + T) ^ (a * (2 * J : ℕ)))) * X ^ (1 + (κ * z + lam / 2)) ≤
      (Crows * C ^ (2 * J) *
        PrimeCancellationUniformity.logAbsorptionConstant (2 * J) (lam / 2)) *
          X ^ (1 + κ * z + lam) * (1 + T) ^ (a * (2 * J : ℕ)) := by
  have hxp : 0 < X := zero_lt_one.trans_le hX
  have htp : 0 ≤ (1 + T) ^ (a * (2 * J : ℕ)) := Real.rpow_nonneg (by linarith) _
  have hb := PrimeCancellationUniformity.one_add_log_pow_le_rpow
    (2 * J) (show 0 < lam / 2 by linarith) hX
  calc
    _ ≤ (Crows * (C ^ (2 * J) *
        (PrimeCancellationUniformity.logAbsorptionConstant (2 * J) (lam / 2) *
          X ^ (lam / 2)) * (1 + T) ^ (a * (2 * J : ℕ)))) *
        X ^ (1 + (κ * z + lam / 2)) := by
      gcongr
    _ = _ := by
      rw [show 1 + κ * z + lam = lam / 2 + (1 + (κ * z + lam / 2)) by ring,
        Real.rpow_add hxp (lam / 2) (1 + (κ * z + lam / 2))]
      ring

end HeckeSkeleton.PrimeCancellationBounds
