import ExpansionDetector.MellinPowerBudget

/-! The three explicit analytic costs expressed in one varying scale U.
Only norm/conductor/height size comparisons are inputs. -/
noncomputable section
namespace ExpansionDetector.PowerBudget

def bufferedScaleConstant (C R ε k : ℝ) : ℝ := C * R ^ ε * R ^ ε * R ^ (k * ε)
def reflectedScaleConstant (C R e ε k : ℝ) : ℝ :=
  C * R ^ (6 * e + ε) * R * R ^ ε * R ^ k * R ^ (k * ε)
def coarseScaleConstant (C R ε k : ℝ) : ℝ :=
  C * R ^ (1 / 8 + ε) * R ^ (5 / 8 : ℝ) * R ^ k

theorem buffered_monomial_scale_bound (C R ε k U θ N Q H : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hε : 0 ≤ ε) (hk : 0 ≤ k)
    (hU : 0 < U) (hN : 0 ≤ N) (hQ : 0 ≤ Q) (hH : 0 ≤ H)
    (hNU : N ≤ R * U) (hQU : Q ≤ R * U) (hHU : H ≤ R * U ^ θ) :
    C * N ^ ε * Q ^ ε * H ^ (k * ε) ≤
      bufferedScaleConstant C R ε k * U ^ (2 * ε + k * ε * θ) := by
  have hNp := Real.rpow_le_rpow hN hNU hε
  have hQp := Real.rpow_le_rpow hQ hQU hε
  have hHp := Real.rpow_le_rpow hH hHU (mul_nonneg hk hε)
  calc
    _ ≤ C * (R * U) ^ ε * (R * U) ^ ε * (R * U ^ θ) ^ (k * ε) := by
      apply mul_le_mul _ hHp (Real.rpow_nonneg hH _) (by positivity)
      apply mul_le_mul _ hQp (Real.rpow_nonneg hQ _) (by positivity)
      exact mul_le_mul_of_nonneg_left hNp hC
    _ = bufferedScaleConstant C R ε k * U ^ (2 * ε + k * ε * θ) := by
      rw [Real.mul_rpow hR hU.le, Real.mul_rpow hR (Real.rpow_nonneg hU.le _),
        ← Real.rpow_mul hU.le]
      have hp : U ^ ε * U ^ ε * U ^ (θ * (k * ε)) = U ^ (2 * ε + k * ε * θ) := by
        rw [← Real.rpow_add hU, ← Real.rpow_add hU]
        congr 1
        ring
      calc
        _ = bufferedScaleConstant C R ε k * (U ^ ε * U ^ ε * U ^ (θ * (k * ε))) := by
          unfold bufferedScaleConstant
          ring
        _ = _ := by rw [hp]

theorem reflected_monomial_scale_bound (C R e ε k U θ N Q H a : ℝ)
    (hC : 0 ≤ C) (hR : 1 ≤ R) (he : 0 ≤ e) (he' : e ≤ 1 / 12)
    (hε : 0 ≤ ε) (hk : 0 ≤ k) (hU : 0 < U)
    (hN : 0 ≤ N) (hQ : 0 ≤ Q) (hH : 0 ≤ H)
    (hNU : N ≤ R * U) (hQU : Q ≤ R * U) (hHU : H ≤ R * U ^ θ)
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) :
    C * N ^ (6 * e + ε) * Q ^ (a - 1 / 2 + 6 * e) * Q ^ ε * H ^ k * H ^ (k * ε) ≤
      reflectedScaleConstant C R e ε k *
        U ^ (a - 1 / 2 + 12 * e + 2 * ε + k * θ * (1 + ε)) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hα : 0 ≤ a - 1 / 2 + 6 * e := by linarith
  have hα1 : a - 1 / 2 + 6 * e ≤ 1 := by linarith
  have hNp := Real.rpow_le_rpow hN hNU (show 0 ≤ 6 * e + ε by positivity)
  have hQp : Q ^ (a - 1 / 2 + 6 * e) ≤ R * U ^ (a - 1 / 2 + 6 * e) := by
    calc
      _ ≤ (R * U) ^ (a - 1 / 2 + 6 * e) := Real.rpow_le_rpow hQ hQU hα
      _ = R ^ (a - 1 / 2 + 6 * e) * U ^ (a - 1 / 2 + 6 * e) := Real.mul_rpow hR0 hU.le
      _ ≤ R * U ^ (a - 1 / 2 + 6 * e) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU.le _)
        exact (Real.rpow_le_rpow_of_exponent_le hR hα1).trans_eq (Real.rpow_one R)
  have hQε := Real.rpow_le_rpow hQ hQU hε
  have hHk := Real.rpow_le_rpow hH hHU hk
  have hHε := Real.rpow_le_rpow hH hHU (mul_nonneg hk hε)
  calc
    _ ≤ C * (R * U) ^ (6 * e + ε) * (R * U ^ (a - 1 / 2 + 6 * e)) *
        (R * U) ^ ε * (R * U ^ θ) ^ k * (R * U ^ θ) ^ (k * ε) := by
      apply mul_le_mul _ hHε (Real.rpow_nonneg hH _) (by positivity)
      apply mul_le_mul _ hHk (Real.rpow_nonneg hH _) (by positivity)
      apply mul_le_mul _ hQε (Real.rpow_nonneg hQ _) (by positivity)
      apply mul_le_mul _ hQp (Real.rpow_nonneg hQ _) (by positivity)
      exact mul_le_mul_of_nonneg_left hNp hC
    _ = _ := by
      simp only [Real.mul_rpow hR0 hU.le,
        Real.mul_rpow hR0 (Real.rpow_nonneg hU.le θ), ← Real.rpow_mul hU.le]
      have hp : U ^ (6 * e + ε) * U ^ (a - 1 / 2 + 6 * e) * U ^ ε *
          U ^ (θ * k) * U ^ (θ * (k * ε)) =
          U ^ (a - 1 / 2 + 12 * e + 2 * ε + k * θ * (1 + ε)) := by
        repeat rw [← Real.rpow_add hU]
        congr 1
        ring
      calc
        _ = reflectedScaleConstant C R e ε k *
            (U ^ (6 * e + ε) * U ^ (a - 1 / 2 + 6 * e) * U ^ ε *
              U ^ (θ * k) * U ^ (θ * (k * ε))) := by
          unfold reflectedScaleConstant
          ring
        _ = _ := by rw [hp]

theorem coarse_monomial_scale_bound (C R ε k U θ N Q H : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hε : 0 ≤ ε) (hk : 0 ≤ k)
    (hU : 0 < U) (hN : 0 ≤ N) (hQ : 0 ≤ Q) (hH : 0 ≤ H)
    (hNU : N ≤ R * U) (hQU : Q ≤ R * U) (hHU : H ≤ R * U ^ θ) :
    C * N ^ (1 / 8 + ε) * Q ^ (5 / 8 : ℝ) * H ^ k ≤
      coarseScaleConstant C R ε k * U ^ (3 / 4 + ε + k * θ) := by
  have hNp := Real.rpow_le_rpow hN hNU (show 0 ≤ 1 / 8 + ε by linarith)
  have hQp := Real.rpow_le_rpow hQ hQU (by norm_num : (0 : ℝ) ≤ 5 / 8)
  have hHp := Real.rpow_le_rpow hH hHU hk
  calc
    _ ≤ C * (R * U) ^ (1 / 8 + ε) * (R * U) ^ (5 / 8 : ℝ) * (R * U ^ θ) ^ k := by
      apply mul_le_mul _ hHp (Real.rpow_nonneg hH _) (by positivity)
      apply mul_le_mul _ hQp (Real.rpow_nonneg hQ _) (by positivity)
      exact mul_le_mul_of_nonneg_left hNp hC
    _ = _ := by
      simp only [Real.mul_rpow hR hU.le,
        Real.mul_rpow hR (Real.rpow_nonneg hU.le θ), ← Real.rpow_mul hU.le]
      have hp : U ^ (1 / 8 + ε) * U ^ (5 / 8 : ℝ) * U ^ (θ * k) =
          U ^ (3 / 4 + ε + k * θ) := by
        rw [← Real.rpow_add hU, ← Real.rpow_add hU]
        congr 1
        ring
      calc
        _ = coarseScaleConstant C R ε k *
            (U ^ (1 / 8 + ε) * U ^ (5 / 8 : ℝ) * U ^ (θ * k)) := by
          unfold coarseScaleConstant
          ring
        _ = _ := by rw [hp]

end ExpansionDetector.PowerBudget
