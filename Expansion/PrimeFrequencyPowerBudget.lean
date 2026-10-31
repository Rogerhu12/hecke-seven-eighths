import Expansion.NormalizedContourBudget

/-!
# A power budget for finite-height prime cancellation

The frequency is bounded inside a fixed multiple of the physical height.
All constants below precede that frequency. Logarithmic conductor and
height losses, the original ideal-deletion loss, and both finite contour
tails are absorbed into an arbitrary prescribed positive power loss.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.PrimeFrequencyPowerBudget

open Expansion.NormalizedContourBudget

def logDerivativeConstant (degree C A L δ ε : ℝ) : ℝ :=
  (48 / δ ^ 2) *
    (1 + Real.log C + A + degree * Real.log (L + 5) + (5 / 8 + degree) / ε)

theorem logDerivativeConstant_nonneg {degree C A L δ ε : ℝ}
    (hd : 0 ≤ degree) (hC : 1 ≤ C) (hA : 0 ≤ A) (hL : 0 ≤ L) (hε : 0 < ε) :
    0 ≤ logDerivativeConstant degree C A L δ ε := by
  have hlogC := Real.log_nonneg hC
  have hlogL := Real.log_nonneg (by linarith : 1 ≤ L + 5)
  unfold logDerivativeConstant
  positivity

/-- The actual logarithmic-derivative envelope has one uniform small power,
even when the physical frequency is selected afterwards. -/
theorem logDerivative_le_power {degree C A L δ ε Z U τ ν : ℝ}
    (hd : 0 ≤ degree) (hC : 1 ≤ C) (hA : 0 ≤ A) (hL : 0 ≤ L) (hε : 0 < ε)
    (hZ : 1 ≤ Z) (hU : 1 ≤ U) (hUZ : U ≤ Z) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1)
    (hν : |ν| ≤ L * Z ^ τ) :
    48 * (1 + Real.log C + (5 / 8) * Real.log U +
      degree * Real.log (4 + |ν| + Z ^ τ) + A) / δ ^ 2 ≤
      logDerivativeConstant degree C A L δ ε * Z ^ ε := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hH : 1 ≤ Z ^ τ := Real.one_le_rpow hZ hτ
  have hHpos : 0 < Z ^ τ := Real.rpow_pos_of_pos hZpos _
  have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg hZ
  have hlogU : Real.log U ≤ Real.log Z := Real.log_le_log hUpos hUZ
  have hheight : 4 + |ν| + Z ^ τ ≤ (L + 5) * Z ^ τ := by
    nlinarith only [hν, hH]
  have hlogheight : Real.log (4 + |ν| + Z ^ τ) ≤
      Real.log (L + 5) + Real.log Z := by
    have hh := Real.log_le_log (by positivity : 0 < 4 + |ν| + Z ^ τ) hheight
    rw [Real.log_mul (by positivity : L + 5 ≠ 0) hHpos.ne', Real.log_rpow hZpos] at hh
    exact hh.trans (add_le_add le_rfl
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hτ' hlogZ))
  let a := 1 + Real.log C + A + degree * Real.log (L + 5)
  let b := 5 / 8 + degree
  have ha : 0 ≤ a := by
    have hc := Real.log_nonneg hC
    have hl := Real.log_nonneg (by linarith : 1 ≤ L + 5)
    dsimp [a]
    positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hsum : 1 + Real.log C + (5 / 8) * Real.log U +
      degree * Real.log (4 + |ν| + Z ^ τ) + A ≤ a + b * Real.log Z := by
    have hu := mul_le_mul_of_nonneg_left hlogU (by norm_num : (0 : ℝ) ≤ 5 / 8)
    have ht := mul_le_mul_of_nonneg_left hlogheight hd
    dsimp [a, b]
    linarith only [hu, ht]
  have hlog := Real.log_le_rpow_div hZpos.le hε
  have hpow : 1 ≤ Z ^ ε := Real.one_le_rpow hZ hε.le
  have hab : a + b * Real.log Z ≤ (a + b / ε) * Z ^ ε := by
    have hc := mul_le_mul_of_nonneg_left hpow ha
    have hl := mul_le_mul_of_nonneg_left hlog hb
    nlinarith only [hc, hl]
  calc
    _ = (48 / δ ^ 2) * (1 + Real.log C + (5 / 8) * Real.log U +
        degree * Real.log (4 + |ν| + Z ^ τ) + A) := by ring
    _ ≤ (48 / δ ^ 2) * ((a + b / ε) * Z ^ ε) :=
      mul_le_mul_of_nonneg_left (hsum.trans hab) (by positivity)
    _ = _ := by unfold logDerivativeConstant; dsimp [a, b]; ring

def contourPowerConstant (D mass CW : ℝ) : ℝ :=
  3 * ((1 / (2 * Real.pi)) * CW * (7 * D + mass))

theorem contourPowerConstant_nonneg {D mass CW : ℝ}
    (hD : 0 ≤ D) (hmass : 0 ≤ mass) (hCW : 0 ≤ CW) :
    0 ≤ contourPowerConstant D mass CW := by
  unfold contourPowerConstant
  positivity

/-- The height order consumes both horizontal and initial-line tails. -/
theorem normalized_contour_le_power {Z ℓ β δ ε η τ M D mass CW : ℝ} {order : ℕ}
    (hZ : 1 ≤ Z) (hℓ : 0 ≤ ℓ) (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 1)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 4) (hε : 0 ≤ ε)
    (hloss : ε + δ * ℓ ≤ η) (horder : 3 / 2 * ℓ ≤ τ * order)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hmass : 0 ≤ mass) (hCW : 0 ≤ CW)
    (hbound : M ≤ D * Z ^ ε) :
    (Real.sqrt (Z ^ ℓ))⁻¹ *
      contourMajorant M M mass CW (2 - (β + δ)) (Z ^ ℓ) 0 (β + δ) (Z ^ τ) order ≤
      contourPowerConstant D mass CW * Z ^ ((β - 1 / 2) * ℓ + η) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hPpos : 0 < Z ^ ℓ := Real.rpow_pos_of_pos hZpos _
  have hsqrt : (Real.sqrt (Z ^ ℓ))⁻¹ = (Z ^ ℓ) ^ ((0 : ℝ) - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hPpos.le]
    congr 1
    ring
  rw [hsqrt]
  have hc := contourMajorant_le_scale (U := Z) (H := Z ^ τ) (τ := τ)
    (r := ℓ) (bL := ε) (bR := ε) (BL := M) (BR := M) (A := D) (B := D)
    (mass := mass) (CW := CW) (width := 2 - (β + δ)) (β := 0) (σ := β + δ)
    (N := order) hZ hM hM hD hD hmass hCW (by linarith) (by linarith)
    hbound hbound le_rfl
  have hbase : 0 ≤ (β - 1 / 2) * ℓ := mul_nonneg (sub_nonneg.mpr hβ) hℓ
  have heη : ε ≤ η := (le_add_of_nonneg_right (mul_nonneg hδ hℓ)).trans hloss
  have h1 : ε + (β + δ - 1 / 2) * ℓ ≤ (β - 1 / 2) * ℓ + η := by
    nlinarith only [hloss]
  have h2 : ε + 3 / 2 * ℓ - τ * order ≤ (β - 1 / 2) * ℓ + η := by
    linarith only [horder, hbase, heη]
  have h3 : 3 / 2 * ℓ - τ * order ≤ (β - 1 / 2) * ℓ + η := by
    linarith only [horder, hbase, hε, heη]
  have hp := add_le_add (add_le_add
    (Real.rpow_le_rpow_of_exponent_le hZ h1)
    (Real.rpow_le_rpow_of_exponent_le hZ h2))
    (Real.rpow_le_rpow_of_exponent_le hZ h3)
  have hk : 0 ≤ (1 / (2 * Real.pi)) * CW * (D + 6 * D + mass) := by positivity
  exact hc.trans ((mul_le_mul_of_nonneg_left hp hk).trans_eq (by
    unfold contourPowerConstant
    ring))

def deletionPowerConstant (D M ε : ℝ) : ℝ :=
  ((Real.log D + Real.log 2 + 1 / ε) / Real.log 2) * M

theorem deletionPowerConstant_nonneg {D M ε : ℝ}
    (hD : 1 ≤ D) (hM : 0 ≤ M) (hε : 0 < ε) :
    0 ≤ deletionPowerConstant D M ε := by
  have hd := Real.log_nonneg hD
  have htwo := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold deletionPowerConstant
  positivity

/-- The full original deletion costs a small power of the outer scale.
The fixed norm D contains all S/6 primes; N is the complete row norm. -/
theorem deletion_log_le_power {Z D N M ε : ℝ}
    (hZ : 1 ≤ Z) (hD : 1 ≤ D) (hN : 0 < N) (hNZ : N ≤ 2 * Z)
    (hM : 0 ≤ M) (hε : 0 < ε) :
    (Real.log (D * N) / Real.log 2) * M ≤ deletionPowerConstant D M ε * Z ^ ε := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (D * N) ≤ Real.log D + Real.log 2 + Real.log Z := by
    have hh := Real.log_le_log (mul_pos hDpos hN)
      (mul_le_mul_of_nonneg_left hNZ hDpos.le)
    rw [Real.log_mul hDpos.ne' (by positivity : (2 * Z : ℝ) ≠ 0),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hZpos.ne'] at hh
    linarith
  have hc : 0 ≤ Real.log D + Real.log 2 :=
    add_nonneg (Real.log_nonneg hD) hlogtwo.le
  have hp : 1 ≤ Z ^ ε := Real.one_le_rpow hZ hε.le
  have hl := Real.log_le_rpow_div hZpos.le hε
  have hm := mul_le_mul_of_nonneg_left hp hc
  have hn : Real.log (D * N) ≤ (Real.log D + Real.log 2 + 1 / ε) * Z ^ ε := by
    nlinarith only [hlog, hm, hl]
  have hh := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hn hlogtwo.le) hM
  exact hh.trans_eq (by unfold deletionPowerConstant; ring)

/-- Any positive physical height exponent admits the required finite order. -/
theorem exists_prime_contour_order {τ ℓ : ℝ} (hτ : 0 < τ) :
    ∃ order : ℕ, 3 / 2 * ℓ ≤ τ * order := by
  obtain ⟨order, horder⟩ := exists_nat_ge ((3 / 2 * ℓ) / τ)
  refine ⟨order, ?_⟩
  simpa only [mul_comm] using (div_le_iff₀ hτ).mp horder

end Expansion.PrimeFrequencyPowerBudget

#print axioms Expansion.PrimeFrequencyPowerBudget.logDerivative_le_power
#print axioms Expansion.PrimeFrequencyPowerBudget.normalized_contour_le_power
#print axioms Expansion.PrimeFrequencyPowerBudget.deletion_log_le_power
#print axioms Expansion.PrimeFrequencyPowerBudget.exists_prime_contour_order
