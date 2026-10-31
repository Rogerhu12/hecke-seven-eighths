import ExpansionDetector.MellinPowerBudget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Normalizing the literal finite contour estimate

These numerical lemmas preserve the separate sharp left-line constant and
coarse horizontal-line constant. Their analytic input is the exact
three-term contour expression supplied by the actual deleted Hecke
polynomial theorems. They do not assert a zero-detection conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.NormalizedContourBudget

open ExpansionDetector.PowerBudget

def contourMajorant (BL BR mass CW width X β σ H : ℝ) (N : ℕ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ((BL * X ^ (σ - β)) * CW +
      2 * (CW / (1 + H) ^ N) * BR * X ^ (2 - β) * width +
      (mass * X ^ (2 - β)) * (CW / H ^ N))

theorem normalized_contourMajorant
    (BL BR mass CW width X β σ H : ℝ) (N : ℕ) (hX : 0 < X) :
    X ^ (β - 1 / 2) * contourMajorant BL BR mass CW width X β σ H N =
      (1 / (2 * Real.pi)) * CW *
        (BL * X ^ (σ - 1 / 2) +
          2 * width * BR * X ^ (3 / 2 : ℝ) / (1 + H) ^ N +
          mass * X ^ (3 / 2 : ℝ) / H ^ N) := by
  have hp : X ^ (β - 1 / 2) * X ^ (σ - β) = X ^ (σ - 1 / 2) := by
    rw [← Real.rpow_add hX]
    congr 1
    ring
  have hq : X ^ (β - 1 / 2) * X ^ (2 - β) = X ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hX]
    congr 1
    ring
  unfold contourMajorant
  calc
    _ = (1 / (2 * Real.pi)) * CW *
        (BL * (X ^ (β - 1 / 2) * X ^ (σ - β)) +
          2 * width * BR * (X ^ (β - 1 / 2) * X ^ (2 - β)) / (1 + H) ^ N +
          mass * (X ^ (β - 1 / 2) * X ^ (2 - β)) / H ^ N) := by ring
    _ = _ := by rw [hp, hq]

theorem scaled_horizontal_term
    {U H τ r b A B : ℝ} {N : ℕ}
    (hU : 0 < U) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : B ≤ A * U ^ b) (hheight : U ^ τ ≤ H) :
    B * (U ^ r) ^ (3 / 2 : ℝ) / H ^ N ≤
      A * U ^ (b + 3 / 2 * r - τ * N) := by
  have hH : 0 < H := (Real.rpow_pos_of_pos hU τ).trans_le hheight
  have hHp : (U ^ τ) ^ N ≤ H ^ N :=
    pow_le_pow_left₀ (Real.rpow_nonneg hU.le τ) hheight N
  calc
    _ ≤ (A * U ^ b) * (U ^ r) ^ (3 / 2 : ℝ) / H ^ N :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbound (by positivity)) (by positivity)
    _ ≤ (A * U ^ b) * (U ^ r) ^ (3 / 2 : ℝ) / (U ^ τ) ^ N :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hHp
    _ = _ := by
      rw [← Real.rpow_mul hU.le, ← Real.rpow_mul_natCast hU.le,
        mul_assoc, ← Real.rpow_add hU, mul_div_assoc, ← Real.rpow_sub hU]
      congr 2
      ring

/-- A single fixed scalar dominates the normalized contour expression.
The reflected main term retains its own exponent `bL`; only the horizontal
error uses `bR`. -/
theorem contourMajorant_le_scale
    {U H τ r bL bR BL BR A B mass CW width β σ : ℝ} {N : ℕ}
    (hU : 1 ≤ U) (hBL : 0 ≤ BL) (hBR : 0 ≤ BR)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hmass : 0 ≤ mass)
    (hCW : 0 ≤ CW) (hwidth : 0 ≤ width) (hwidth' : width ≤ 3)
    (hleft : BL ≤ A * U ^ bL) (hright : BR ≤ B * U ^ bR)
    (hheight : U ^ τ ≤ H) :
    (U ^ r) ^ (β - 1 / 2) *
        contourMajorant BL BR mass CW width (U ^ r) β σ H N ≤
      ((1 / (2 * Real.pi)) * CW * (A + 6 * B + mass)) *
        (U ^ (bL + (σ - 1 / 2) * r) +
          U ^ (bR + 3 / 2 * r - τ * N) + U ^ (3 / 2 * r - τ * N)) := by
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hH : 0 < H := (Real.rpow_pos_of_pos hUpos τ).trans_le hheight
  rw [normalized_contourMajorant _ _ _ _ _ _ _ _ _ _ (by positivity)]
  have hmain : BL * (U ^ r) ^ (σ - 1 / 2) ≤
      A * U ^ (bL + (σ - 1 / 2) * r) := by
    calc
      _ ≤ (A * U ^ bL) * (U ^ r) ^ (σ - 1 / 2) :=
        mul_le_mul_of_nonneg_right hleft (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul hUpos.le, mul_assoc, ← Real.rpow_add hUpos]
        congr 2
        ring
  have hhorizontal :
      2 * width * BR * (U ^ r) ^ (3 / 2 : ℝ) / (1 + H) ^ N ≤
        6 * B * U ^ (bR + 3 / 2 * r - τ * N) := by
    have hsmall := scaled_horizontal_term (r := r) (N := N) hUpos hB hBR hright
      (hheight.trans (by linarith : H ≤ 1 + H))
    calc
      _ = (2 * width) * (BR * (U ^ r) ^ (3 / 2 : ℝ) / (1 + H) ^ N) := by ring
      _ ≤ (2 * width) * (B * U ^ (bR + 3 / 2 * r - τ * N)) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ _ := by
        have hw : 2 * width ≤ 6 := by linarith
        have hh := mul_le_mul_of_nonneg_right hw
          (show 0 ≤ B * U ^ (bR + 3 / 2 * r - τ * N) by positivity)
        simpa only [mul_assoc] using hh
  have htail : mass * (U ^ r) ^ (3 / 2 : ℝ) / H ^ N ≤
      mass * U ^ (3 / 2 * r - τ * N) := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using
      (scaled_horizontal_term (b := 0) (r := r) (N := N) hUpos hmass hmass
        (by rw [Real.rpow_zero, mul_one]) hheight)
  have hsum := add_le_add (add_le_add hmain hhorizontal) htail
  have hsum' :
      A * U ^ (bL + (σ - 1 / 2) * r) +
        6 * B * U ^ (bR + 3 / 2 * r - τ * N) +
        mass * U ^ (3 / 2 * r - τ * N) ≤
      (A + 6 * B + mass) *
        (U ^ (bL + (σ - 1 / 2) * r) +
          U ^ (bR + 3 / 2 * r - τ * N) + U ^ (3 / 2 * r - τ * N)) := by
    have h₁ : A ≤ A + 6 * B + mass := by linarith
    have h₂ : 6 * B ≤ A + 6 * B + mass := by linarith
    have h₃ : mass ≤ A + 6 * B + mass := by linarith
    have h := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right h₁ (Real.rpow_nonneg hUpos.le (bL + (σ - 1 / 2) * r)))
      (mul_le_mul_of_nonneg_right h₂ (Real.rpow_nonneg hUpos.le (bR + 3 / 2 * r - τ * N))))
      (mul_le_mul_of_nonneg_right h₃ (Real.rpow_nonneg hUpos.le (3 / 2 * r - τ * N)))
    nlinarith
  exact (mul_le_mul_of_nonneg_left (hsum.trans hsum')
    (show 0 ≤ (1 / (2 * Real.pi)) * CW by positivity)).trans_eq (by ring)

theorem three_power_majorant_mono
    {U C₀ C a b c x η : ℝ} (hU : 1 ≤ U) (hC₀ : 0 ≤ C₀) (hC : C₀ ≤ C)
    (ha : a ≤ x + η / 4) (hb : b ≤ -100) (hc : c ≤ -100) :
    C₀ * (U ^ a + U ^ b + U ^ c) ≤
      C * (U ^ (x + η / 4) + U ^ (-100 : ℝ) + U ^ (-100 : ℝ)) := by
  have hsum := add_le_add (add_le_add
    (Real.rpow_le_rpow_of_exponent_le hU ha)
    (Real.rpow_le_rpow_of_exponent_le hU hb))
    (Real.rpow_le_rpow_of_exponent_le hU hc)
  exact (mul_le_mul_of_nonneg_left hsum hC₀).trans
    (mul_le_mul_of_nonneg_right hC (by positivity))

/-- A concrete simultaneous small-loss choice. The permitted bin-width cap
is imposed first; the common positive height ceiling is then fixed before
the later Fourier/contour truncation exponent or tail order. -/
theorem exists_detector_loss_budget (k η cap : ℝ)
    (hk : 0 ≤ k) (hη : 0 < η) (hcap : 0 < cap) :
    ∃ e ε θ : ℝ, 0 < e ∧ e < 1 / 1000 ∧ e ≤ cap ∧
      0 < ε ∧ ε ≤ 1 ∧ 0 < θ ∧ θ ≤ 1 ∧
      132 * e + 2 * ε + k * ε * θ ≤ η / 4 ∧
      12 * e + 2 * ε + k * θ * (1 + ε) ≤ η / 4 := by
  let e := min cap (min (1 / 2000) (η / 2112))
  let w := min 1 (η / (64 * (k + 1)))
  have he : 0 < e := by
    unfold e
    apply lt_min hcap
    exact lt_min (by norm_num) (by positivity)
  have hecap : e ≤ cap := min_le_left _ _
  have he₁ : e ≤ 1 / 2000 := (min_le_right _ _).trans (min_le_left _ _)
  have he₂ : e ≤ η / 2112 := (min_le_right _ _).trans (min_le_right _ _)
  have hw : 0 < w := by
    unfold w
    exact lt_min zero_lt_one (by positivity)
  have hw₁ : w ≤ 1 := min_le_left _ _
  have hw₂ : w ≤ η / (64 * (k + 1)) := min_le_right _ _
  have hden : 0 < 64 * (k + 1) := by positivity
  have hscaled := (le_div_iff₀ hden).mp hw₂
  have hkw : 0 ≤ k * w := mul_nonneg hk hw.le
  have hkw₂ : k * w * w ≤ k * w := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hw₁ hkw
  have hecost : 132 * e ≤ η / 16 := by linarith
  have hecost' : 12 * e ≤ η / 16 := by linarith
  have hwcost : 2 * w ≤ η / 32 := by nlinarith
  have hkwcost : k * w ≤ η / 64 := by nlinarith
  refine ⟨e, w, w, he, by linarith, hecap, hw, hw₁, hw, hw₁, ?_, ?_⟩
  · nlinarith
  · nlinarith

end Expansion.NormalizedContourBudget
