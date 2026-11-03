import HeckeGeneral.Analysis.WitnessRowCount
import HeckeGeneral.Analysis.EndpointRangeSavings

/-!
# Numerics for the direct closure from the Euler-product bound

The closure may start from the common boundary `7/8 < B ≤ 1` instead of the
separate `11/12` theorem.  Two new ranges occur.

* Bins with `5/6 ≤ δ ≤ 1` (Q Remark 19.3 allows the unselected inverse count
  for `1/50 < δ ≤ 1`).  At witness parameter `t = 3/2`: if `r ≥ 1` the amplified
  inverse moment gives `1/6 + (5/6 - δ) r ≤ 1 - δ`; if `r < 1`, then `m > 1/2 - η`
  and the zero-slot plain moment gives `1 - 2δm ≤ 1 - δ + 2η`.  The moderate
  exponent is then at most `-1/48 - δ/16 ≤ -7/96`, plus the losses.  In Q the
  saturation bounds of Proposition 8.3 (`m ≤ 1/2 + O(ε)`, so `r ≥ 1 - O(ε)`)
  make the inverse side enough.  `WitnessCover` records only `r ≤ t + λ` and
  `r + m ≥ t - λ`, so the branch `r < 1` uses the zero-slot case of Q Lemma
  18.1 instead.
* Dynamic capacities `κ = 3/4 + 2Δ` up to `κ = 1`, i.e. `0 ≤ Δ ≤ 1/8`
  (Q Lemma 18.1 and its transfer M Proposition A.1 cover `3/4 ≤ κ ≤ 1`; Q
  Section 20 uses only `Δ ≤ 1/24`).  The certificate comparison is unchanged;
  only the slope bound for the frequency extension is re-checked.
-/

namespace HeckeGeneral.Analysis

open OAI.SevenEighths.Endpoint
open scoped BigOperators

/-- Markov counting at base `U` (local copy of the `WitnessRowCount` helper):
a pointwise lower bound `U ^ a` and a moment bound `k U ^ b H` leave at most
`k U ^ (b - a) H` rows. -/
private theorem large_card_le_rpow_of_markov {Row : Type*} (C : Finset Row) (f : Row → ℝ)
    {U a b k H : ℝ} (hU : 0 < U) (hlow : ∀ u ∈ C, U ^ a ≤ f u)
    (hsum : ∑ u ∈ C, f u ≤ k * U ^ b * H) :
    (C.card : ℝ) ≤ k * U ^ (b - a) * H := by
  have h := card_mul_le_of_forall_le C f hlow hsum
  have hpos : 0 < U ^ a := Real.rpow_pos_of_pos hU a
  have heq : k * U ^ (b - a) * H = k * U ^ b * H / U ^ a := by
    rw [Real.rpow_sub hU]
    ring
  rw [heq, le_div_iff₀ hpos]
  exact h

/-- Raising the exponent of a row-count bound at base `U ≥ 1`. -/
private theorem large_card_le_rpow_mono {Row : Type*} {C : Finset Row} {U a b k H : ℝ}
    (hU : 1 ≤ U) (hk : 0 ≤ k) (hH : 0 ≤ H)
    (h : (C.card : ℝ) ≤ k * U ^ a * H) (hab : a ≤ b) :
    (C.card : ℝ) ≤ k * U ^ b * H :=
  h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hab) hk) hH)

private theorem large_rpow_two_mul_eq_sq {U : ℝ} (hU : 0 < U) (a : ℝ) :
    U ^ (2 * a) = (U ^ a) ^ 2 := by
  rw [two_mul, Real.rpow_add hU, sq]

/-- Pointwise lower bound for a zero-slot plain row: `‖S u ^ 2‖ ^ 2 = ‖S u‖ ^ 4`. -/
private theorem large_plain_lower {Row : Type*} (S : Row → ℂ) {U δ m lam : ℝ} (hU : 0 < U)
    (u : Row) (hS : U ^ (δ * m - lam) ≤ ‖S u‖ ^ 2) :
    U ^ (2 * (δ * m - lam)) ≤ ‖S u ^ 2‖ ^ 2 := by
  rw [large_rpow_two_mul_eq_sq hU, norm_pow]
  exact pow_le_pow_left₀ (Real.rpow_pos_of_pos hU _).le hS 2

/-- Large bins `5/6 ≤ δ ≤ 1`: the unselected count at witness parameter `3/2`. -/
theorem witness_row_count_large {Row : Type*} (C : Finset Row) (M S : Row → ℂ)
    {U δ r m lam η k H : ℝ}
    (hU : 1 < U) (hδ0 : 5 / 6 ≤ δ) (hδ1 : δ ≤ 1) (hr0 : 0 ≤ r) (hm0 : 0 ≤ m)
    (hrmt : 3 / 2 - η ≤ r + m) (hlam : 0 ≤ lam) (hη : 0 ≤ η)
    (hk : 0 ≤ k) (hH : 0 ≤ H)
    (hMspike : ∀ u ∈ C, U ^ (δ * r - lam) ≤ ‖M u‖ ^ 2)
    (hSspike : ∀ u ∈ C, U ^ (δ * m - lam) ≤ ‖S u‖ ^ 2)
    (hIamp : ∑ u ∈ C, ‖M u‖ ^ 2 ≤ k * U ^ (amplifiedInverseExponent r + lam) * H)
    (hP0 : ∑ u ∈ C, ‖S u ^ 2‖ ^ 2 ≤ k * U ^ (1 + lam) * H) :
    (C.card : ℝ) ≤ k * U ^ (1 - δ + (3 * lam + 2 * η)) * H := by
  have hU0 : (0 : ℝ) < U := by linarith
  rcases le_or_gt 1 r with hr1 | hr1
  · -- `r ≥ 1`: the amplified inverse moment, `1/6 + (5/6 - δ) r ≤ 1 - δ` as `δ ≥ 5/6`.
    have hAmp : (C.card : ℝ) ≤
        k * U ^ (amplifiedInverseExponent r + lam - (δ * r - lam)) * H :=
      large_card_le_rpow_of_markov C (fun u => ‖M u‖ ^ 2) hU0 hMspike hIamp
    have he : amplifiedInverseExponent r = (1 + 5 * r) / 6 := by
      unfold amplifiedInverseExponent
      exact max_eq_right (by linarith)
    rw [he] at hAmp
    refine large_card_le_rpow_mono hU.le hk hH hAmp ?_
    have h1 : (5 / 6 - δ) * r ≤ (5 / 6 - δ) * 1 :=
      mul_le_mul_of_nonpos_left hr1 (by linarith)
    linarith
  · -- `r < 1`: then `m > 1/2 - η`, and the zero-slot plain moment gives
    -- `1 - 2δm ≤ 1 - δ + 2δη ≤ 1 - δ + 2η`.
    have hZero : (C.card : ℝ) ≤ k * U ^ (1 + lam - 2 * (δ * m - lam)) * H :=
      large_card_le_rpow_of_markov C (fun u => ‖S u ^ 2‖ ^ 2) hU0
        (fun u hu => large_plain_lower S hU0 u (hSspike u hu)) hP0
    refine large_card_le_rpow_mono hU.le hk hH hZero ?_
    have h1 : δ * (1 / 2 - η) ≤ δ * m :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : δ * η ≤ 1 * η := mul_le_mul_of_nonneg_right hδ1 hη
    have h3 : 0 ≤ δ * r := mul_nonneg (by linarith) hr0
    have h4 : 0 ≤ δ * m := mul_nonneg (by linarith) hm0
    linarith

/-- The moderate exponent of a large bin, including the fixed extension above `h`. -/
theorem large_bin_saving {d δ q R ε ζ : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 13 / 16 + ζ)
    (hζ : 0 ≤ ζ) (hδ0 : 5 / 6 ≤ δ) (hδ1 : δ ≤ 1) (hq : q ≤ δ / 2)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 10) (hR : R ≤ 1 - δ + ε) :
    moderateExponent d δ q R ≤ -(7 / 96) + ε + ζ := by
  -- Raise the count to `1 - δ + ε`; its value at `d = 13/16` is at most
  -- `-1/48 - δ/16 + 13ε/16 ≤ -7/96 + 13ε/16`.
  have hc := moderateExponent_mono_count hd hR (δ := δ) (q := q)
  -- The bounding slope `33/50 - δ/2 + ε` lies in `[0, 1]`.
  have hs0 : 0 ≤ (1 - δ + ε) + δ / 2 - 17 / 50 := by linarith
  have hs1 : (1 - δ + ε) + δ / 2 - 17 / 50 ≤ 1 := by linarith
  have hmove := mul_le_mul_of_nonneg_right (show d - 13 / 16 ≤ ζ by linarith) hs0
  have hext := mul_le_mul_of_nonneg_left hs1 hζ
  unfold moderateExponent at *
  linarith

/-- The bounding slope of `moderate_bounding_slope`, re-checked for `Δ ≤ 1/8`
(so `Δ/4 ≤ 1/32`): it stays in `[73/300, 2]`. -/
private theorem moderate_bounding_slope_extended {δ y Δ ε : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1 / 8) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 12) :
    73 / 300 ≤ balancedRowCount δ y + Δ / 4 + ε + δ / 2 - 17 / 50 ∧
      balancedRowCount δ y + Δ / 4 + ε + δ / 2 - 17 / 50 ≤ 2 := by
  obtain ⟨hl, hu⟩ := balancedRowCount_range hδ0 hδ1 hy0 hy1
  constructor <;> linarith

/-- `dynamic_moderate_range_saving` for every dynamic capacity up to `κ = 1`. -/
theorem dynamic_moderate_range_saving_extended {d δ y Δ ε ζ R : ℝ}
    (hd : 0 ≤ d) (hdhi : d ≤ 13 / 16 + ζ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1 / 8)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 12) (hζ : 0 ≤ ζ)
    (hR : R ≤ balancedRowCount δ y + Δ / 4 + ε) :
    moderateExponent d δ (δ * (1 / 2 - y)) R - Δ ≤
      -(49 / 440640) - (51 / 64) * Δ + (13 / 16) * ε + 2 * ζ := by
  let Rb := balancedRowCount δ y + Δ / 4 + ε
  have hc := moderateExponent_mono_count hd hR (δ := δ) (q := δ * (1 / 2 - y))
  have he := dynamic_endpoint_saving_with_loss hδ0 hδ1 hy0 hy1
    (R := Rb) (Δ := Δ) (ε := ε) (le_refl _)
  obtain ⟨hlo, hhi⟩ := moderate_bounding_slope_extended hδ0 hδ1 hy0 hy1 hΔ0 hΔ1 hε0 hε1
  have hs0 : 0 ≤ Rb + δ / 2 - 17 / 50 := by dsimp [Rb]; linarith
  have hmove := mul_le_mul_of_nonneg_right (show d - 13 / 16 ≤ ζ by linarith) hs0
  have hext := mul_le_mul_of_nonneg_left hhi hζ
  change moderateExponent d δ (δ * (1 / 2 - y)) R ≤
    moderateExponent d δ (δ * (1 / 2 - y)) Rb at hc
  dsimp only [Rb] at *
  unfold moderateExponent at *
  nlinarith only [hc, he, hmove, hext]

end HeckeGeneral.Analysis
