import HeckeGeneral.Analysis.DynamicWitnessCrossing

/-! The complete real-parameter range bookkeeping in M Section 7.
The input R is a row-count EXPONENT; this file does not assume or prove
that any actual collection of rows has that count. The positive slope is
proved for the bounding exponent before comparing smaller actual R.
All choices here precede the target character and its height constants. -/

noncomputable section
namespace HeckeGeneral.Analysis

open OAI.SevenEighths.Endpoint

theorem balancedRowCount_range {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    1 - δ ≤ balancedRowCount δ y ∧
      balancedRowCount δ y ≤ 17 / 12 - 3 * δ / 2 := by
  obtain ⟨ht0, ht1⟩ := balancedCutoff_mem_Icc hδ0 hδ1 hy0 hy1
  have ha : 0 ≤ 5 / 6 - δ := by linarith
  have hl := mul_le_mul_of_nonneg_left ht0 ha
  have hu := mul_le_mul_of_nonneg_left ht1 ha
  unfold balancedRowCount
  constructor <;> nlinarith

theorem moderateExponent_mono_count {d δ q R R' : ℝ}
    (hd : 0 ≤ d) (hR : R ≤ R') :
    moderateExponent d δ q R ≤ moderateExponent d δ q R' := by
  have h := mul_le_mul_of_nonneg_left hR hd
  unfold moderateExponent
  nlinarith only [h]

/-- Both slope bounds hold for the upper count, not necessarily the
actual count. This distinction matters below the endpoint d=13/16. -/
theorem moderate_bounding_slope {δ y Δ ε : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1 / 24) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 12) :
    73 / 300 ≤ balancedRowCount δ y + Δ / 4 + ε + δ / 2 - 17 / 50 ∧
      balancedRowCount δ y + Δ / 4 + ε + δ / 2 - 17 / 50 ≤ 2 := by
  obtain ⟨hl, hu⟩ := balancedRowCount_range hδ0 hδ1 hy0 hy1
  constructor <;> linarith

/-- A single estimate covers d below the endpoint and the fixed extension
up to 13/16+zeta, including delta=5/6. The extension cost is explicit. -/
theorem dynamic_moderate_range_saving {d δ y Δ ε ζ R : ℝ}
    (hd : 0 ≤ d) (hdhi : d ≤ 13 / 16 + ζ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1 / 24)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 12) (hζ : 0 ≤ ζ)
    (hR : R ≤ balancedRowCount δ y + Δ / 4 + ε) :
    moderateExponent d δ (δ * (1 / 2 - y)) R - Δ ≤
      -(49 / 440640) - (51 / 64) * Δ + (13 / 16) * ε + 2 * ζ := by
  let Rb := balancedRowCount δ y + Δ / 4 + ε
  have hc := moderateExponent_mono_count hd hR (δ := δ) (q := δ * (1 / 2 - y))
  have he := dynamic_endpoint_saving_with_loss hδ0 hδ1 hy0 hy1
    (R := Rb) (Δ := Δ) (ε := ε) (le_refl _)
  obtain ⟨hlo, hhi⟩ := moderate_bounding_slope hδ0 hδ1 hy0 hy1 hΔ0 hΔ1 hε0 hε1
  have hs0 : 0 ≤ Rb + δ / 2 - 17 / 50 := by dsimp [Rb]; linarith
  have hmove := mul_le_mul_of_nonneg_right (show d - 13 / 16 ≤ ζ by linarith) hs0
  have hext := mul_le_mul_of_nonneg_left hhi hζ
  change moderateExponent d δ (δ * (1 / 2 - y)) R ≤
    moderateExponent d δ (δ * (1 / 2 - y)) Rb at hc
  dsimp only [Rb] at *
  unfold moderateExponent at *
  nlinarith only [hc, he, hmove, hext]

/-- The floor bin uses only the trivial count exponent R <= 1. -/
theorem floor_bin_saving {d q R : ℝ}
    (hd : 0 ≤ d) (hdhi : d ≤ 13 / 16) (hq : q ≤ 1 / 100) (hR : R ≤ 1) :
    moderateExponent d (1 / 50) q R ≤ -(7 / 1200) := by
  have hc := moderateExponent_mono_count hd hR (δ := 1 / 50) (q := q)
  unfold moderateExponent at *
  nlinarith only [hc, hdhi, hq]

/-- The unselected middle count gives the exact manuscript margin. -/
theorem middle_bin_saving {d δ q R : ℝ}
    (hd : 0 ≤ d) (hdhi : d ≤ 1 / 2)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hq : q ≤ δ / 2)
    (hR : R ≤ 76 / 75 - 2 * δ / 3) :
    moderateExponent d δ q R ≤ -(49 / 14400) := by
  have hc := moderateExponent_mono_count hd hR (δ := δ) (q := q)
  have hs0 : 0 ≤ (76 / 75 - 2 * δ / 3) + δ / 2 - 17 / 50 := by linarith
  have hm := mul_le_mul_of_nonneg_right hdhi hs0
  unfold moderateExponent at *
  nlinarith only [hc, hm, hq, hδ1]

/-- Every primitive high/principal margin dominates eight times the same
pretarget saving. Finite later sums may consume part of this reserve. -/
theorem closureSaving_reserves (Δ : ℝ) (J : ℕ) :
    8 * closureSaving Δ J ≤ (51 / 64) * Δ ∧
    8 * closureSaving Δ J ≤ 63 / 800 ∧
    8 * closureSaving Δ J ≤ 23 / 960 ∧
    8 * closureSaving Δ J ≤ 13 / 9600 ∧
    8 * closureSaving Δ J ≤ 7 / (96 * (J : ℝ)) := by
  have h0 := min_le_left ((51 / 64 : ℝ) * Δ)
    (min (63 / 800) (min (23 / 960) (min (13 / 9600) (7 / (96 * (J : ℝ))))))
  have h1 := min_le_right ((51 / 64 : ℝ) * Δ)
    (min (63 / 800) (min (23 / 960) (min (13 / 9600) (7 / (96 * (J : ℝ))))))
  have h2 := min_le_left (63 / 800 : ℝ)
    (min (23 / 960) (min (13 / 9600) (7 / (96 * (J : ℝ)))))
  have h3 := min_le_right (63 / 800 : ℝ)
    (min (23 / 960) (min (13 / 9600) (7 / (96 * (J : ℝ)))))
  have h4 := min_le_left (23 / 960 : ℝ) (min (13 / 9600) (7 / (96 * (J : ℝ))))
  have h5 := min_le_right (23 / 960 : ℝ) (min (13 / 9600) (7 / (96 * (J : ℝ))))
  have h6 := min_le_left (13 / 9600 : ℝ) (7 / (96 * (J : ℝ)))
  have h7 := min_le_right (13 / 9600 : ℝ) (7 / (96 * (J : ℝ)))
  unfold closureSaving
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The actual range bound leaves a six-sigma reserve after the explicitly
budgeted rounding and extension losses. No target occurs in this statement. -/
theorem dynamic_moderate_range_reserved {d δ y Δ ε ζ R : ℝ} (J : ℕ)
    (hd : 0 ≤ d) (hdhi : d ≤ 13 / 16 + ζ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1 / 24)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 12) (hζ : 0 ≤ ζ)
    (hR : R ≤ balancedRowCount δ y + Δ / 4 + ε)
    (hloss : (13 / 16) * ε + 2 * ζ ≤ 2 * closureSaving Δ J) :
    moderateExponent d δ (δ * (1 / 2 - y)) R - Δ ≤
      -(49 / 440640) - 6 * closureSaving Δ J := by
  have h := dynamic_moderate_range_saving hd hdhi hδ0 hδ1 hy0 hy1 hΔ0 hΔ1 hε0 hε1 hζ hR
  have hr := (closureSaving_reserves Δ J).1
  linarith

end HeckeGeneral.Analysis
