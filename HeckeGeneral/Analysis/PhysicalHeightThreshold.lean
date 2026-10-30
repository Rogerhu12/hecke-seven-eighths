import HeckeGeneral.Analysis.PhysicalHeightComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Source contour estimates need only hold above a fixed positive height.
Clamping the auxiliary analysis height proves the old all-height comparison
without changing the two physical functions. Constants and scale thresholds
may grow; the common saving, height degree and height ceiling do not. -/

noncomputable section
namespace HeckeGeneral.Analysis

open Filter

/-- The source lower cutoff is fixed before the arbitrary external order. -/
def PhysicalHeightComparisonAbove (J f : ℝ → ℂ) (C σ : ℝ) : Prop :=
  ∃ A R ceiling H₀ : ℝ, 0 ≤ A ∧ 0 < ceiling ∧ 1 ≤ H₀ ∧
    ∀ N : ℕ, ∃ k Z₀ : ℝ, 0 < k ∧ 1 ≤ Z₀ ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → H₀ ≤ T → T ≤ Z ^ ceiling →
        ‖J Z - f Z‖ ≤ k *
          (Z ^ (C - 2 * σ) * (1 + T) ^ A + Z ^ R * T ^ (-(N : ℝ)))

theorem PhysicalHeightComparisonAbove.to_comparison
    {J f : ℝ → ℂ} {C σ : ℝ} (h : PhysicalHeightComparisonAbove J f C σ) :
    PhysicalHeightComparison J f C σ := by
  obtain ⟨A, R, ceiling, H₀, hA, hc, hH, hb⟩ := h
  obtain ⟨Zh, hZh⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hc).eventually (eventually_ge_atTop H₀))
  let L : ℝ := (1 + H₀) ^ A
  have hL : 1 ≤ L := Real.one_le_rpow (by linarith) hA
  refine ⟨A, R, ceiling, hA, hc, fun N => ?_⟩
  obtain ⟨k, Z₀, hk, hZ₀, he⟩ := hb N
  refine ⟨k * L, max Z₀ Zh, by positivity, hZ₀.trans (le_max_left _ _), ?_⟩
  intro Z T hZ hT hTc
  have hZm : Z₀ ≤ Z := (le_max_left _ _).trans hZ
  have hZh' : Zh ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZ₀.trans hZm
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTH : H₀ ≤ max H₀ T := le_max_left _ _
  have hTT : T ≤ max H₀ T := le_max_right _ _
  have hcap : max H₀ T ≤ Z ^ ceiling := max_le (hZh Z hZh') hTc
  have hmain : (1 + max H₀ T) ^ A ≤ L * (1 + T) ^ A := by
    have hbase : 1 + max H₀ T ≤ (1 + H₀) * (1 + T) := by
      rcases le_total H₀ T with h | h
      · rw [max_eq_right h]
        nlinarith
      · rw [max_eq_left h]
        nlinarith
    calc
      _ ≤ ((1 + H₀) * (1 + T)) ^ A := Real.rpow_le_rpow (by positivity) hbase hA
      _ = _ := Real.mul_rpow (by linarith) (by linarith)
  have htail : (max H₀ T) ^ (-(N : ℝ)) ≤ T ^ (-(N : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hTpos hTT (neg_nonpos.mpr (Nat.cast_nonneg N))
  have htailL : T ^ (-(N : ℝ)) ≤ L * T ^ (-(N : ℝ)) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hL
      (Real.rpow_nonneg hTpos.le (-(N : ℝ)))
  calc
    _ ≤ k * (Z ^ (C - 2 * σ) * (1 + max H₀ T) ^ A +
        Z ^ R * (max H₀ T) ^ (-(N : ℝ))) := he Z (max H₀ T) hZm hTH hcap
    _ ≤ k * (Z ^ (C - 2 * σ) * (L * (1 + T) ^ A) +
        Z ^ R * (L * T ^ (-(N : ℝ)))) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg hZpos.le _))
        (mul_le_mul_of_nonneg_left (htail.trans htailL) (Real.rpow_nonneg hZpos.le _))) hk.le
    _ = _ := by ring

/-- No equivalence at small scales is claimed. The scale threshold may be
raised when a source estimate is only stated at T > 2. -/
theorem physicalHeightComparisonAbove_iff {J f : ℝ → ℂ} {C σ : ℝ} :
    PhysicalHeightComparisonAbove J f C σ ↔ PhysicalHeightComparison J f C σ := by
  constructor
  · exact PhysicalHeightComparisonAbove.to_comparison
  · rintro ⟨A, R, ceiling, hA, hc, h⟩
    exact ⟨A, R, ceiling, 1, hA, hc, le_refl _, h⟩

/-- Uniform statements in positive tau also apply to arbitrary bounded
analysis heights, via tau=log(T)/log(Z). This does not swap quantifiers. -/
theorem exists_height_power_parameter {Z T ceiling : ℝ}
    (hZ : 1 < Z) (hT : 1 < T) (hTc : T ≤ Z ^ ceiling) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ ceiling ∧ Z ^ τ = T := by
  have hZpos : 0 < Z := lt_trans zero_lt_one hZ
  have hTpos : 0 < T := lt_trans zero_lt_one hT
  have hlogZ : 0 < Real.log Z := Real.log_pos hZ
  let τ := Real.log T / Real.log Z
  have hτ : 0 < τ := div_pos (Real.log_pos hT) hlogZ
  have he : Z ^ τ = T := (Real.mul_log_eq_log_iff hZpos hTpos).mp
    (div_mul_cancel₀ _ hlogZ.ne')
  have hτc : τ ≤ ceiling := (Real.rpow_le_rpow_left_iff hZ).mp (he ▸ hTc)
  exact ⟨τ, hτ, hτc, he⟩

end HeckeGeneral.Analysis
