import HeckeGeneral.Analysis.PhysicalHeightComparison

/-! Assembly of a retained error and an external contour tail.
The functions J and f do not depend on height. The error decomposition may
depend on height but not on the requested external decay order. All height
degrees and scale exponents are chosen before that order. These are proved
consumers of actual estimates, not definitions of T or of its conclusion. -/

noncomputable section
namespace HeckeGeneral.Analysis

/-- A fixed polynomial height cost with arbitrary external tail decay. -/
def HeightTailBound (E : ℝ → ℝ → ℂ) : Prop :=
  ∃ A R ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ N : ℕ, ∃ k Z₀ : ℝ, 0 < k ∧ 1 ≤ Z₀ ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → T ≤ Z ^ ceiling →
        ‖E Z T‖ ≤ k * Z ^ R * (1 + T) ^ A * T ^ (-(N : ℝ))

/-- Absorbing the fixed height degree changes only the externally requested
order and its constant. The scale exponent and height ceiling are intact. -/
theorem HeightTailBound.without_height_degree {E : ℝ → ℝ → ℂ}
    (h : HeightTailBound E) :
    ∃ R ceiling : ℝ, 0 < ceiling ∧
      ∀ N : ℕ, ∃ k Z₀ : ℝ, 0 < k ∧ 1 ≤ Z₀ ∧
        ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → T ≤ Z ^ ceiling →
          ‖E Z T‖ ≤ k * Z ^ R * T ^ (-(N : ℝ)) := by
  obtain ⟨A, R, ceiling, hA, hceiling, hb⟩ := h
  obtain ⟨M, hM⟩ := exists_nat_gt A
  refine ⟨R, ceiling, hceiling, fun N => ?_⟩
  obtain ⟨k, Z₀, hk, hZ₀, he⟩ := hb (N + M)
  refine ⟨k * (2 : ℝ) ^ A, Z₀, by positivity, hZ₀, ?_⟩
  intro Z T hZ hT hTc
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one (hZ₀.trans hZ)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hcost : (1 + T) ^ A ≤ (2 : ℝ) ^ A * T ^ A := by
    calc
      _ ≤ (2 * T) ^ A := Real.rpow_le_rpow (by positivity) (by linarith) hA
      _ = _ := Real.mul_rpow (by norm_num) hTpos.le
  have hdecay : T ^ A * T ^ (-((N + M : ℕ) : ℝ)) ≤ T ^ (-(N : ℝ)) := by
    rw [← Real.rpow_add hTpos]
    apply Real.rpow_le_rpow_of_exponent_le hT
    simp only [Nat.cast_add]
    linarith
  calc
    _ ≤ k * Z ^ R * (1 + T) ^ A * T ^ (-((N + M : ℕ) : ℝ)) := he Z T hZ hT hTc
    _ ≤ k * Z ^ R * ((2 : ℝ) ^ A * T ^ A) * T ^ (-((N + M : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost (by positivity))
        (Real.rpow_nonneg hTpos.le _)
    _ = (k * (2 : ℝ) ^ A * Z ^ R) *
        (T ^ A * T ^ (-((N + M : ℕ) : ℝ))) := by ring
    _ ≤ (k * (2 : ℝ) ^ A * Z ^ R) * T ^ (-(N : ℝ)) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)

/-- Exact height-dependent error decomposition plus retained and tail
bounds gives the previously defined finite-height comparison. -/
theorem PhysicalHeightComparison.of_main_and_tail
    {J f : ℝ → ℂ} {E Q : ℝ → ℝ → ℂ} {C σ : ℝ}
    (hdecomp : ∀ Z T : ℝ, 1 ≤ Z → 1 ≤ T → J Z - f Z = E Z T + Q Z T)
    (hmain : ∃ A ceiling k Z₀ : ℝ, 0 ≤ A ∧ 0 < ceiling ∧ 0 < k ∧ 1 ≤ Z₀ ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → T ≤ Z ^ ceiling →
        ‖E Z T‖ ≤ k * Z ^ (C - 2 * σ) * (1 + T) ^ A)
    (htail : HeightTailBound Q) : PhysicalHeightComparison J f C σ := by
  obtain ⟨A, ceiling, k, Z₀, hA, hc, hk, hZ₀, hE⟩ := hmain
  obtain ⟨R, tailCeiling, htc, hQ⟩ := htail.without_height_degree
  refine ⟨A, R, min ceiling tailCeiling, hA, lt_min hc htc, fun N => ?_⟩
  obtain ⟨kt, Zt, hkt, hZt, ht⟩ := hQ N
  refine ⟨k + kt, max Z₀ Zt, by linarith, le_trans hZ₀ (le_max_left _ _), ?_⟩
  intro Z T hZ hT hTc
  have hZmain := le_trans (le_max_left _ _) hZ
  have hZtail := le_trans (le_max_right _ _) hZ
  have hZ1 := hZ₀.trans hZmain
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTm : T ≤ Z ^ ceiling := hTc.trans
    (Real.rpow_le_rpow_of_exponent_le hZ1 (min_le_left _ _))
  have hTt : T ≤ Z ^ tailCeiling := hTc.trans
    (Real.rpow_le_rpow_of_exponent_le hZ1 (min_le_right _ _))
  rw [hdecomp Z T hZ1 hT]
  calc
    _ ≤ ‖E Z T‖ + ‖Q Z T‖ := norm_add_le _ _
    _ ≤ k * Z ^ (C - 2 * σ) * (1 + T) ^ A + kt * Z ^ R * T ^ (-(N : ℝ)) :=
      add_le_add (hE Z T hZmain hT hTm) (ht Z T hZtail hT hTt)
    _ ≤ (k + kt) * (Z ^ (C - 2 * σ) * (1 + T) ^ A + Z ^ R * T ^ (-(N : ℝ))) := by
      have h₁ : 0 ≤ k * (Z ^ R * T ^ (-(N : ℝ))) := by positivity
      have h₂ : 0 ≤ kt * (Z ^ (C - 2 * σ) * (1 + T) ^ A) := by positivity
      nlinarith only [h₁, h₂]

end HeckeGeneral.Analysis
