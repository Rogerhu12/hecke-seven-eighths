import HeckeGeneral.Analysis.TargetHeightChoice
import HeckeGeneral.Analysis.MellinZeroDetector

/-!
M Section 7: absorb the target-dependent height degree and tail by choosing
tau after a common saving and N after tau. The two height-free physical
functions are fixed throughout. This is a consumer of the precise physical
comparison estimate, not a definition of T or a proof of its transfer.
-/

noncomputable section
namespace HeckeGeneral.Analysis

open Filter Asymptotics Set MeasureTheory
open scoped Topology

/-- The source's estimate before height removal. The degree, remainder
exponent and permitted ceiling are chosen before the arbitrary tail order.
Constants and thresholds may depend on that order. -/
def PhysicalHeightComparison (J f : ℝ → ℂ) (C σ : ℝ) : Prop :=
  ∃ A R ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ N : ℕ, ∃ k Z₀ : ℝ, 0 < k ∧ 1 ≤ Z₀ ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → T ≤ Z ^ ceiling →
        ‖J Z - f Z‖ ≤ k *
          (Z ^ (C - 2 * σ) * (1 + T) ^ A + Z ^ R * T ^ (-(N : ℝ)))

theorem PhysicalHeightComparison.isBigO {J f : ℝ → ℂ} {C σ : ℝ}
    (hσ : 0 < σ) (h : PhysicalHeightComparison J f C σ) :
    (fun Z => J Z - f Z) =O[atTop] (fun Z : ℝ => Z ^ (C - σ)) := by
  obtain ⟨A, R, ceiling, hA, hceiling, hbound⟩ := h
  obtain ⟨τ, hτ, hτc, hfirst, N, htail⟩ :=
    exists_target_height_and_tail_order hσ hceiling A R C hA
  obtain ⟨k, Z₀, hk, hZ₀, hbound⟩ := hbound N
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨k * ((2 : ℝ) ^ A + 1), ?_⟩
  filter_upwards [eventually_ge_atTop Z₀] with Z hZ
  have hZ1 : 1 ≤ Z := hZ₀.trans hZ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
  have hT1 : 1 ≤ Z ^ τ := Real.one_le_rpow hZ1 hτ.le
  have hTpos : 0 < Z ^ τ := Real.rpow_pos_of_pos hZpos _
  have hTc : Z ^ τ ≤ Z ^ ceiling := Real.rpow_le_rpow_of_exponent_le hZ1 hτc.le
  have hh := hbound Z (Z ^ τ) hZ hT1 hTc
  have hgrowth : (1 + Z ^ τ) ^ A ≤ (2 : ℝ) ^ A * Z ^ (A * τ) := by
    calc
      _ ≤ (2 * Z ^ τ) ^ A := Real.rpow_le_rpow (by positivity) (by linarith) hA
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hTpos.le,
          ← Real.rpow_mul hZpos.le]
        congr 2
        ring
  have hfirst' : Z ^ (C - 2 * σ) * (1 + Z ^ τ) ^ A ≤
      (2 : ℝ) ^ A * Z ^ (C - σ) := by
    calc
      _ ≤ Z ^ (C - 2 * σ) * ((2 : ℝ) ^ A * Z ^ (A * τ)) :=
        mul_le_mul_of_nonneg_left hgrowth (Real.rpow_nonneg hZpos.le _)
      _ = (2 : ℝ) ^ A * Z ^ (C - 2 * σ + A * τ) := by
        rw [Real.rpow_add hZpos]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hfirst) (Real.rpow_nonneg (by norm_num) _)
  have htail' : Z ^ R * (Z ^ τ) ^ (-(N : ℝ)) ≤ Z ^ (C - σ) := by
    rw [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos]
    apply Real.rpow_le_rpow_of_exponent_le hZ1
    nlinarith [htail]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hZpos.le _)]
  calc
    _ ≤ k * (Z ^ (C - 2 * σ) * (1 + Z ^ τ) ^ A +
        Z ^ R * (Z ^ τ) ^ (-(N : ℝ))) := hh
    _ ≤ k * ((2 : ℝ) ^ A * Z ^ (C - σ) + Z ^ (C - σ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst' htail') hk.le
    _ = _ := by ring

theorem physicalProbeBound_of_low_and_heightComparison
    {J f : ℝ → ℂ} {B σ : ℝ}
    (hσ : 0 < σ) (hσsmall : σ < (B - 7 / 8) / 2)
    (hlow : ∀ ε : ℝ, 0 < ε → J =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + ε)))
    (hhigh : PhysicalHeightComparison J f (B - 11 / 16) σ)
    (hloc : LocallyIntegrableOn f (Ioi 0))
    (hsmall : ∀ N : ℝ, f =O[𝓝[>] 0] (fun Z : ℝ => Z ^ N)) :
    PhysicalProbeBound f (B - σ) := by
  have hlow' := hlow ((B - 7 / 8) / 2) (by linarith)
  have hp : (fun Z : ℝ => Z ^ (3 / 16 + (B - 7 / 8) / 2))
      =O[atTop] (fun Z : ℝ => Z ^ (B - σ - 11 / 16)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Z hZ
    simp only [Real.norm_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one hZ) _), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hh : (fun Z => J Z - f Z) =O[atTop] (fun Z : ℝ => Z ^ (B - σ - 11 / 16)) := by
    simpa only [show B - 11 / 16 - σ = B - σ - 11 / 16 by ring] using hhigh.isBigO hσ
  refine ⟨hloc, ?_, hsmall⟩
  simpa only [sub_sub_cancel] using (hlow'.trans hp).sub hh

end HeckeGeneral.Analysis
