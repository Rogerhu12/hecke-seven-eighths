import HeckeSkeleton.LowEnergy.AnnularEnergy

/-! Finite weighted Minkowski for the literal original row vectors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalHilbert

open scoped Classical BigOperators

theorem finite_sum_energy {ι κ : Type*} (blocks : Finset ι) (rows : Finset κ)
    (piece : ι → κ → ℂ) (amplitude : ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (ha : ∀ i ∈ blocks, 0 ≤ amplitude i)
    (hpiece : ∀ i ∈ blocks, (∑ k ∈ rows, ‖piece i k‖ ^ 2) ≤ amplitude i ^ 2 * B) :
    (∑ k ∈ rows, ‖∑ i ∈ blocks, piece i k‖ ^ 2) ≤
      (∑ i ∈ blocks, amplitude i) ^ 2 * B := by
  have h := HeckeSkeleton.LowEnergy.AnnularEnergy.finite_rows_minkowski rows
    (fun i : blocks => piece i.val) (fun i : blocks => amplitude i.val) B
    (fun i => ha i.val i.property) hB (Summable.of_finite)
    (fun i => hpiece i.val i.property)
  have hsum (k : κ) : (∑' i : blocks, piece i.val k) =
      ∑ i ∈ blocks, piece i k := by
    rw [tsum_fintype]
    exact Finset.sum_coe_sort blocks (fun i => piece i k)
  simp_rw [hsum] at h
  simpa only [tsum_fintype, Finset.sum_coe_sort] using h

/-- Both a row-dependent bounded phase and an independent arithmetic
amplitude are retained before the positive Hilbert-space estimate. -/
theorem finite_coefficient_energy {ι κ : Type*} (blocks : Finset ι) (rows : Finset κ)
    (coefficient piece : ι → κ → ℂ) (weight amplitude : ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hw : ∀ i ∈ blocks, 0 ≤ weight i)
    (ha : ∀ i ∈ blocks, 0 ≤ amplitude i)
    (hc : ∀ i ∈ blocks, ∀ k ∈ rows, ‖coefficient i k‖ ≤ weight i)
    (hpiece : ∀ i ∈ blocks, (∑ k ∈ rows, ‖piece i k‖ ^ 2) ≤ amplitude i ^ 2 * B) :
    (∑ k ∈ rows, ‖∑ i ∈ blocks, coefficient i k * piece i k‖ ^ 2) ≤
      (∑ i ∈ blocks, weight i * amplitude i) ^ 2 * B := by
  apply finite_sum_energy blocks rows (fun i k => coefficient i k * piece i k)
    (fun i => weight i * amplitude i) B hB (fun i hi => mul_nonneg (hw i hi) (ha i hi))
  intro i hi
  calc
    _ ≤ ∑ k ∈ rows, weight i ^ 2 * ‖piece i k‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hc i hi k hk) 2) (sq_nonneg _)
    _ = weight i ^ 2 * ∑ k ∈ rows, ‖piece i k‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ weight i ^ 2 * (amplitude i ^ 2 * B) :=
      mul_le_mul_of_nonneg_left (hpiece i hi) (sq_nonneg _)
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalHilbert

end
