import HeckeGeneral.Analysis.MomentInputs
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Finite character expansions preserve a strong constituent witness with an
explicit cardinality loss. This is the consumer needed before applying a
single-character moment to the finite ray-character expansion of a probe.
No character expansion or admissibility of a constituent is assumed proved.
-/

noncomputable section
namespace HeckeGeneral.Analysis

open scoped Classical BigOperators

theorem exists_norm_sum_le_card_mul {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (hne : S.Nonempty) :
    ∃ i ∈ S, ‖∑ j ∈ S, z j‖ ≤ (S.card : ℝ) * ‖z i‖ := by
  obtain ⟨i, hi, hmax⟩ := S.exists_max_image (fun i => ‖z i‖) hne
  refine ⟨i, hi, (norm_sum_le S z).trans ?_⟩
  calc
    (∑ j ∈ S, ‖z j‖) ≤ ∑ j ∈ S, ‖z i‖ := Finset.sum_le_sum hmax
    _ = (S.card : ℝ) * ‖z i‖ := by simp

/-- The bound is on squared norms, matching both the inverse and paired
moment interfaces. The size loss is kept outside the power of Z. -/
theorem exists_sq_norm_constituent {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (hne : S.Nonempty) :
    ∃ i ∈ S, ‖∑ j ∈ S, z j‖ ^ 2 ≤ (S.card : ℝ) ^ 2 * ‖z i‖ ^ 2 := by
  obtain ⟨i, hi, h⟩ := exists_norm_sum_le_card_mul S z hne
  refine ⟨i, hi, ?_⟩
  have hn : 0 ≤ (S.card : ℝ) * ‖z i‖ := by positivity
  have hs := sq_le_sq₀ (norm_nonneg _) hn |>.mpr h
  simpa [mul_pow] using hs

/-- This form accommodates a different finite character list in every
slot, including the zero-slot product. The literal expansion is used. -/
theorem exists_product_expansion_witness {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)]
    (z : ∀ i, κ i → ℂ) :
    ∃ a : ∀ i, κ i,
      ‖∏ i, ∑ j, z i j‖ ^ 2 ≤
        (Fintype.card (∀ i, κ i) : ℝ) ^ 2 * ‖∏ i, z i (a i)‖ ^ 2 := by
  classical
  have he : (∏ i, ∑ j, z i j) = ∑ a : ∀ i, κ i, ∏ i, z i (a i) :=
    Fintype.prod_sum z
  rw [he]
  obtain ⟨a, _, ha⟩ := exists_sq_norm_constituent Finset.univ
    (fun a : ∀ i, κ i => ∏ i, z i (a i)) Finset.univ_nonempty
  exact ⟨a, by simpa using ha⟩

end HeckeGeneral.Analysis
