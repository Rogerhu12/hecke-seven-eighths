import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! Exact finite aggregation on disjoint original-row fibres. -/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.FiniteFiberEnergy
open scoped Classical BigOperators

theorem sum_eq_fibres {Row Label : Type*} [DecidableEq Label] (R : Finset Row)
    (label : Row → Label) (E : Row → ℝ) :
    (∑ r ∈ R, E r) =
      ∑ a ∈ R.image label, ∑ r ∈ R.filter (fun r => label r = a), E r := by
  exact (Finset.sum_fiberwise_of_maps_to
    (fun r hr => Finset.mem_image_of_mem label hr) E).symm

theorem sum_le_fibre_majorants {Row Label : Type*} [DecidableEq Label] (R : Finset Row)
    (label : Row → Label) (E : Row → ℝ) (W : Label → ℝ)
    (h : ∀ a ∈ R.image label,
      (∑ r ∈ R.filter (fun r => label r = a), E r) ≤ W a) :
    (∑ r ∈ R, E r) ≤ ∑ a ∈ R.image label, W a := by
  rw [sum_eq_fibres R label E]
  exact Finset.sum_le_sum h

/-- A shell index partitions the original rows. Its cost is its number of
possible values, rather than a Cauchy loss from treating it as an amplitude
index. The statement applies directly to `E r = ‖amplitude r‖²`. -/
theorem fibre_bound_from_shells {Row Label : Type*} [DecidableEq Label] (R : Finset Row)
    (label : Row → Label) (shell : Row → ℕ) (E : Row → ℝ)
    (N : ℕ) (hshell : ∀ r ∈ R, shell r < N)
    (W : Label → ℝ)
    (h : ∀ a ∈ R.image label, ∀ j ∈ Finset.range N,
      (∑ r ∈ R.filter (fun r => label r = a ∧ shell r = j), E r) ≤ W a) :
    ∀ a ∈ R.image label,
      (∑ r ∈ R.filter (fun r => label r = a), E r) ≤ (N : ℝ) * W a := by
  intro a ha
  have hm : ∀ r ∈ R.filter (fun r => label r = a), shell r ∈ Finset.range N := by
    intro r hr
    exact Finset.mem_range.mpr (hshell r (Finset.mem_filter.mp hr).1)
  rw [← Finset.sum_fiberwise_of_maps_to hm E]
  calc
    _ ≤ ∑ _j ∈ Finset.range N, W a := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Finset.filter_filter] using h a ha j hj
    _ = (N : ℝ) * W a := by simp

theorem sum_le_shell_majorants {Row Label : Type*} [DecidableEq Label] (R : Finset Row)
    (label : Row → Label) (shell : Row → ℕ) (E : Row → ℝ)
    (N : ℕ) (hshell : ∀ r ∈ R, shell r < N)
    (W : Label → ℝ)
    (h : ∀ a ∈ R.image label, ∀ j ∈ Finset.range N,
      (∑ r ∈ R.filter (fun r => label r = a ∧ shell r = j), E r) ≤ W a) :
    (∑ r ∈ R, E r) ≤ (N : ℝ) * ∑ a ∈ R.image label, W a := by
  have hb := fibre_bound_from_shells R label shell E N hshell W h
  calc
    _ ≤ ∑ a ∈ R.image label, (N : ℝ) * W a :=
      sum_le_fibre_majorants R label E (fun a => (N : ℝ) * W a) hb
    _ = _ := (Finset.mul_sum ..).symm

#print axioms sum_eq_fibres
#print axioms sum_le_shell_majorants

end HeckeSkeleton.LowEnergy.FiniteFiberEnergy
