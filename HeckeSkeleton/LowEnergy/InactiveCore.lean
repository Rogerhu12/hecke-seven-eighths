import HeckeSkeleton.LowEnergy.TupleCore
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Inactive coefficients: exact separation and L1 assembly

The inactive reciprocal-prime factors stay in the coefficient outside the
active row sum.  The outer energy costs the square of their total absolute
mass, and never the cardinality of the inactive tuple set.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.InactiveCore
open HeckeSkeleton.LowEnergy.TupleCore
open scoped BigOperators Classical

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

theorem prod_join (P : ι → Prop) [DecidablePred P]
    (a : {i // P i} → α) (b : {i // ¬P i} → α) (w : ι → α → ℂ) :
    (∏ i, w i (join P a b i)) =
      (∏ i : {i // P i}, w i (a i)) *
        ∏ i : {i // ¬P i}, w i (b i) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype P]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [join_of_true P a b i i.property]
  · apply Finset.prod_congr rfl
    intro i _
    rw [join_of_false P a b i i.property]

/-- Exact splitting of the physical weights and the inactive prefactor.
The inactive tuple is the outer variable.  The active sum remains linear. -/
theorem weighted_sum_piFinset_split (W : ι → Finset α) (P : ι → Prop)
    [DecidablePred P] (w v : ι → α → ℂ) (f : (ι → α) → ℂ) :
    (∑ t ∈ Fintype.piFinset W,
      (∏ i, w i (t i)) * (∏ i : {i // ¬P i}, v i (t i)) * f t) =
      ∑ b ∈ Fintype.piFinset (fun i : {i // ¬P i} => W i),
        (∏ i : {i // ¬P i}, w i (b i) * v i (b i)) *
          ∑ a ∈ Fintype.piFinset (fun i : {i // P i} => W i),
            (∏ i : {i // P i}, w i (a i)) * f (join P a b) := by
  rw [sum_piFinset_split W P, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hinactive :
      (∏ i : {i // ¬P i}, v i (join P a b i)) =
        ∏ i : {i // ¬P i}, v i (b i) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [join_of_false P a b i i.property]
  rw [prod_join, hinactive, Finset.prod_mul_distrib]
  ring

/-- The absolute tuple mass factorizes exactly over its slots. -/
theorem tuple_l1_mass (W : ι → Finset α) (a : ι → α → ℂ) :
    (∑ t ∈ Fintype.piFinset W, ‖∏ i, a i (t i)‖) =
      ∏ i, ∑ x ∈ W i, ‖a i x‖ := by
  simp_rw [norm_prod]
  exact (Finset.prod_univ_sum W (fun i x => ‖a i x‖)).symm

theorem tuple_l1_mass_le (W : ι → Finset α) (a : ι → α → ℂ)
    (C : ι → ℝ) (hC : ∀ i, ∑ x ∈ W i, ‖a i x‖ ≤ C i) :
    (∑ t ∈ Fintype.piFinset W, ‖∏ i, a i (t i)‖) ≤ ∏ i, C i := by
  rw [tuple_l1_mass]
  exact Finset.prod_le_prod₀
    (fun i _ => Finset.sum_nonneg (fun x _ => norm_nonneg _)) (fun i _ => hC i)

theorem tuple_l1_mass_le_pow (W : ι → Finset α) (a : ι → α → ℂ)
    {C : ℝ} (hC : ∀ i, ∑ x ∈ W i, ‖a i x‖ ≤ C) :
    (∑ t ∈ Fintype.piFinset W, ‖∏ i, a i (t i)‖) ≤ C ^ Fintype.card ι := by
  simpa only [Finset.prod_const, Finset.card_univ] using
    tuple_l1_mass_le W a (fun _ => C) hC

/-- Finite weighted Minkowski in squared form.  The outer cost is the L1
mass squared.  Every inner energy uses the same row set, while coefficients
and rows may depend on the outer index. -/
theorem finite_weighted_energy_le {η κ : Type*} (s : Finset η) (rows : Finset κ)
    (a : η → ℂ) (v : η → κ → ℂ) {E : ℝ}
    (hE : ∀ i ∈ s, (∑ k ∈ rows, ‖v i k‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ i ∈ s, a i * v i k‖ ^ 2) ≤
      (∑ i ∈ s, ‖a i‖) ^ 2 * E := by
  have hmass : 0 ≤ ∑ i ∈ s, ‖a i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hpoint (k : κ) :
      ‖∑ i ∈ s, a i * v i k‖ ^ 2 ≤
        (∑ i ∈ s, ‖a i‖) * ∑ i ∈ s, ‖a i‖ * ‖v i k‖ ^ 2 := by
    have hn : ‖∑ i ∈ s, a i * v i k‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖v i k‖ := by
      simpa only [norm_mul] using norm_sum_le s (fun i => a i * v i k)
    calc
      ‖∑ i ∈ s, a i * v i k‖ ^ 2 ≤
          (∑ i ∈ s, ‖a i‖ * ‖v i k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ (∑ i ∈ s, ‖a i‖) * ∑ i ∈ s, ‖a i‖ * ‖v i k‖ ^ 2 := by
        apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
          (fun i _ => norm_nonneg (a i))
          (fun i _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
        intro i _
        exact le_of_eq (by ring)
  calc
    (∑ k ∈ rows, ‖∑ i ∈ s, a i * v i k‖ ^ 2) ≤
        ∑ k ∈ rows, (∑ i ∈ s, ‖a i‖) *
          ∑ i ∈ s, ‖a i‖ * ‖v i k‖ ^ 2 :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = (∑ i ∈ s, ‖a i‖) *
        ∑ i ∈ s, ‖a i‖ * (∑ k ∈ rows, ‖v i k‖ ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.mul_sum rows (fun k => ‖v i k‖ ^ 2) ‖a i‖).symm
    _ ≤ (∑ i ∈ s, ‖a i‖) * ∑ i ∈ s, ‖a i‖ * E :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i hi =>
          mul_le_mul_of_nonneg_left (hE i hi) (norm_nonneg _))) hmass
    _ = (∑ i ∈ s, ‖a i‖) ^ 2 * E := by
      rw [← Finset.sum_mul]
      ring

theorem finite_weighted_energy_le_of_mass {η κ : Type*}
    (s : Finset η) (rows : Finset κ) (a : η → ℂ) (v : η → κ → ℂ)
    {M E : ℝ} (hE0 : 0 ≤ E)
    (hM : (∑ i ∈ s, ‖a i‖) ≤ M)
    (hE : ∀ i ∈ s, (∑ k ∈ rows, ‖v i k‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ i ∈ s, a i * v i k‖ ^ 2) ≤ M ^ 2 * E := by
  refine (finite_weighted_energy_le s rows a v hE).trans ?_
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => norm_nonneg _)) hM 2) hE0

#print axioms weighted_sum_piFinset_split
#print axioms tuple_l1_mass
#print axioms finite_weighted_energy_le
#print axioms finite_weighted_energy_le_of_mass

end HeckeSkeleton.LowEnergy.InactiveCore
