import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
An exact finite-sum obstruction to recovering individual piece estimates
from aggregate identities. The construction keeps the indexing set and
the sum unchanged. For a set containing two distinct indices, one piece
can be prescribed arbitrarily; another piece absorbs the difference.

This is a structural audit, not a counterexample to any canonically
constructed contour decomposition.
-/

set_option autoImplicit false
noncomputable section

namespace HighBinVerified.FinitePieceGauge

open scoped Classical BigOperators

variable {Row : Type*}

/-- Replace the value at `u` and compensate at the distinct index `v`. -/
def replacePair (f : Row → ℂ) (u v : Row) (z : ℂ) (x : Row) : ℂ :=
  f x + (if x = u then z - f u else 0) -
    (if x = v then z - f u else 0)

theorem replacePair_left (f : Row → ℂ) (u v : Row) (z : ℂ) (huv : u ≠ v) :
    replacePair f u v z u = z := by
  unfold replacePair
  rw [ite_eq_left rfl, ite_eq_right huv, sub_zero,
    ← add_sub_assoc, add_comm (f u) z, add_sub_cancel_right]

/-- The signed sum is unchanged even though the individual norms need not be. -/
theorem sum_replacePair (F : Finset Row) (f : Row → ℂ)
    (u v : Row) (hu : u ∈ F) (hv : v ∈ F) (z : ℂ) :
    (∑ x ∈ F, replacePair f u v z x) = ∑ x ∈ F, f x := by
  classical
  simp only [replacePair, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', ite_eq_left hu, ite_eq_left hv, add_sub_cancel_right]

theorem pair_exists (F : Finset Row) (hF : 2 ≤ F.card) :
    ∃ p : Row × Row, p.1 ∈ F ∧ p.2 ∈ F ∧ p.1 ≠ p.2 := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hF
  exact ⟨(u, v), hu, hv, huv⟩

/-- A pair chosen from the original finite set; no new indices are inserted. -/
def chosenPair (F : Finset Row) (hF : 2 ≤ F.card) : Row × Row :=
  Classical.choose (pair_exists F hF)

theorem chosenPair_spec (F : Finset Row) (hF : 2 ≤ F.card) :
    (chosenPair F hF).1 ∈ F ∧ (chosenPair F hF).2 ∈ F ∧
      (chosenPair F hF).1 ≠ (chosenPair F hF).2 :=
  Classical.choose_spec (pair_exists F hF)

/-- Total finite-piece replacement. Singletons and empty sets are unchanged. -/
def prescribePiece (F : Finset Row) (f : Row → ℂ) (z : ℂ) : Row → ℂ :=
  if hF : 2 ≤ F.card then
    replacePair f (chosenPair F hF).1 (chosenPair F hF).2 z
  else f

theorem sum_prescribePiece (F : Finset Row) (f : Row → ℂ) (z : ℂ) :
    (∑ x ∈ F, prescribePiece F f z x) = ∑ x ∈ F, f x := by
  classical
  unfold prescribePiece
  split_ifs with hF
  · exact sum_replacePair F f _ _ (chosenPair_spec F hF).1
      (chosenPair_spec F hF).2.1 z
  · rfl

theorem prescribePiece_chosen (F : Finset Row) (f : Row → ℂ) (z : ℂ)
    (hF : 2 ≤ F.card) :
    prescribePiece F f z (chosenPair F hF).1 = z := by
  rw [prescribePiece, dite_eq_left hF]
  exact replacePair_left f _ _ z (chosenPair_spec F hF).2.2

theorem norm_le_sum_norm_prescribePiece (F : Finset Row) (f : Row → ℂ)
    (z : ℂ) (hF : 2 ≤ F.card) :
    ‖z‖ ≤ ∑ x ∈ F, ‖prescribePiece F f z x‖ := by
  calc
    ‖z‖ = ‖prescribePiece F f z (chosenPair F hF).1‖ :=
      congrArg norm (prescribePiece_chosen F f z hF).symm
    _ ≤ _ := Finset.single_le_sum
      (fun x _hx => norm_nonneg (prescribePiece F f z x)) (chosenPair_spec F hF).1

/-- No finite bound for the sum of norms follows from this one sum identity. -/
theorem exists_same_sum_larger_norm (F : Finset Row) (f : Row → ℂ)
    (hF : 2 ≤ F.card) (M : ℝ) :
    ∃ f' : Row → ℂ,
      (∑ x ∈ F, f' x) = (∑ x ∈ F, f x) ∧ M < ∑ x ∈ F, ‖f' x‖ := by
  let z : ℂ := (max M 0 + 1 : ℝ)
  refine ⟨prescribePiece F f z, sum_prescribePiece F f z, ?_⟩
  have hz : ‖z‖ = max M 0 + 1 := by
    change ‖((max M 0 + 1 : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    linarith [le_max_right M 0]
  have hM : M < ‖z‖ := by
    rw [hz]
    linarith [le_max_left M 0]
  exact hM.trans_le (norm_le_sum_norm_prescribePiece F f z hF)

end HighBinVerified.FinitePieceGauge

#print axioms HighBinVerified.FinitePieceGauge.sum_prescribePiece
#print axioms HighBinVerified.FinitePieceGauge.norm_le_sum_norm_prescribePiece
#print axioms HighBinVerified.FinitePieceGauge.exists_same_sum_larger_norm
