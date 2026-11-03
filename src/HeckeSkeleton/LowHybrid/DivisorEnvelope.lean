import HeckeSkeleton.LowHybrid.SquarefreeDivisors
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Actual cutoff envelopes for the squarefree divisor loss

The envelope is the maximum of the divisor counts in a finite norm cutoff.
Its small-power bound is derived from the small-prime argument, rather than
assumed as an independent analytic input.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators
noncomputable section

def divisorCountEnvelope {I : Type*} (cutoff : ℝ → Finset I)
    (divisors : I → Finset I) (X : ℝ) : ℝ :=
  ((cutoff X).sup (fun i => (divisors i).card) : ℕ)

theorem divisorCountEnvelope_nonneg {I : Type*} (cutoff : ℝ → Finset I)
    (divisors : I → Finset I) (X : ℝ) :
    0 ≤ divisorCountEnvelope cutoff divisors X := by
  unfold divisorCountEnvelope
  positivity

/-- The finite maximum bounds the actual divisor count of every member. -/
theorem divisor_count_le_envelope {I : Type*} (cutoff : ℝ → Finset I)
    (divisors : I → Finset I) (X : ℝ) (i : I) (hi : i ∈ cutoff X) :
    ((divisors i).card : ℝ) ≤ divisorCountEnvelope cutoff divisors X := by
  unfold divisorCountEnvelope
  exact Nat.cast_le.mpr (Finset.le_sup (f := fun j => (divisors j).card) hi)

/-- Uniform pointwise divisor bounds pass to the actual cutoff maximum. -/
theorem divisorCountEnvelope_subpower
    {I : Type*} (cutoff : ℝ → Finset I) (divisors : I → Finset I) (normI : I → ℝ)
    (hnorm : ∀ i : I, 0 ≤ normI i)
    (hcutoff : ∀ X : ℝ, 1 ≤ X → ∀ i ∈ cutoff X, normI i ≤ X)
    (hdiv : ∀ eta : ℝ, 0 < eta → ∃ C : ℝ, 0 < C ∧
      ∀ i : I, ((divisors i).card : ℝ) ≤ C * normI i ^ eta) :
    SubpowerBound (divisorCountEnvelope cutoff divisors) := by
  intro eta heta
  obtain ⟨C, hC, hb⟩ := hdiv eta heta
  refine ⟨C, hC, ?_⟩
  intro X hX
  classical
  rcases (cutoff X).eq_empty_or_nonempty with hempty | hne
  · simp only [divisorCountEnvelope, hempty, Finset.sup_empty, bot_eq_zero, Nat.cast_zero]
    exact mul_nonneg (le_of_lt hC) (Real.rpow_nonneg (le_trans zero_le_one hX) eta)
  · obtain ⟨i, hi, heq⟩ :=
      Finset.exists_mem_eq_sup (cutoff X) hne (fun i => (divisors i).card)
    unfold divisorCountEnvelope
    rw [heq]
    exact (hb i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hnorm i) (hcutoff X hX i hi) (le_of_lt heta)) (le_of_lt hC))

/-- The full chain from finite small-prime cutoffs to the required uniform
divisor envelope. No divisor asymptotic is assumed. -/
theorem divisor_envelope_subpower_from_prime_norms
    {I P : Type*} (support : I → Finset P) (divisors : I → Finset I)
    (primeNorm : P → ℝ) (normI : I → ℝ) (cutoff : ℝ → Finset I)
    (hp : ∀ p : P, 1 ≤ primeNorm p)
    (hfinite : ∀ X : ℝ, Set.Finite {p : P | primeNorm p ≤ X})
    (hcard : ∀ i : I, ((divisors i).card : ℝ) ≤ (2 : ℝ) ^ (support i).card)
    (hnorm : ∀ i : I, (∏ p ∈ support i, primeNorm p) ≤ normI i)
    (hcutoff : ∀ X : ℝ, 1 ≤ X → ∀ i ∈ cutoff X, normI i ≤ X) :
    SubpowerBound (divisorCountEnvelope cutoff divisors) := by
  apply divisorCountEnvelope_subpower cutoff divisors normI
  · intro i
    exact (Finset.prod_nonneg (fun p _ => le_trans zero_le_one (hp p))).trans (hnorm i)
  · exact hcutoff
  · exact squarefree_divisor_count_subpower support divisors primeNorm normI hp hfinite hcard hnorm

#print axioms divisor_count_le_envelope
#print axioms divisorCountEnvelope_subpower
#print axioms divisor_envelope_subpower_from_prime_norms

end
end HeckeSkeleton.LowHybrid
