import HeckePort.Moments.Descent.IdealMasks
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The actual nonempty-subset allocation mass

For every prime in the literal `primeSupport D`, the allocation records a
nonempty subset of the `k` factor occurrences.  Its index set is exactly
the product of the nonempty-powerset indices in the divisor
inclusion-exclusion formula.  Its cardinality is `(2^k - 1)^ω(D)`.

The bound is uniform for `k ≤ N`: the constant is chosen before the ideal
and the number of occurrences.  It holds for every nonzero ideal, hence
in particular for the squarefree divisors used in the engine.  Filtering
this actual family by divisibility or compatibility conditions only
decreases its cardinality and its signed inclusion-exclusion mass.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.AllocationMass

open NumberField HeckePort.IdealMobiusDivisorSum

/-- The literal nonempty subset index in one prime's inclusion-exclusion. -/
def choices (k : ℕ) : Finset (Finset (Fin k)) :=
  (Finset.univ : Finset (Fin k)).powerset.filter Finset.Nonempty

theorem choices_eq_erase (k : ℕ) :
    choices k = (Finset.univ : Finset (Fin k)).powerset.erase ∅ := by
  ext J
  simp [choices, Finset.nonempty_iff_ne_empty, and_comm]

@[simp] theorem card_choices (k : ℕ) : (choices k).card = 2 ^ k - 1 := by
  rw [choices_eq_erase, Finset.card_erase_of_mem (Finset.empty_mem_powerset _)]
  simp

/-- One independent, nonempty occurrence subset for every actual prime. -/
def allocations {ι : Type*} (P : Finset ι) (k : ℕ) :
    Finset (P → Finset (Fin k)) :=
  Fintype.piFinset (fun _p : P => choices k)

@[simp] theorem mem_allocations {ι : Type*} (P : Finset ι) (k : ℕ)
    (v : P → Finset (Fin k)) :
    v ∈ allocations P k ↔ ∀ p, (v p).Nonempty := by
  simp [allocations, choices, Fintype.mem_piFinset]

@[simp] theorem card_allocations {ι : Type*} (P : Finset ι) (k : ℕ) :
    (allocations P k).card = (2 ^ k - 1) ^ P.card := by
  simp [allocations]

theorem card_allocations_le {ι : Type*} (P : Finset ι) (k : ℕ) :
    (allocations P k).card ≤ (2 ^ P.card) ^ k := by
  rw [card_allocations]
  calc
    (2 ^ k - 1) ^ P.card ≤ (2 ^ k) ^ P.card :=
      Nat.pow_le_pow_left (Nat.sub_le _ _) _
    _ = (2 ^ P.card) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The product of the actual inclusion-exclusion signs. -/
def sign {ι : Type*} (P : Finset ι) {k : ℕ} (v : P → Finset (Fin k)) : ℂ :=
  ∏ p : P, (-1 : ℂ) ^ ((v p).card + 1)

@[simp] theorem norm_sign {ι : Type*} (P : Finset ι) {k : ℕ}
    (v : P → Finset (Fin k)) : ‖sign P v‖ = 1 := by
  simp [sign, norm_prod]

theorem sum_norm_sign {ι : Type*} (P : Finset ι) {k : ℕ}
    (T : Finset (P → Finset (Fin k))) :
    (∑ v ∈ T, ‖sign P v‖) = (T.card : ℝ) := by
  simp

variable {K : Type*} [Field K] [NumberField K]

/-- Allocations on the literal support of the actual squarefree divisor. -/
def idealAllocations (D : Ideal (𝓞 K)) (k : ℕ) :
    Finset (primeSupport D → Finset (Fin k)) := allocations (primeSupport D) k

theorem idealAllocations_card (D : Ideal (𝓞 K)) (k : ℕ) :
    (idealAllocations D k).card = (2 ^ k - 1) ^ (primeSupport D).card :=
  card_allocations _ _

/-- Uniform subpower cost of all actual allocations, including `k = 0`.
The constant depends on the fixed occurrence bound, never on the divisor. -/
theorem ideal_allocation_card_bound (K : Type*) [Field K] [NumberField K]
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal (𝓞 K)), D ≠ ⊥ → ∀ k : ℕ, k ≤ N →
      ((idealAllocations D k).card : ℝ) ≤ C * (Ideal.absNorm D : ℝ) ^ ε := by
  let δ : ℝ := ε / ((N : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨B, hB, hsub⟩ := HeckePort.Moments.prime_support_subsets_bound K δ hδ
  let M : ℝ := max B 1
  have hM : 1 ≤ M := le_max_right _ _
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  refine ⟨M ^ N, pow_pos hMpos _, ?_⟩
  intro D hD k hk
  have hnorm : (1 : ℝ) ≤ Ideal.absNorm D := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hbudget : δ * (k : ℝ) ≤ ε := by
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    have he : δ * ((N : ℝ) + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hbase : (2 : ℝ) ^ (primeSupport D).card ≤
      M * (Ideal.absNorm D : ℝ) ^ δ :=
    (hsub D hD).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hcard : ((idealAllocations D k).card : ℝ) ≤
      ((2 : ℝ) ^ (primeSupport D).card) ^ k := by
    exact_mod_cast card_allocations_le (primeSupport D) k
  calc
    _ ≤ ((2 : ℝ) ^ (primeSupport D).card) ^ k := hcard
    _ ≤ (M * (Ideal.absNorm D : ℝ) ^ δ) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    _ = M ^ k * (Ideal.absNorm D : ℝ) ^ (δ * (k : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    _ ≤ M ^ N * (Ideal.absNorm D : ℝ) ^ ε :=
      mul_le_mul (pow_le_pow_right₀ hM hk)
        (Real.rpow_le_rpow_of_exponent_le hnorm hbudget)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hMpos.le _)

/-- The actual signed allocation mass, after any further compatibility
filter, has the same uniform subpower bound. -/
theorem ideal_allocation_mass_bound (K : Type*) [Field K] [NumberField K]
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal (𝓞 K)), D ≠ ⊥ → ∀ k : ℕ, k ≤ N →
      ∀ T : Finset (primeSupport D → Finset (Fin k)), T ⊆ idealAllocations D k →
        (∑ v ∈ T, ‖sign (primeSupport D) v‖) ≤ C * (Ideal.absNorm D : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := ideal_allocation_card_bound K N ε hε
  refine ⟨C, hC, ?_⟩
  intro D hD k hk T hT
  rw [sum_norm_sign]
  exact (Nat.cast_le.mpr (Finset.card_le_card hT)).trans (hb D hD k hk)

end HeckeSkeleton.Moments.EngineStep.AllocationMass

#print axioms HeckeSkeleton.Moments.EngineStep.AllocationMass.ideal_allocation_card_bound
#print axioms HeckeSkeleton.Moments.EngineStep.AllocationMass.ideal_allocation_mass_bound
