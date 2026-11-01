import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveDeletion
import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds

/-!
# Uniform cost of the actual passive-deletion labels

The carrier is the literal sigma of divisors of the fixed deletion
ideal and allocations to all `k + 2` original occurrences. Its size
is bounded by one divisor-count estimate and one allocation-count
estimate, each using half of the prescribed exponent.

The constant is selected before the ideal and moving slot count.
Every subsequent compatibility or nonempty-column filter decreases
the sum of norms of the unchanged signed coefficients.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion

open NumberField DedekindZetaZeroFree.LargeSieve
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

/-- The actual signed coefficient has norm at most one on every label,
including labels which later have an empty allocated carrier. -/
theorem sum_norm_sign_le_card {k : ℕ} (T : Finset (Label K k)) :
    (∑ a ∈ T, ‖sign a‖) ≤ (T.card : ℝ) := by
  calc
    _ ≤ ∑ _a ∈ T, (1 : ℝ) :=
      Finset.sum_le_sum (fun a _ => norm_sign_le_one a)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

theorem norm_sum_sign_le_card {k : ℕ} (T : Finset (Label K k)) :
    ‖∑ a ∈ T, sign a‖ ≤ (T.card : ℝ) :=
  (norm_sum_le T sign).trans (sum_norm_sign_le_card T)

/-- The full finite divisor-allocation carrier has a uniform subpower
cost. Both plain occurrences and every prime slot are counted. -/
theorem labels_card_bound (K : Type) [Field K] [NumberField K]
    (cap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal (𝓞 K)), M ≠ 0 → ∀ k : ℕ, k ≤ cap →
      ((labels M k).card : ℝ) ≤ C * (Ideal.absNorm M : ℝ) ^ ε := by
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨Cdiv, hCdiv, hdiv⟩ := ideal_divisor_count_le_rpow K (ε / 2) hhalf
  obtain ⟨Calloc, hCalloc, halloc⟩ :=
    AllocationMass.ideal_allocation_card_bound K (cap + 2) (ε / 2) hhalf
  refine ⟨Cdiv * Calloc, mul_pos (zero_lt_one.trans_le hCdiv) hCalloc, ?_⟩
  intro M hM k hk
  have hnorm : 0 < (Ideal.absNorm M : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hM)
  have hcard (D : Ideal (𝓞 K)) (hD : D ∈ idealDivisors M) :
      ((AllocationMass.idealAllocations D (k + 2)).card : ℝ) ≤
        Calloc * (Ideal.absNorm M : ℝ) ^ (ε / 2) := by
    have hdvd : D ∣ M := (mem_idealDivisors hM).mp hD
    have hDzero : D ≠ 0 := ne_zero_of_dvd_ne_zero hM hdvd
    have hnormD : (Ideal.absNorm D : ℝ) ≤ (Ideal.absNorm M : ℝ) := by
      exact_mod_cast Nat.le_of_dvd
        (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hM))
        (map_dvd Ideal.absNorm hdvd)
    exact (halloc D hDzero (k + 2) (Nat.add_le_add_right hk 2)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hnormD hhalf.le) hCalloc.le)
  have hdivCard : ((idealDivisors M).card : ℝ) ≤
      Cdiv * (Ideal.absNorm M : ℝ) ^ (ε / 2) := hdiv M
  rw [labels, Finset.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _D ∈ idealDivisors M, Calloc * (Ideal.absNorm M : ℝ) ^ (ε / 2) :=
      Finset.sum_le_sum hcard
    _ = ((idealDivisors M).card : ℝ) *
        (Calloc * (Ideal.absNorm M : ℝ) ^ (ε / 2)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Cdiv * (Ideal.absNorm M : ℝ) ^ (ε / 2)) *
        (Calloc * (Ideal.absNorm M : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right hdivCard
        (mul_nonneg hCalloc.le (Real.rpow_nonneg hnorm.le _))
    _ = (Cdiv * Calloc) * ((Ideal.absNorm M : ℝ) ^ (ε / 2) *
        (Ideal.absNorm M : ℝ) ^ (ε / 2)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hnorm, show ε / 2 + ε / 2 = ε by ring]

/-- The signed mass of any actual surviving subfamily has the same
uniform cost. Its cardinality is proved from the original labels. -/
theorem labels_mass_bound (K : Type) [Field K] [NumberField K]
    (cap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal (𝓞 K)), M ≠ 0 → ∀ k : ℕ, k ≤ cap →
      ∀ T : Finset (Label K k), T ⊆ labels M k →
        (∑ a ∈ T, ‖sign a‖) ≤ C * (Ideal.absNorm M : ℝ) ^ ε := by
  obtain ⟨C, hC, hcard⟩ := labels_card_bound K cap ε hε
  refine ⟨C, hC, ?_⟩
  intro M hM k hk T hT
  exact (sum_norm_sign_le_card T).trans
    ((Nat.cast_le.mpr (Finset.card_le_card hT)).trans (hcard M hM k hk))

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.sum_norm_sign_le_card
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.norm_sum_sign_le_card
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.labels_card_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.labels_mass_bound
