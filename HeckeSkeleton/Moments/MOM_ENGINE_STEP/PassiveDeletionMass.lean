import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveDeletion
import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds

set_option linter.unusedSectionVars false

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
  sorry

theorem norm_sum_sign_le_card {k : ℕ} (T : Finset (Label K k)) :
    ‖∑ a ∈ T, sign a‖ ≤ (T.card : ℝ) := by
  sorry

/-- The full finite divisor-allocation carrier has a uniform subpower
cost. Both plain occurrences and every prime slot are counted. -/
theorem labels_card_bound (K : Type) [Field K] [NumberField K]
    (cap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal (𝓞 K)), M ≠ 0 → ∀ k : ℕ, k ≤ cap →
      ((labels M k).card : ℝ) ≤ C * (Ideal.absNorm M : ℝ) ^ ε := by
  sorry

/-- The signed mass of any actual surviving subfamily has the same
uniform cost. Its cardinality is proved from the original labels. -/
theorem labels_mass_bound (K : Type) [Field K] [NumberField K]
    (cap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal (𝓞 K)), M ≠ 0 → ∀ k : ℕ, k ≤ cap →
      ∀ T : Finset (Label K k), T ⊆ labels M k →
        (∑ a ∈ T, ‖sign a‖) ≤ C * (Ideal.absNorm M : ℝ) ^ ε := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.sum_norm_sign_le_card
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.norm_sum_sign_le_card
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.labels_card_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.labels_mass_bound
