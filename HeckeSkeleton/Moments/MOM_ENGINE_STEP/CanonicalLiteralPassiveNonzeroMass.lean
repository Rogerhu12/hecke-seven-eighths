import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveNonzero
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveLabelMass

/-!
# Exact mass of the nonzero passive labels

Every retained signed coefficient is an actual Mobius sign times an
occurrence-allocation sign. Nonvanishing forces a squarefree divisor,
so its norm is exactly one. The cardinality used after Minkowski is
therefore exactly the signed mass of the original surviving labels.

The direct and pool bounds below use the already proved original
column/prime windows. No reverse use of a norm-at-most-one inequality
and no new cardinality hypothesis is involved.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis LocalFiniteSums
open CanonicalLiteralPassiveDeletion CanonicalLiteralPassiveLabelMass

variable {K : Type} [Field K] [NumberField K]

theorem norm_sign_eq_one_of_ne_zero {k : ℕ} (a : Label K k) (ha : sign a ≠ 0) :
    ‖sign a‖ = 1 := by
  have hs : Squarefree a.1 := by
    by_contra h
    exact ha (by simp only [sign, moebius_of_not_squarefree h, Int.cast_zero, zero_mul])
  rw [sign, norm_mul, AllocationMass.norm_sign, mul_one, hs.moebius_eq]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow, norm_neg,
    norm_one, one_pow]

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k) (A : SArithmeticData K)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)

/-- The finite carrier is the same attached-and-filtered carrier used
by the actual passive Minkowski inequality. -/
theorem card_eq_signed_mass :
    ((nonzeroLabels W B A M).card : ℝ) =
      ∑ a ∈ CanonicalLiteralPassiveSource.labels W B A M, ‖sign a‖ := by
  calc
    _ = ∑ a ∈ nonzeroLabels W B A M, ‖sign a.val‖ := by
      symm
      calc
        _ = ∑ _a ∈ nonzeroLabels W B A M, (1 : ℝ) :=
          Finset.sum_congr rfl (fun a ha =>
            norm_sign_eq_one_of_ne_zero a.val (sign_ne_zero W B A M a ha))
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ∑ a ∈ (CanonicalLiteralPassiveSource.labels W B A M).attach,
        ‖sign a.val‖ := by
      apply Finset.sum_subset (nonzeroLabels_subset W B A M)
      intro a ha hn
      have hz : sign a.val = 0 := by
        by_contra h
        exact hn (Finset.mem_filter.mpr ⟨ha, h⟩)
      simp only [hz, norm_zero]
    _ = _ := Finset.sum_attach _ (fun a => ‖sign a‖)

/-- This is the actual direct/main nonzero-label count, with its
constant chosen before the source, scale and common fibre. -/
theorem direct_source_card (cap : ℕ) (columnBound ε : ℝ)
    (hcolumnBound : 0 ≤ columnBound) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z → ∀ (A : SArithmeticData K)
      (D I : Ideal (𝓞 K)), I ≠ 0 → (firstMask D).val ∣ I →
      (Ideal.absNorm I : ℝ) ≤ Z ^ columnBound →
      ∀ k : ℕ, ∀ (d : CanonicalLiteralRectangles.Atoms (K := K) k)
        (W : d.ProfileData) (allocation : ActualColumnAllocation K k), k ≤ cap →
        ((nonzeroLabels W allocation A (firstMask D)).card : ℝ) ≤ C * Z ^ ε := by
  obtain ⟨C, hC, hmass⟩ := direct_source_labels_mass (K := K)
    cap columnBound ε hcolumnBound hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ A D I hI hdiv hnorm k d W allocation hk
  rw [card_eq_signed_mass]
  exact hmass Z hZ A D I hI hdiv hnorm k d W allocation hk

/-- The pool mask still includes both genuine prime copies at
valuation six; only zero Mobius coefficients are removed. -/
theorem pool_source_card (cap : ℕ) (columnBound primeBound ε : ℝ)
    (hcolumnBound : 0 ≤ columnBound) (hprimeBound : 0 ≤ primeBound) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z → ∀ (A : SArithmeticData K)
      (D I : Ideal (𝓞 K)), I ≠ 0 → (firstMask D).val ∣ I →
      (Ideal.absNorm I : ℝ) ≤ Z ^ columnBound →
      ∀ (p : ExteriorPrime A), (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ primeBound →
      ∀ e : AmplifierValuation, ∀ k : ℕ,
      ∀ (d : CanonicalLiteralRectangles.Atoms (K := K) k)
        (W : d.ProfileData) (allocation : ActualColumnAllocation K k), k ≤ cap →
        ((nonzeroLabels W allocation A (poolMask D p e)).card : ℝ) ≤ C * Z ^ ε := by
  obtain ⟨C, hC, hmass⟩ := pool_source_labels_mass (K := K)
    cap columnBound primeBound ε hcolumnBound hprimeBound hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ A D I hI hdiv hnorm p hprime e k d W allocation hk
  rw [card_eq_signed_mass]
  exact hmass Z hZ A D I hI hdiv hnorm p hprime e k d W allocation hk

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero.norm_sign_eq_one_of_ne_zero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero.card_eq_signed_mass
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero.direct_source_card
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero.pool_source_card
