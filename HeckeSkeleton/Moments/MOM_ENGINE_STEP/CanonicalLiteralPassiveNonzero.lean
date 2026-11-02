import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveEnergy

set_option linter.unusedSectionVars false

/-!
# Remove zero passive coefficients before producing children

The new finite carrier is a filter of the existing attached live
labels.  Every element is still the original label and stores exactly
the same allocation witness.  A nonzero signed coefficient forces its
divisor to be squarefree, so the later frozen-scalar estimate needs no
new squarefreeness premise.  Zero coefficients are removed by an exact
finite-sum identity before applying weighted Minkowski.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

namespace CanonicalLiteralPassiveNonzero

open CanonicalLiteralPassiveSource CanonicalLiteralPassiveDeletion

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k) (A : SArithmeticData K)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)

def nonzeroLabels :=
  (CanonicalLiteralPassiveSource.labels W B A M).attach.filter
    (fun a => sign a.val ≠ 0)

theorem nonzeroLabels_subset :
    nonzeroLabels W B A M ⊆ (CanonicalLiteralPassiveSource.labels W B A M).attach := by
  sorry

variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })

theorem sign_ne_zero (ha : a ∈ nonzeroLabels W B A M) : sign a.val ≠ 0 := by
  sorry

theorem divisor_squarefree (ha : a ∈ nonzeroLabels W B A M) :
    Squarefree (branch W B A M a).divisor := by
  sorry

/-- The original live allocation already has a valid occurrence
selection. The additional nonzero filter never changes that selection. -/
theorem selection_mem :
    (branch W B A M a).selection ∈
      AllocationMass.idealAllocations (branch W B A M a).divisor
        (B.keep.card + 2) := by
  sorry

variable {σ : K →+* ℂ}
variable (paid : FixedChildCharacters K B.keep.card)

/-- The actual centered column is unchanged when its zero signed
terms are removed. All retained labels have their original type. -/
theorem passiveColumn_eq_sum_nonzero (g h : A.R)
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    passiveColumn (σ := σ) W B paid M g h firstSign negative ξ =
      ∑ a ∈ nonzeroLabels W B A M,
        sign a.val * jointFourierColumn (branch W B A M a).columns
          ((table W B A paid).frequencyWhole (σ := σ) g h)
          (rawSourceLocation (plainLocation₁ B firstSign negative)
            (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ := by
  sorry

/-- Weighted Minkowski is used only after the zero coefficients have
been removed. Every resulting branch therefore has a squarefree
divisor proved by `divisor_squarefree`. -/
theorem sqrt_passiveColumn_le_nonzero {H : Type*} (rows : Finset H)
    (weight : H → ℂ) (g h : H → A.R) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (∑ j ∈ rows, ‖weight j‖ *
      ‖passiveColumn (σ := σ) W B paid M (g j) (h j) firstSign negative ξ‖ ^ 2) ≤
      ∑ a ∈ nonzeroLabels W B A M,
        Real.sqrt (jointColumnEnergy rows (branch W B A M a).columns weight
          (fun j => (table W B A paid).frequencyWhole (σ := σ) (g j) (h j))
          (fun _ => rawSourceLocation (plainLocation₁ B firstSign negative)
            (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ) := by
  sorry

end CanonicalLiteralPassiveNonzero
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero.divisor_squarefree
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero.selection_mem
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero.passiveColumn_eq_sum_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero.sqrt_passiveColumn_le_nonzero
