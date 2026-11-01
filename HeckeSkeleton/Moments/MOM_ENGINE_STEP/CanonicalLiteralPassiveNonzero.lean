import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveEnergy

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
    nonzeroLabels W B A M ⊆ (CanonicalLiteralPassiveSource.labels W B A M).attach :=
  Finset.filter_subset _ _

variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })

theorem sign_ne_zero (ha : a ∈ nonzeroLabels W B A M) : sign a.val ≠ 0 :=
  (Finset.mem_filter.mp ha).2

theorem divisor_squarefree (ha : a ∈ nonzeroLabels W B A M) :
    Squarefree (branch W B A M a).divisor := by
  change Squarefree a.val.1
  by_contra hsq
  have hz : sign a.val = 0 := by
    simp only [sign, moebius_of_not_squarefree hsq, Int.cast_zero, zero_mul]
  exact sign_ne_zero W B A M a ha hz

/-- The original live allocation already has a valid occurrence
selection. The additional nonzero filter never changes that selection. -/
theorem selection_mem :
    (branch W B A M a).selection ∈
      AllocationMass.idealAllocations (branch W B A M a).divisor
        (B.keep.card + 2) := by
  change a.val.2 ∈ AllocationMass.idealAllocations a.val.1 (B.keep.card + 2)
  exact (Finset.mem_sigma.mp (Finset.mem_filter.mp a.property).1).2

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
  unfold passiveColumn
  symm
  apply Finset.sum_subset (nonzeroLabels_subset W B A M)
  intro a ha hn
  have hz : sign a.val = 0 := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨ha, h⟩)
  simp only [hz, zero_mul]

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
  simp_rw [passiveColumn_eq_sum_nonzero (σ := σ) W B A M paid]
  refine (sqrt_row_energy_sum rows (nonzeroLabels W B A M) weight
    (fun a j => sign a.val * jointFourierColumn (branch W B A M a).columns
      ((table W B A paid).frequencyWhole (σ := σ) (g j) (h j))
      (rawSourceLocation (plainLocation₁ B firstSign negative)
        (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ)).trans ?_
  apply Finset.sum_le_sum
  intro a _
  apply Real.sqrt_le_sqrt
  unfold jointColumnEnergy
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, mul_pow]
  have hs : ‖sign a.val‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (norm_sign_le_one a.val) 2
  calc
    _ ≤ ‖weight j‖ * (1 *
        ‖jointFourierColumn (branch W B A M a).columns
          ((table W B A paid).frequencyWhole (σ := σ) (g j) (h j))
          (rawSourceLocation (plainLocation₁ B firstSign negative)
            (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (sq_nonneg _))
        (norm_nonneg _)
    _ = _ := by rw [one_mul]

end CanonicalLiteralPassiveNonzero
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero.divisor_squarefree
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero.selection_mem
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero.passiveColumn_eq_sum_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNonzero.sqrt_passiveColumn_le_nonzero
