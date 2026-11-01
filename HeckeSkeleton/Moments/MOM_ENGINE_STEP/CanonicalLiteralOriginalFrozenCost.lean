import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveEnergy
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrozenBounds

/-!
# The actual frozen cost of the preceding original allocation

This cost is read from the original allocation witness: each removed
prime contributes its actual annulus ratio and squared profile norm.
The divisor denominator is the original allocation's full ideal norm.
The binary arithmetic mask and the original squarefree allocation
identity prove the scalar bound for every actual pair of frequencies.

The energy wrapper uses that proved scalar bound on the unchanged row
carrier. The original cost is kept outside the new independent passive
allocations; no completed scalar estimate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (B : ActualColumnAllocation K k)

/-- Every factor is evaluated at the stored original witness. -/
def originalFrozenCost : ℝ :=
  (∏ i ∈ Finset.univ \ B.keep,
    ((Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) / d.base ^ d.length i) *
      ‖d.slotWeight i (B.witness.2 i)‖ ^ 2) /
    (Ideal.absNorm B.divisor : ℝ)

theorem originalFrozenCost_nonneg : 0 ≤ d.originalFrozenCost B := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.prod_nonneg
  intro i _
  exact mul_nonneg
    (div_nonneg (Nat.cast_nonneg _)
      (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).le)
    (sq_nonneg _)

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The individual arithmetic bounds and the actual allocation prove
the row-uniform cost, including the genuine old divisor denominator. -/
theorem originalFrozenCost_scalar_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hmask : d.characters.MaskIndicator)
    (hsquarefree : Squarefree B.divisor)
    (hselection : B.selection ∈ AllocationMass.idealAllocations B.divisor (k + 2))
    (g h : A.R) :
    ‖B.scalar (σ := σ) d.characters g h d.base d.length d.slotWeight‖ ^ 2 ≤
      d.originalFrozenCost B := by
  refine B.scalar_norm_sq_le_divisor C d.characters g h d.base
    (zero_lt_one.trans d.base_gt_one) d.length d.slotWeight
    (fun i => (Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) / d.base ^ d.length i)
    (fun i => ‖d.slotWeight i (B.witness.2 i)‖ ^ 2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsquarefree hselection
  · exact OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
      d.characters.plain d.characters.plainTwist d.characters.mask _ (hmask _)
  · exact OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
      d.characters.plain d.characters.plainTwist d.characters.mask _ (hmask _)
  · intro i _
    exact OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one
      (d.characters.slot i) (d.characters.slotTwist i) d.characters.mask _ (hmask _)
  · intro i _
    exact le_of_eq (div_mul_cancel₀ _
      (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).ne').symm
  · intro i _
    exact le_rfl
  · intro i
    exact div_nonneg (Nat.cast_nonneg _)
      (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).le
  · intro i
    exact sq_nonneg _

/-- Only the actual removed occurrences are counted. The old shared
divisor, when present, is identified later when the two sides pair. -/
theorem originalFrozenCost_le_power
    (cap : ℕ) (budget : ℝ) (hbudget : 1 ≤ budget) (hcap : k ≤ cap)
    (hslot : ∀ i ∈ Finset.univ \ B.keep,
      ((Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) / d.base ^ d.length i) *
        ‖d.slotWeight i (B.witness.2 i)‖ ^ 2 ≤ budget) :
    d.originalFrozenCost B ≤ budget ^ cap / (Ideal.absNorm B.divisor : ℝ) := by
  unfold originalFrozenCost
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∏ _i ∈ Finset.univ \ B.keep, budget :=
      Finset.prod_le_prod₀ (fun i _ => mul_nonneg
        (div_nonneg (Nat.cast_nonneg _)
          (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).le)
        (sq_nonneg _)) hslot
    _ = budget ^ (Finset.univ \ B.keep).card := Finset.prod_const budget
    _ ≤ _ := pow_le_pow_right₀ hbudget ((Finset.card_le_univ _).trans
      (by simpa only [Fintype.card_fin] using hcap))

end CanonicalLiteralRectangles.Atoms

namespace CanonicalLiteralPassiveEnergy

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}

/-- The original energy estimate now consumes only the actual mask
and allocation identities. Its scalar cost is constructed above. -/
theorem original_sqrt_le_actualCost {H : Type*}
    (B : ActualColumnAllocation K k) (C : A.GeneralArithmeticContext σ η hS)
    (rows : Finset H) (weight : H → ℂ) (g h : H → A.R)
    (firstSign : ℝ) (negative : Bool)
    (hmask : d.characters.MaskIndicator)
    (hsquarefree : Squarefree B.divisor)
    (hselection : B.selection ∈ AllocationMass.idealAllocations B.divisor (k + 2))
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (jointColumnEnergy rows B.columns weight
      (fun j => d.frequencyWhole (σ := σ) (g j) (h j))
      (fun _ => canonicalPoint firstSign negative) ξ) ≤
      Real.sqrt (d.originalFrozenCost B) * Real.sqrt
        (∑ j ∈ rows, ‖weight j‖ *
          ‖CanonicalLiteralPassiveSource.centeredColumn (σ := σ) (d := d)
            B (d.characters.restrictSlots B.keep) (g j) (h j) firstSign negative ξ‖ ^ 2) := by
  apply original_sqrt_le_centered B rows weight g h firstSign negative
    (d.originalFrozenCost B) (d.originalFrozenCost_nonneg B) _ ξ
  intro j _
  exact d.originalFrozenCost_scalar_bound B C hmask hsquarefree hselection (g j) (h j)

end CanonicalLiteralPassiveEnergy
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.originalFrozenCost
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.originalFrozenCost_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.originalFrozenCost_scalar_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.originalFrozenCost_le_power
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveEnergy.original_sqrt_le_actualCost
