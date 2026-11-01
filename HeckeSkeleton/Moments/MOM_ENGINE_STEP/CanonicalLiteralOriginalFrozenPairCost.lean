import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralOriginalFrozenCost

/-!
# The old allocation contributes one additional slot cost

The outer weight used by the actual passive kernel family is the
product of square roots of the two original witness-based costs. Its
bound follows from the individual original slot windows. Both ideal
norm denominators are retained until an explicit equality identifies
the preceding shared divisor.

This equality concerns only the old allocation. The two later passive
allocation divisors are independent and do not occur in this proof.
The resulting additional slot power is paid once outside the new
profile radii and normalized capacities.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Analysis HeckePort.Moments

namespace CanonicalLiteralRectangles.Atoms

variable {K : Type} [Field K] [NumberField K] {k l : ℕ}
variable (left : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (right : CanonicalLiteralRectangles.Atoms (K := K) l)
variable (leftAllocation : ActualColumnAllocation K k)
variable (rightAllocation : ActualColumnAllocation K l)

/-- This is the exact old frozen outer cost used by the passive
family, before any estimate or identification of divisors. -/
def originalFrozenPairCost : ℝ :=
  Real.sqrt (left.originalFrozenCost leftAllocation) *
    Real.sqrt (right.originalFrozenCost rightAllocation)

theorem originalFrozenPairCost_nonneg :
    0 ≤ originalFrozenPairCost left right leftAllocation rightAllocation :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The original two sets of removed occurrences cost one slot power
after their two square roots are paired. -/
theorem originalFrozenPairCost_le_independent
    (cap : ℕ) (budget : ℝ) (hbudget : 1 ≤ budget) (hleft : k ≤ cap) (hright : l ≤ cap)
    (hslotL : ∀ i ∈ Finset.univ \ leftAllocation.keep,
      ((Ideal.absNorm (leftAllocation.witness.2 i).asIdeal : ℝ) / left.base ^ left.length i) *
        ‖left.slotWeight i (leftAllocation.witness.2 i)‖ ^ 2 ≤ budget)
    (hslotR : ∀ i ∈ Finset.univ \ rightAllocation.keep,
      ((Ideal.absNorm (rightAllocation.witness.2 i).asIdeal : ℝ) / right.base ^ right.length i) *
        ‖right.slotWeight i (rightAllocation.witness.2 i)‖ ^ 2 ≤ budget) :
    originalFrozenPairCost left right leftAllocation rightAllocation ≤
      budget ^ cap /
        (Real.sqrt (Ideal.absNorm leftAllocation.divisor : ℝ) *
          Real.sqrt (Ideal.absNorm rightAllocation.divisor : ℝ)) := by
  have hl := Real.sqrt_le_sqrt
    (left.originalFrozenCost_le_power leftAllocation cap budget hbudget hleft hslotL)
  have hr := Real.sqrt_le_sqrt
    (right.originalFrozenCost_le_power rightAllocation cap budget hbudget hright hslotR)
  calc
    _ ≤ Real.sqrt (budget ^ cap / (Ideal.absNorm leftAllocation.divisor : ℝ)) *
        Real.sqrt (budget ^ cap / (Ideal.absNorm rightAllocation.divisor : ℝ)) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_div (pow_nonneg (zero_le_one.trans hbudget) cap),
        Real.sqrt_div (pow_nonneg (zero_le_one.trans hbudget) cap), div_mul_div_comm,
        Real.mul_self_sqrt (pow_nonneg (zero_le_one.trans hbudget) cap)]

/-- Only the preceding original divisor is shared. This converts the
actual outer cost to the single original inverse norm, once. -/
theorem originalFrozenPairCost_le_shared
    (cap : ℕ) (budget : ℝ) (hbudget : 1 ≤ budget) (hleft : k ≤ cap) (hright : l ≤ cap)
    (hslotL : ∀ i ∈ Finset.univ \ leftAllocation.keep,
      ((Ideal.absNorm (leftAllocation.witness.2 i).asIdeal : ℝ) / left.base ^ left.length i) *
        ‖left.slotWeight i (leftAllocation.witness.2 i)‖ ^ 2 ≤ budget)
    (hslotR : ∀ i ∈ Finset.univ \ rightAllocation.keep,
      ((Ideal.absNorm (rightAllocation.witness.2 i).asIdeal : ℝ) / right.base ^ right.length i) *
        ‖right.slotWeight i (rightAllocation.witness.2 i)‖ ^ 2 ≤ budget)
    (horiginalDivisor : leftAllocation.divisor = rightAllocation.divisor) :
    originalFrozenPairCost left right leftAllocation rightAllocation ≤
      budget ^ cap / (Ideal.absNorm leftAllocation.divisor : ℝ) := by
  have h := originalFrozenPairCost_le_independent left right leftAllocation rightAllocation
    cap budget hbudget hleft hright hslotL hslotR
  simpa only [← horiginalDivisor, Real.mul_self_sqrt (Nat.cast_nonneg _)] using h

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.originalFrozenPairCost
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.originalFrozenPairCost_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.originalFrozenPairCost_le_independent
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.originalFrozenPairCost_le_shared
