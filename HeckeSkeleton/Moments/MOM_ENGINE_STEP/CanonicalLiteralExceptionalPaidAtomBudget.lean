import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalAtomBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidScales

set_option linter.unusedSectionVars false

/-!
# Fixed costs of the paid original exceptional atomic scales

The two original extraction windows enlarge each root constant by the
fixed factor `annulus ^ cap`. This file computes that change on the
actual allocation records. The two atom constants therefore cost
`annulus ^ (2 * cap)`. The original common envelope and the separate
central Gauss compensation are then combined explicitly.

Every constant below depends only on the number field, the original
slot cap and the fixed annulus. The original profile amplitude remains
an explicit power; no completed atom or source bound is requested.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidAtomBudget

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

def pairConstant (cap : ℕ) (annulus : ℝ) : ℝ :=
  annulus ^ (2 * cap) *
    CanonicalLiteralExceptionalAtomBudget.pairConstant (K := K) cap annulus

/-- The central Gauss cost occurs once, outside the two atomic scales. -/
def totalConstant (cap : ℕ) (annulus : ℝ) : ℝ :=
  annulus ^ cap *
    (CanonicalLiteralExceptionalAtomBudget.commonConstant cap annulus *
      pairConstant (K := K) cap annulus)

theorem pairConstant_pos (cap : ℕ) (annulus : ℝ) (hannulus : 1 ≤ annulus) :
    0 < pairConstant (K := K) cap annulus := by
  sorry

theorem totalConstant_pos (cap : ℕ) (annulus : ℝ) (hannulus : 1 ≤ annulus) :
    0 < totalConstant (K := K) cap annulus := by
  sorry

theorem totalConstant_eq (cap : ℕ) (annulus : ℝ) :
    totalConstant (K := K) cap annulus =
      idealCountConstant K ^ (2 * cap) * annulus ^ (9 * cap + 3) := by
  sorry

/-- The formal total and slot lengths affect exponents, not this
constant. This equality is computed from the same original allocation. -/
theorem scales_constant_eq_original
    {k : ℕ} (B : ActualColumnAllocation K k)
    (Z targetTotal : ℝ) (length : Fin k → ℝ) (hlength : ∀ i, 0 ≤ length i)
    (annulus amplitude : ℝ) (cap : ℕ)
    (hannulus : 1 ≤ annulus) (hamplitude : 0 ≤ amplitude) (plainTotal : ℝ) :
    (CanonicalLiteralExceptionalPaidScales.scales B Z targetTotal length hlength
      annulus amplitude cap hannulus hamplitude).constant =
      annulus ^ cap *
        (B.originalAtomicScales Z plainTotal length hlength
          (fun _ => annulus) (fun _ => amplitude)
          (fun _ => hannulus) (fun _ => hamplitude)).constant := by
  sorry

/-- The two actual paid scales inherit the original per-atom budget.
Their two additional root constants are paid exactly once each. -/
theorem original_pair_constant_le
    (cap : ℕ) (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 1 ≤ amplitude)
    {k l : ℕ} (left : ActualColumnAllocation K k) (right : ActualColumnAllocation K l)
    (baseLeft targetTotalLeft baseRight targetTotalRight : ℝ)
    (lengthLeft : Fin k → ℝ) (lengthRight : Fin l → ℝ)
    (hleftLength : ∀ i, 0 ≤ lengthLeft i) (hrightLength : ∀ i, 0 ≤ lengthRight i)
    (hk : k ≤ cap) (hl : l ≤ cap) :
    (CanonicalLiteralExceptionalPaidScales.scales left baseLeft targetTotalLeft
        lengthLeft hleftLength annulus amplitude cap hannulus
        (zero_le_one.trans hamplitude)).constant *
      (CanonicalLiteralExceptionalPaidScales.scales right baseRight targetTotalRight
        lengthRight hrightLength annulus amplitude cap hannulus
        (zero_le_one.trans hamplitude)).constant ≤
      pairConstant (K := K) cap annulus *
        amplitude ^ CanonicalLiteralExceptionalAtomBudget.pairDegree cap := by
  sorry

/-- Common atoms, both paid root constants and the single central
compensation preserve the original explicit profile degree. -/
theorem budget_product (cap : ℕ) (annulus amplitude : ℝ) :
    annulus ^ cap *
        ((CanonicalLiteralExceptionalAtomBudget.commonConstant cap annulus *
            amplitude ^ CanonicalLiteralExceptionalAtomBudget.commonDegree cap) *
          (pairConstant (K := K) cap annulus *
            amplitude ^ CanonicalLiteralExceptionalAtomBudget.pairDegree cap)) =
      totalConstant (K := K) cap annulus *
        amplitude ^ CanonicalLiteralExceptionalAtomBudget.totalDegree cap := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidAtomBudget

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidAtomBudget.scales_constant_eq_original
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidAtomBudget.original_pair_constant_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidAtomBudget.budget_product
