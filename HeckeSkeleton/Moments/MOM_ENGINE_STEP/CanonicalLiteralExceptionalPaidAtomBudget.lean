import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalAtomBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidScales

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
    0 < pairConstant (K := K) cap annulus :=
  mul_pos (pow_pos (zero_lt_one.trans_le hannulus) _)
    (CanonicalLiteralExceptionalAtomBudget.pairConstant_pos cap annulus hannulus)

theorem totalConstant_pos (cap : ℕ) (annulus : ℝ) (hannulus : 1 ≤ annulus) :
    0 < totalConstant (K := K) cap annulus :=
  mul_pos (pow_pos (zero_lt_one.trans_le hannulus) _)
    (mul_pos
      (zero_lt_one.trans_le
        (CanonicalLiteralExceptionalAtomBudget.commonConstant_one cap annulus hannulus))
      (pairConstant_pos cap annulus hannulus))

theorem totalConstant_eq (cap : ℕ) (annulus : ℝ) :
    totalConstant (K := K) cap annulus =
      idealCountConstant K ^ (2 * cap) * annulus ^ (9 * cap + 3) := by
  unfold totalConstant pairConstant
    CanonicalLiteralExceptionalAtomBudget.commonConstant
    CanonicalLiteralExceptionalAtomBudget.pairConstant
  calc
    _ = idealCountConstant K ^ (2 * cap) *
        (annulus ^ cap * annulus ^ (cap + 1) *
          annulus ^ (2 * cap) * annulus ^ (5 * cap + 2)) := by ring
    _ = _ := by
      rw [← pow_add, ← pow_add, ← pow_add,
        show cap + (cap + 1) + 2 * cap + (5 * cap + 2) = 9 * cap + 3 by omega]

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
  dsimp only [CanonicalLiteralExceptionalPaidScales.scales,
    ExceptionalAtomicScales.constant, ExceptionalAtomicScales.frozenNumerator,
    ActualColumnAllocation.originalAtomicScales]
  ring

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
  let UL := left.originalAtomicScales baseLeft 0 lengthLeft hleftLength
    (fun _ => annulus) (fun _ => amplitude)
    (fun _ => hannulus) (fun _ => zero_le_one.trans hamplitude)
  let UR := right.originalAtomicScales baseRight 0 lengthRight hrightLength
    (fun _ => annulus) (fun _ => amplitude)
    (fun _ => hannulus) (fun _ => zero_le_one.trans hamplitude)
  have h := CanonicalLiteralExceptionalAtomBudget.original_pair_constant_le
    cap annulus amplitude hannulus hamplitude left right
    baseLeft 0 baseRight 0 lengthLeft lengthRight hleftLength hrightLength hk hl
  calc
    _ = annulus ^ (2 * cap) * (UL.constant * UR.constant) := by
      rw [scales_constant_eq_original left baseLeft targetTotalLeft lengthLeft hleftLength
          annulus amplitude cap hannulus (zero_le_one.trans hamplitude) 0,
        scales_constant_eq_original right baseRight targetTotalRight lengthRight hrightLength
          annulus amplitude cap hannulus (zero_le_one.trans hamplitude) 0,
        show 2 * cap = cap + cap by omega, pow_add]
      dsimp only [UL, UR]
      ring
    _ ≤ annulus ^ (2 * cap) *
        (CanonicalLiteralExceptionalAtomBudget.pairConstant (K := K) cap annulus *
          amplitude ^ CanonicalLiteralExceptionalAtomBudget.pairDegree cap) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg (zero_le_one.trans hannulus) _)
    _ = _ := by unfold pairConstant; ring

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
  calc
    _ = annulus ^ cap * (annulus ^ (2 * cap) *
        ((CanonicalLiteralExceptionalAtomBudget.commonConstant cap annulus *
            amplitude ^ CanonicalLiteralExceptionalAtomBudget.commonDegree cap) *
          (CanonicalLiteralExceptionalAtomBudget.pairConstant (K := K) cap annulus *
            amplitude ^ CanonicalLiteralExceptionalAtomBudget.pairDegree cap))) := by
      unfold pairConstant
      ring
    _ = _ := by
      rw [CanonicalLiteralExceptionalAtomBudget.budget_product]
      unfold totalConstant pairConstant CanonicalLiteralExceptionalAtomBudget.totalConstant
      ring

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidAtomBudget

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidAtomBudget.scales_constant_eq_original
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidAtomBudget.original_pair_constant_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidAtomBudget.budget_product
