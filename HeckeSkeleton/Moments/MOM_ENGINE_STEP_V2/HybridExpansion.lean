import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridFiniteLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ScalarLedger

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A single finite family for every two-transform branch

Direct, pool-main, and valuation 1/6/7 branches share this carrier.
Each leaf retains its actual row polynomial and both original Fourier
kernels.  The exceptional contribution is computed from those leaves.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ActualSIntegerMoments
open EngineStep EngineInduction

variable {K : Type} [Field K] [NumberField K]

structure HybridExpansion (c : TargetContext K)
    (n : Node K c.family.omega (targetCharacter K c)) (Z : ℝ)
    (input : OriginalInput c n Z) where
  branches : ℕ
  leaf : Fin branches → ActualHybridLeaf K (ActualSIntegerOrbit K (places K c)) ℝ ℝ
  firstZero : ℝ
  secondZero : ℝ
  tail : ℝ
  firstZero_nonneg : 0 ≤ firstZero
  secondZero_nonneg : 0 ≤ secondZero
  tail_nonneg : 0 ≤ tail

namespace HybridExpansion

variable {c : TargetContext K}
variable {n : Node K c.family.omega (targetCharacter K c)} {Z : ℝ}
variable {input : OriginalInput c n Z}

def exceptional (E : HybridExpansion c n Z input) : ℝ :=
  ∑ b : Fin E.branches, (E.leaf b).exceptionalCost

def ordinary (E : HybridExpansion c n Z input) : ℝ :=
  ∑ b : Fin E.branches, (E.leaf b).ordinaryCost

theorem exceptional_nonneg (E : HybridExpansion c n Z input) : 0 ≤ E.exceptional := by
  sorry

theorem ordinary_nonneg (E : HybridExpansion c n Z input) : 0 ≤ E.ordinary := by
  sorry

def terminals (E : HybridExpansion c n Z input) : ScalarLedger where
  firstZero := E.firstZero
  secondZero := E.secondZero
  exceptional := E.exceptional
  tail := E.tail
  firstZero_nonneg := E.firstZero_nonneg
  secondZero_nonneg := E.secondZero_nonneg
  exceptional_nonneg := E.exceptional_nonneg
  tail_nonneg := E.tail_nonneg

def total (E : HybridExpansion c n Z input) : ℝ :=
  E.terminals.total + E.ordinary

/-- Fubini is applied once to the actual finite leaf polynomials. -/
theorem ordinary_add_exceptional (E : HybridExpansion c n Z input) :
    E.exceptional + E.ordinary = ∑ b : Fin E.branches, (E.leaf b).cost := by
  sorry

theorem leaf_fubini (E : HybridExpansion c n Z input) (b : Fin E.branches) :
    (∫ ξ, (E.leaf b).firstPhaseCost ξ ∂actualFourierMeasure (E.leaf b).firstKernel) =
      (E.leaf b).cost := by
  sorry

end HybridExpansion
end HeckeSkeleton.Moments.EngineStepV2
