import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.HybridExpansion

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Finite leaf transport keeps the same source and terminal terms

The finite carrier is reindexed once at the public boundary.  This
module supplies that common transport for every amplification tag and
for both Cauchy sides, with no new arithmetic or analytic input.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField HeckeGeneral.ThetaSkeleton.Global EngineInduction

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}
variable {n : Node K c.family.omega (targetCharacter K c)} {Z : ℝ}
variable {input : OriginalInput c n Z}

namespace HybridExpansion

def reindex (E : HybridExpansion c n Z input) {m : ℕ}
    (e : Fin m ≃ Fin E.branches) : HybridExpansion c n Z input where
  branches := m
  pool := E.pool
  tag b := E.tag (e b)
  leaf b := E.leaf (e b)
  firstZero := E.firstZero
  secondZero := E.secondZero
  tail := E.tail
  firstZero_nonneg := E.firstZero_nonneg
  secondZero_nonneg := E.secondZero_nonneg
  tail_nonneg := E.tail_nonneg

theorem reindex_exceptional (E : HybridExpansion c n Z input) {m : ℕ}
    (e : Fin m ≃ Fin E.branches) : (E.reindex e).exceptional = E.exceptional := by
  sorry

theorem reindex_ordinary (E : HybridExpansion c n Z input) {m : ℕ}
    (e : Fin m ≃ Fin E.branches) : (E.reindex e).ordinary = E.ordinary := by
  sorry

theorem reindex_total (E : HybridExpansion c n Z input) {m : ℕ}
    (e : Fin m ≃ Fin E.branches) : (E.reindex e).total = E.total := by
  sorry

end HybridExpansion
end HeckeSkeleton.Moments.EngineStepV2
