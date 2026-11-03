import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalRefinement
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedCostBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The second allocation scalar is charged exactly once

The canonical residual source moves the original inner frozen scalar
into the row weight. Its passive allocation then supplies its own new
frozen scalar. The identities below distinguish these two operations
and retain the original complex common normalizer unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ConditionalMoments

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} {input : ProfileInput call}

namespace OrdinarySeed

variable (seed : OrdinarySeed packet)
variable (support : seed.ordinary.PassiveSupport input)

theorem innerScalar_eq_original_frozen (side : Bool) (h : seed.ordinary.rows.live) :
    seed.innerScalar side h =
      (seed.ordinary.originalSource side false).frozenScalar
        (σ := Arithmetic.embedding c) h := by
  have hlength : (seed.ordinary.originalSource side false).length =
      seed.occurrences.beforeLength side := funext (seed.atoms.length side false)
  have hweight : (seed.ordinary.originalSource side false).slotWeight h =
      seed.occurrences.beforeSlotWeight side :=
    funext fun i => funext fun q => seed.atoms.slotWeight side false h i q
  unfold innerScalar ActualAllocatedSource.frozenScalar
  rw [seed.atoms.characters side false h, seed.atoms.base side false, hlength, hweight]
  cases side <;> rfl

theorem canonicalSource_weight_eq_childWeight (side : Bool)
    (a : support.labels side) (rectangle : Bool) (h : seed.ordinary.rows.live) :
    (seed.canonicalSource input support side a rectangle).weight h =
      (seed.ordinary.originalSource side false).childWeight
        (σ := Arithmetic.embedding c) h := by
  change (seed.ordinary.originalSource side false).weight h * seed.innerScalar side h *
    star (seed.innerScalar side h) = _
  rw [seed.innerScalar_eq_original_frozen]
  rfl

theorem canonicalSource_weight_norm (side : Bool)
    (a : support.labels side) (rectangle : Bool) (h : seed.ordinary.rows.live) :
    ‖(seed.canonicalSource input support side a rectangle).weight h‖ =
      ‖(seed.ordinary.originalSource side false).weight h‖ *
        ‖seed.innerScalar side h‖ ^ 2 := by
  change ‖(seed.ordinary.originalSource side false).weight h * seed.innerScalar side h *
    star (seed.innerScalar side h)‖ = _
  simp only [norm_mul, norm_star, pow_two]
  ring

theorem canonicalSource_fiber (side : Bool)
    (a : support.labels side) (rectangle : Bool) :
    SourceCost.fiber (seed.canonicalSource input support side a rectangle) =
      SourceCost.fiber (seed.ordinary.originalSource side false) := rfl

theorem canonicalSource_rowCost_le (side : Bool)
    (a : support.labels side) (rectangle : Bool)
    {rowCost innerCost : ℝ} (hrowCost : 0 ≤ rowCost) (hinnerCost : 0 ≤ innerCost)
    (hrow : ∀ h ∈ (seed.ordinary.originalSource side false).rows,
      ‖(seed.ordinary.originalSource side false).weight h‖ ≤ rowCost)
    (hinner : ∀ h ∈ (seed.ordinary.originalSource side false).rows,
      ‖seed.innerScalar side h‖ ^ 2 ≤ innerCost) :
    SourceCost.row (seed.canonicalSource input support side a rectangle) ≤
      rowCost * innerCost := by
  apply SourceCost.row_le _ (mul_nonneg hrowCost hinnerCost)
  intro h hh
  rw [seed.canonicalSource_weight_norm support]
  exact mul_le_mul (hrow h hh) (hinner h hh) (sq_nonneg _) hrowCost

theorem refinement_normalizer (side : Bool)
    (a : support.labels side) (rectangle : Bool) :
    (seed.refinement input support).normalizer side a rectangle =
      seed.occurrences.normalizer seed.phases side := rfl

/-- All passive and comparison labels share the same original common
scalar. Enlarging it independently would violate this identity. -/
theorem refinement_normalizer_eq (side : Bool)
    (a b : support.labels side) (rectangle₁ rectangle₂ : Bool) :
    (seed.refinement input support).normalizer side a rectangle₁ =
      (seed.refinement input support).normalizer side b rectangle₂ := rfl

theorem passiveMask_ne_zero : seed.ordinary.passiveMask ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro I hI
  exact (Finset.prod_ne_zero_iff.mp seed.phases.deletion_nonzero) I
    (Finset.mem_filter.mp hI).1

theorem passiveMask_dvd_originalDeletion :
    seed.ordinary.passiveMask ∣ seed.phases.deletionIdeal.val := by
  let mask := packet.second.physical.first.fullDeletion
  let residual := fun I : Ideal (𝓞 K) =>
    ¬I ∣ packet.second.physical.first.paidSupport.val
  refine ⟨∏ I ∈ mask.filter (fun I => ¬residual I), I, ?_⟩
  exact (Finset.prod_filter_mul_prod_filter_not mask residual id).symm

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.innerScalar_eq_original_frozen
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalSource_weight_eq_childWeight
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalSource_rowCost_le
