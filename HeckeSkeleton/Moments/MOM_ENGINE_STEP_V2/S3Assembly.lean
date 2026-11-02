import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3Energy
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3Windows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3UniformDensity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3FrozenDivisor
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3RowExponent

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Assemble the one-pool source task from original column bounds

The only analytic preparation used here bounds the original finite
column carrier uniformly.  The original row exponent and every frozen
divisor then lie in a fixed box before a single pool is chosen.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

open NumberField IsDedekindDomain DedekindZetaZeroFree
open EngineStep EngineInduction.Source
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

theorem amplification_of_uniform_column_bound
    (c : TargetContext K) (p : SourceParameters c)
    (columns : ∀ frame : SourceFrame, ∃ B : ℝ, ∃ demand : UniformDemand,
      ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
        demand.Ready call input → ∀ F : FirstPresentation call p, F.Realizes →
        ∀ j ∈ F.source.columns,
          (Arithmetic.data c).exteriorNorm (F.source.ideal j) ≤ call.base ^ B) :
    AmplificationTask c p := by
  intro frame
  obtain ⟨B, columnDemand, hcolumns⟩ := columns frame
  obtain ⟨threshold, hthreshold, hpools⟩ := exists_source_pool_with_power_density c p
    (4 + recipeInductionSigma c / 8 + 4 * p.loss + recipeInductionSigma c) B
  let poolDemand : UniformDemand :=
    { orders := ∅
      threshold := threshold
      threshold_one_le := hthreshold.le }
  refine ⟨columnDemand.join poolDemand, ?_⟩
  intro call input hframe ready F hF family hfamily hW
  by_cases hslots : call.node.data.geometry.slotCount = 0
  · exact direct_solution hslots hW
  · obtain ⟨pool, hdensity⟩ := hpools call.base (UniformDemand.ready_right ready).large
    have hnorm := hcolumns call input hframe (UniformDemand.ready_left ready) F hF
    have hpower : ∀ i, call.base ^ (recipeInductionSigma c / 3 - 2 * p.loss) ≤
        pool.rowDensity (family.source i).rowExponent
          (idealLogLength call.base (family.source i).first.residualDivisor.val) := by
      intro i
      exact hdensity _ _ (cauchy_rowExponent_le hF hfamily i (hW i))
        (frozen_exponent_le hfamily i B hnorm)
    let P : PoolPresentation family := presentation pool hpower
    have hP : P.Realizes := presentation_realizes pool hpower
    exact ⟨expansion P, expansion_realizes P hslots hP,
      family_cost_le_expansion P hP, expansion_windows P hP hF hfamily hW⟩

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3.amplification_of_uniform_column_bound
