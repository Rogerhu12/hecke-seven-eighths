import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafRowZero

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option Elab.async false
set_option stderrAsMessages false

/-!
# S6: omitted original classes have both costs zero

The carrier is the intersection of the original leaf's `Live` predicate
with the original second class's `Active` predicate. Each of the four
ways that a class can be inactive is discharged on its stored weight,
whole column coefficient, or complete correlation. No kernel, row, or
coefficient is replaced in passing to this exact finite carrier.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

local instance finiteLeavesCircleFintype : Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) :=
  Fintype.ofFinite _

variable {K : Type} [Field K] [NumberField K]

namespace FiniteLeavesSupport

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: start"
    stderr.flush

/-- A zero complete row correlation removes both original terms. -/
theorem costs_zero_of_rowWeight_zero {H : Type*}
    (B : ActualHybridLeaf K H ℝ ℝ)
    (hz : ∀ h ∈ B.rows, B.rowWeight h = 0) :
    B.exceptionalCost = 0 ∧ B.ordinaryCost = 0 := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: rowWeight enter"
    stderr.flush
  refine ⟨B.exceptionalCost_eq_zero_of_rowWeight_zero hz, ?_⟩
  have hi (z : ℝ × ℝ) : B.ordinaryIntegrand z = 0 := by
    have hl : jointColumnEnergy (B.rows.filter (fun h => ¬B.exceptional h)) B.left
        B.rowWeight B.leftCoefficient
        (fun h i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i))
        (WithLp.toLp 2 z) = 0 := by
      apply Finset.sum_eq_zero
      intro h hh
      simp only [hz h (Finset.mem_filter.mp hh).1, norm_zero, zero_mul]
    change Real.sqrt _ * Real.sqrt _ = 0
    rw [hl, Real.sqrt_zero, zero_mul]
  simp only [ActualHybridLeaf.ordinaryCost, hi, integral_zero, mul_zero]

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: rowWeight complete"
    stderr.flush

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}

/-- An empty physical row set has its actual fibre multiplicity zero. -/
theorem orbitMultiplicity_eq_zero (source : PhysicalSource call p)
    (hrows : ¬source.source.rows.Nonempty) : source.orbitMultiplicity = 0 := by
  have he : source.source.rows = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrows
  simp only [PhysicalSource.orbitMultiplicity, he, Finset.image_empty,
    Finset.sup_empty]

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: orbitMultiplicity complete"
    stderr.flush

variable (covers : RawCovers second)

/-- The positive outer weight, physical row set, active common pair,
and nonzero complete correlation are all necessary for a nonzero cost. -/
theorem costs_zero_of_not_active (hsecond : second.Realizes) (key : covers.Key)
    (hinactive : ¬(covers.classKey key).Active) :
    (covers.leaf key).exceptionalCost = 0 ∧
      (covers.leaf key).ordinaryCost = 0 := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive enter"
    stderr.flush
  let source := second.source key.1.1
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive source"
    stderr.flush
  have hs : source.Realizes := hsecond.stage key.1.1
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive realizes"
    stderr.flush
  by_cases houter : 0 < source.physical.outerWeight
  · by_cases hrows : source.physical.source.rows.Nonempty
    · by_cases hcommon : key.1.2.1.val ∈ source.physical.activeCommon
      · run_tac do
          let stderr ← IO.getStderr
          stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive correlation branch"
          stderr.flush
        have hlive : ¬((covers.classKey key).R.live).Nonempty := by
          intro h
          exact hinactive ⟨houter, hrows, hcommon, h⟩
        run_tac do
          let stderr ← IO.getStderr
          stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive correlation empty"
          stderr.flush
        apply costs_zero_of_rowWeight_zero
        run_tac do
          let stderr ← IO.getStderr
          stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive rowWeight applied"
          stderr.flush
        intro h hh
        have hc : (covers.classKey key).R.correlation h = 0 := by
          by_contra hn
          exact hlive ⟨h, Finset.mem_filter.mpr ⟨hh, hn⟩⟩
        change (covers.classKey key).R.weight h *
          (covers.classKey key).R.correlation h = 0
        rw [hc, mul_zero]
      · run_tac do
          let stderr ← IO.getStderr
          stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive common branch"
          stderr.flush
        apply (covers.leaf key).costs_zero_of_not_live
        run_tac do
          let stderr ← IO.getStderr
          stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive notLive applied"
          stderr.flush
        intro hlive
        obtain ⟨h, hh, j, hj, hn⟩ := hlive.2.1
        run_tac do
          let stderr ← IO.getStderr
          stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive column witness"
          stderr.flush
        apply hn
        have hc : (source.stage.charts key.1.2.1 key.1.2.2.1).leftCoefficient
            ((SourceClassKey.leftReindex key.1.2).index j) = 0 := by
          run_tac do
            let stderr ← IO.getStderr
            stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive coefficient rewrite"
            stderr.flush
          rw [hs.leftCoefficient]
          simp only [hcommon, if_false]
        change (((source.stage.charts key.1.2.1 key.1.2.2.1).leftCoefficient
          ((SourceClassKey.leftReindex key.1.2).index j) * _) * _) * _ = 0
        rw [hc]
        simp only [zero_mul]
    · run_tac do
        let stderr ← IO.getStderr
        stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive rows branch"
        stderr.flush
      have hf : source.stage.fiber = 0 :=
        hs.fiber.trans (orbitMultiplicity_eq_zero source.physical hrows)
      have hw : (covers.leaf key).weight = 0 := by
        change (source.physical.outerWeight * (source.stage.fiber : ℝ)) * _ = 0
        rw [hf]
        simp only [Nat.cast_zero, mul_zero, zero_mul]
      exact ⟨(covers.leaf key).exceptionalCost_eq_zero_of_weight_eq_zero hw,
        (covers.leaf key).ordinaryCost_eq_zero_of_weight_eq_zero hw⟩
  · run_tac do
      let stderr ← IO.getStderr
      stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive outer branch"
      stderr.flush
    have ho : source.physical.outerWeight = 0 :=
      le_antisymm (not_lt.mp houter) source.physical.outerWeight_nonneg
    have hw : (covers.leaf key).weight = 0 := by
      change (source.physical.outerWeight * _) * _ = 0
      rw [ho]
      simp only [zero_mul]
    exact ⟨(covers.leaf key).exceptionalCost_eq_zero_of_weight_eq_zero hw,
      (covers.leaf key).ordinaryCost_eq_zero_of_weight_eq_zero hw⟩

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: inactive complete"
    stderr.flush

/-- Exact omission criterion, separately for both original costs. -/
theorem costs_zero_of_not_retained (hsecond : second.Realizes) (key : covers.Key)
    (hkey : ¬((covers.leaf key).Live ∧ (covers.classKey key).Active)) :
    (covers.leaf key).exceptionalCost = 0 ∧
      (covers.leaf key).ordinaryCost = 0 := by
  by_cases hlive : (covers.leaf key).Live
  · exact costs_zero_of_not_active covers hsecond key (fun h => hkey ⟨hlive, h⟩)
  · exact (covers.leaf key).costs_zero_of_not_live hlive

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 FiniteLeavesSupport checkpoint: retained complete"
    stderr.flush

end FiniteLeavesSupport
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeavesSupport.costs_zero_of_not_active
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeavesSupport.costs_zero_of_not_retained
