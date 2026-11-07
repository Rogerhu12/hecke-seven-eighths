module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyCore

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Uniform quantifier assembly

This is only the final logical adapter. Its two inputs are supplied by the
separate blueprint tasks and their explicit assembly. It neither asserts
their existence nor imports a theorem whose proof remains unfinished.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source
open Blueprint

variable {K : Type} [Field K] [NumberField K]

local instance uniformReflectionMeasurable : MeasurableSpace (ℕ × Bool) := ⊤
local instance uniformReflectionSingleton : MeasurableSingletonClass (ℕ × Bool) := by
  constructor
  intro x
  trivial

/-- The original target follows after uniform preparation and the local
construction have been supplied, in exactly that quantifier order. -/
theorem pairedStepHypothesis_of_preparations (c : TargetContext K)
    (prepare : ∀ frame : SourceFrame, UniformPreparation c frame)
    (produce : ∀ (frame : SourceFrame) (Cp Hp : ℝ)
      (hCp : 0 < Cp) (hminimum : (prepare frame).schedule.minimumCp ≤ Cp)
      (hHp : 0 ≤ Hp)
      (request : (prepare frame).Request Cp Hp hCp hminimum hHp)
      (frequency : ℝ × ℝ),
      let call := (prepare frame).toCall request frequency
      call.node.EngineOutput (Ω := EngineParameter)
        call.base (recipeInductionSigma c) (recipeInductionEdgeLoss c)
        (recipeInductionTerminalLoss c)
        call.prepared.engineCoefficient call.prepared.engineControl
        (admissibleOfInvariant call.primitive)) :
    PairedStepHypothesis EngineParameter c := by
  constructor
  intro lower upper hlower hlowerSmall hupper hinterval
    decay hdecay reflection hreflection
  let frame : SourceFrame := {
    lower := lower
    upper := upper
    lower_pos := hlower
    lower_small := hlowerSmall
    upper_large := hupper
    interval := hinterval
    decay := decay
    decay_gt_one := hdecay
    reflection := reflection
    reflection_order := hreflection }
  let preparation := prepare frame
  refine ⟨preparation.schedule.engine, preparation.schedule.minimumCp, ?_⟩
  intro Cp Hp hCp hminimum hHp
  refine ⟨strictFamily c frame preparation.schedule Cp Hp
    (preparation.bounds Cp Hp hCp hminimum hHp) ?_⟩
  intro request
  exact ⟨strictBranch request
    (preparation.prepared Cp Hp hCp hminimum hHp request)
    (produce frame Cp Hp hCp hminimum hHp request)
    (preparation.budget Cp Hp hCp hminimum hHp request)⟩

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.pairedStepHypothesis_of_preparations
