module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4CalibrationBinding
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4SourceConditions

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: source conditions for the exact original N3 recipe

The calibration binding identifies the same canonical source, original
factor list, complete remaining mask and finite row image. A row from
the original live class supplies the pattern witness before ordinary
restriction. The original source trace proves the support atoms and
the two physical windows, hence both source budgets.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} {input : ProfileInput call}
variable {seed : OrdinarySeed packet} {support : seed.ordinary.PassiveSupport input}
variable {side : Bool} {a : support.labels side} {rectangle : Bool}
variable {D : OriginalCalibration call (seed.canonicalSource input support side a rectangle)}
variable {pattern : Fin packet.block.primeCount → Bool}

/-- The exact N3 binding has no support or joint budget field. Both
budgets are derived from the same actual physical source here. -/
def conditionsOfBinding
    (binding : CalibrationBinding seed support side a rectangle D pattern)
    (hpacket : packet.Realizes) : D.SourceConditions := by
  let h0 : packet.R.live := Classical.choice (packet_live_nonempty packet hpacket)
  let h : packet.R.NonunitClass (Arithmetic.context c) pattern :=
    ⟨h0, binding.pattern_actual h0⟩
  exact sourceConditions_of_exact_recipe seed input support hpacket side a rectangle D pattern h
    binding.moving binding.remaining binding.m binding.q binding.allowed_exact
    binding.timeIndependent binding.primeSupport

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.conditionsOfBinding
