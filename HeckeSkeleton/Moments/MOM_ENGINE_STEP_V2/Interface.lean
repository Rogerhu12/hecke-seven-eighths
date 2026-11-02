import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StepHypothesis
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.Output

set_option linter.unusedSectionVars false

/-!
# Compact paired-engine step (V2)

This module is the entry point for a separate implementation of the
paired-engine single step. The target declaration is
`HeckeSkeleton.Moments.EngineInduction.Source.PairedStepHypothesis`.

The implementation is deliberately isolated from the original
`EngineStep` namespace. In particular, this file does not introduce
a new hypothesis or claim that the target is already proved.
-/

namespace HeckeSkeleton.Moments.EngineStepV2

-- Shared finite-leaf and side-parametric constructions will be imported here.
-- The bridge to the existing induction hypothesis will be added only after
-- the common declarations have passed the dedicated CI compilation.

end HeckeSkeleton.Moments.EngineStepV2
