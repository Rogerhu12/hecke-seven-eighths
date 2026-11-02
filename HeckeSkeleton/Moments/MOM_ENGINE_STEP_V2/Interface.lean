import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CoveredStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FiniteKernelFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.HybridExpansion
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.KernelCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LeafCoverage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LeafNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LocalProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.Output
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PreparedCall
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ScalarLedger
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceFrame
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceHypothesis
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.StrictFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TerminalCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformChoices

set_option linter.unusedSectionVars false

/-!
# Compact paired-engine step

This entry point imports the complete V2 statement skeleton. The source
producer retains the original request, literal leaves, one selected pool,
the same two-sided kernels, all four terminals and the exact recursive
invariant. No shared STEP or INDUCTION declaration is changed.

The statement-skeleton phase explicitly permits unfinished proofs in the
unproved groups recorded in .github/v2/manifest.json. A proved group is
checked by a fresh recursive kernel-axiom audit. The full target remains
unfinished until every production obligation has been discharged.
-/

#print axioms HeckeSkeleton.Moments.EngineStepV2.pairedStepHypothesis
