import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveUniformEngine
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalMeshDirectEngine
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalMeshPooledEngine

/-!
# The authoritative engine with the original independent mesh

The owner now carries the original per-slot mesh through its literal
construction at immutable revision
f9eba0adee99dbd28dfedbf8d4357dac9147f005. These transparent names preserve
the induction task's existing consumers while using that same producer,
constants, selected children and positive kernels directly. The analytic
cutoff loss remains independent, and the mass exponent is epsilon plus
the original mesh. No local copy of the analytic proof is retained.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.OriginalMeshUniformEngine

abbrev threshold := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine.threshold
abbrev threshold_gt_one := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine.threshold_gt_one
abbrev threshold_spec := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine.threshold_spec
abbrev constant := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine.constant
abbrev constant_pos := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine.constant_pos
abbrev produce := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine.produce

end HeckeSkeleton.Moments.EngineInduction.OriginalMeshUniformEngine

#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshUniformEngine.threshold_gt_one
#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshUniformEngine.constant_pos
#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshUniformEngine.produce
