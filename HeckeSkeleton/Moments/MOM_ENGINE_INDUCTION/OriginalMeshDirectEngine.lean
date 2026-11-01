import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveDirectEngine
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalMeshEngineMass

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

namespace HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe

abbrev literalOriginalMeshDirectEngineExceptionalCost := @HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectEngineExceptionalCost
abbrev literalOriginalMeshDirectEngine := @HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectEngine

end HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalMeshDirectEngine
