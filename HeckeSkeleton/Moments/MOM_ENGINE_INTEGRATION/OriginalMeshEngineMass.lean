import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineMassChoices

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

namespace HeckeSkeleton.Moments.EngineInduction.OriginalMeshEngineMass

abbrev massLoss := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.massLoss
abbrev massLoss_pos := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.massLoss_pos
abbrev degree := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.degree
abbrev degree_eq := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.degree_eq
abbrev tilt_eq_actual := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.tilt_eq_actual
abbrev rawWidth_eq := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.rawWidth_eq
abbrev contour := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.contour
abbrev contour_pos := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.contour_pos
abbrev contour_le_quarter := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.contour_le_quarter
abbrev contour_eq_actual := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.contour_eq_actual
abbrev directConstant := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.directConstant
abbrev pooledConstant := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.pooledConstant
abbrev directConstant_pos := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.directConstant_pos
abbrev pooledConstant_pos := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.pooledConstant_pos
abbrev constant := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.constant
abbrev constant_pos := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.constant_pos
abbrev directConstant_le := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.directConstant_le
abbrev pooledConstant_le := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.pooledConstant_le
abbrev pooledThreshold := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.pooledThreshold
abbrev pooledThreshold_gt_one := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.pooledThreshold_gt_one
abbrev direct_exponent_le := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.direct_exponent_le
abbrev pooled_exponent_le := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.pooled_exponent_le
abbrev direct_bound := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.direct_bound
abbrev pooled_bound := @HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.pooled_bound

end HeckeSkeleton.Moments.EngineInduction.OriginalMeshEngineMass

#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshEngineMass.degree_eq
#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshEngineMass.contour_pos
#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshEngineMass.contour_le_quarter
#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshEngineMass.contour_eq_actual
#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshEngineMass.constant_pos
#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshEngineMass.pooledThreshold_gt_one
#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshEngineMass.direct_bound
#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshEngineMass.pooled_bound
