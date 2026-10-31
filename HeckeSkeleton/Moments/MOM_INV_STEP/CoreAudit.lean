import HeckeSkeleton.Moments.MOM_INV_STEP.Interface
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLabelFibers
import HeckeSkeleton.Moments.MOM_INV_STEP.FourierSeparation
import HeckeSkeleton.Moments.MOM_INV_STEP.SourceLengths

/-! This independent audit records the finite reconstruction interface even if
another analytic module fails.  The workflow still requires `Audit` to pass. -/

#print axioms HeckeSkeleton.Moments.MOMInvStep.physical_prefactor_identity
#print axioms HeckeSkeleton.Moments.MOMInvStep.physical_block_scalar_budget
#print axioms HeckeSkeleton.Moments.MOMInvStep.ChildGeometry.step
#print axioms HeckeSkeleton.Moments.MOMInvStep.FirstLabelFibers.source_energy_bound
#print axioms HeckeSkeleton.Moments.MOMInvStep.FixedTripleFibers.exists_sourceTriples_normalized_mass_bound
#print axioms HeckeSkeleton.Moments.MOMInvStep.FixedTripleEnergy.normalizedChildEnergy_eq
#print axioms HeckeSkeleton.Moments.MOMInvStep.FixedTripleEnergy.ReconstructionPacket.signedValue_le_normalized
#print axioms HeckeSkeleton.Moments.MOMInvStep.fixed_triple_energy_step
#print axioms HeckeSkeleton.Moments.MOMInvStep.canonical_child_geometry
#print axioms HeckeSkeleton.Moments.MOMInvStep.SourceLengths.puncture_length_from_source
