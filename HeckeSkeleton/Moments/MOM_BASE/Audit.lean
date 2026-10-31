import HeckeSkeleton.Moments.MOM_BASE.CanonicalCalibration
import HeckeSkeleton.Moments.MOM_BASE.Marks
import HeckeSkeleton.Moments.MOM_BASE.PairedContext

/-! Public entry-point audit for MOM_BASE. CI checks every printed axiom
set against exactly `propext`, `Classical.choice`, and `Quot.sound`. -/

#print axioms HeckeSkeleton.Moments.MOM_BASE.canonical_cube_calibration
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonical_first_transform
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonical_second_transform
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonical_gamma_two_norm
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalCoefficient_norm
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonical_G_finiteOrder
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalPeriod_coefficient
#print axioms HeckeSkeleton.Moments.MOM_BASE.exteriorSymbolHom_apply
#print axioms HeckeSkeleton.Moments.MOM_BASE.idealSymbol_mul_denominator
#print axioms HeckeSkeleton.Moments.MOM_BASE.idealSymbol_mul_numerator
#print axioms HeckeSkeleton.Moments.MOM_BASE.idealSymbol_pow_numerator
#print axioms HeckeSkeleton.Moments.MOM_BASE.idealSymbol_sixth_power_mask
#print axioms HeckeSkeleton.Moments.MOM_BASE.idealSymbol_twelfth_power_mask
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalTau_apply
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalTau_label
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalTau_cube_phase
#print axioms HeckeSkeleton.Moments.MOM_BASE.norm_frozen_phase_le_one
#print axioms HeckeSkeleton.Moments.MOM_BASE.tsum_moebius_dilates
#print axioms HeckeSkeleton.Moments.MOM_BASE.tsum_moebius_cube_dilates
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalCompletedTerm_finite_support
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalCompletedTerm_cube_extract
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalCubeInversion_summable
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalCubeInversion
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalCubeInversion_of_hasCompactSupport
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalVstar_ideal_normalization
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalCompletedTerm_eq_actual
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalCompletedSum_eq_weightedTheta
#print axioms HeckeSkeleton.Moments.MOM_BASE.actualCompletedSummand
#print axioms HeckeSkeleton.Moments.MOM_BASE.canonicalThetaBridge
#print axioms HeckeSkeleton.Moments.MOM_BASE.actual_mark_priority
#print axioms HeckeSkeleton.Moments.MOM_BASE.frozen_label_mask
#print axioms HeckeSkeleton.Moments.MOM_BASE.frozen_phase_joint_contraction
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.originalPrimeMask_mul
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.paired_primeCoefficient
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.paired_relativeCoefficient
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.paired_finite_slot
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.Presentation.prime_pairing
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.Presentation.finiteTwist_prime_pairing
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.Presentation.conjugate_prime_pairing
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.two_finite_transforms_prime_pairing
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.two_finite_transforms_finiteOrder
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.idealCoefficient_character_mul
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.norm_idealCoefficient_of_unramified
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.whole_product_extraction
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.whole_product_common_cancellation
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.two_finite_transforms_whole_background
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.originalPairedPrimePolynomial_eq_masked
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.originalPairedPrimePolynomial_eq
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.primePolynomial_character_finite
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.paired_polynomial_orientation
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.centered_polynomial_orientation
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.context_finite_prime_pairing
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.context_common_cancellation
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.context_frozen_background
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.context_originalPrimePolynomial_eq_masked
#print axioms HeckeSkeleton.Moments.MOM_BASE.Paired.context_originalPrimePolynomial_eq
