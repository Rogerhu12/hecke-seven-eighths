import HeckeSkeleton.Main
import HeckeSkeleton.HighEulerAlgebra
import HeckeSkeleton.GramSectionRigidity
import HeckeSkeleton.HardNumerics
import HeckeSkeleton.HardLedger
import HeckeSkeleton.MarkedAnnularSupport
import HeckeSkeleton.LowExponent
import HeckeSkeleton.GramSectionReciprocity
import HeckeSkeleton.GramMaskTransport
import HeckeSkeleton.BufferedReciprocal
import HeckeSkeleton.HeckeBufferedReciprocal
import HeckeSkeleton.FunctionalEquationConductor
import HeckeSkeleton.ExplicitHeckeFunctionalEquation
import HeckeSkeleton.HeckeGammaReciprocal
import HeckeSkeleton.HeckeFixedTypeGammaBound
import HeckeSkeleton.HeckeStripPolynomial
import HeckeSkeleton.HeckeGammaQualitativeGrowth
import HeckeSkeleton.HeckeUniformStripGrowth
import HeckeSkeleton.HighNormBackgroundExclusion
import HeckeSkeleton.HeckeUniformBufferedControl
import HeckeSkeleton.HeckeFiniteBackgroundControl
import HeckeSkeleton.HeckePhysicalFamilyBufferedControl
import HeckeSkeleton.HeckeDynamicGammaBound
import HeckeSkeleton.HeckeHighRowLRatio
import HeckeSkeleton.HeckeConductorNorm
import HeckeSkeleton.HeckeDeletedEulerControl
import HeckeSkeleton.HeckeLRatioConductorBudget
import HeckeSkeleton.FiniteOrderKernelOpen
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Report both direct admissions and the actual constant-dependency graph.
An endpoint with sorryAx is expected here and is never called verified. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending : Array Name := #[`HeckeSkeleton.generalHeckeSevenEighths_skeleton]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if let some idx := env.getModuleIdxFor? name then
        if let some moduleName := env.allImportedModuleNames[idx]? then
          if (`HeckeSkeleton).isPrefixOf moduleName then
            let some info := env.find? name | throwError "Missing skeleton constant {name}"
            let deps := info.getUsedConstantsAsSet.toList
            let direct := deps.contains `sorryAx
            logInfo m!"SKELETON_DECL|{name}|{moduleName}|{direct}|{String.intercalate "," (deps.map toString)}"
            pending := pending ++ deps.toArray
  liftIO <| IO.println s!"SKELETON_GRAPH_VISITED|{seen.size}"
  let axioms ← Lean.collectAxioms `HeckeSkeleton.generalHeckeSevenEighths_skeleton
  for a in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound, `sorryAx].contains a do
      throwError "Unexpected endpoint axiom {a}"
  unless axioms.contains `sorryAx do
    throwError "Expected an explicitly incomplete skeleton; audit its changed status"
  logInfo m!"SKELETON_ENDPOINT_AXIOMS|{String.intercalate "," (axioms.toList.map toString)}"


/-! The following leaves are proved over the verified library, independently
of the remaining skeleton admissions. Mellin summability is audited at its
generic cutoff/decay theorem, not at the still conditional KP data instance. -/
open Lean Elab Command in
run_cmd do
  for name in #[`HeckeSkeleton.Gram.amplitude_finite_support,
      `HeckeSkeleton.Gram.amplitude_sixth_unit,
      `HeckeSkeleton.Gram.ordinary_frequency_count,
      `HeckeSkeleton.FiniteMellin.finite_absolute_mellin_of_valuation_cutoff_decay,
      `HeckeSkeleton.HighEulerCharacters.finiteOrder_ne_normTwist_iff,
      `HeckeSkeleton.HighEulerAlgebra.rowEulerRational_eq_cancelled,
      `HeckeSkeleton.HighEulerAlgebra.rowEulerCancelledValue_W_one,
      `HeckeSkeleton.HighEulerAlgebra.localRowCorrection_at_W_one,
      `HeckeGeneral.ThetaSkeleton.Physical.localRowCorrection_eq_literal_of_initial,
      `HeckeGeneral.ThetaSkeleton.Physical.localRowCorrection_eq_literal_of_rowEulerRegion,
      `HeckeGeneral.ThetaSkeleton.Physical.localRowCorrection_negativeStrip_bound,
      `HeckeSkeleton.GramSectionRigidity.reciprocal_twist_fiber_rigidity,
      `HeckeSkeleton.GramSectionRigidity.reciprocal_twist_factors_through_labels,
      `HeckeSkeleton.GramSectionRigidity.sameGenerator_nested_literal_quotient,
      `HeckeSkeleton.HardNumerics.high_row_scale_identity,
      `HeckeSkeleton.HardNumerics.omitted_slot_normalization_cost,
      `HeckeSkeleton.HardNumerics.paired_comparison_capacity_margin,
      `HeckeSkeleton.HardNumerics.paired_comparison_endpoint_margin,
      `HeckeSkeleton.HardLedger.common_support_local,
      `HeckeSkeleton.HardLedger.greedy_prefix_capacity_and_cost,
      `HeckeSkeleton.HardLedger.greedy_cost_from_defect,
      `HeckeSkeleton.HardLedger.inverse_child_width_drop,
      `HeckeSkeleton.MarkedAnnularSupport.completedTerm_summable_of_annular,
      `HeckeSkeleton.LowExponent.hybrid_gain_dichotomy,
      `HeckeSkeleton.LowExponent.hybrid_and_kernel_quarter,
      `HeckeSkeleton.LowExponent.dual_length_le,
      `HeckeSkeleton.LowExponent.reflected_exponent_le,
      `HeckeSkeleton.GramSectionReciprocity.idealSymbol_one,
      `HeckeSkeleton.GramSectionReciprocity.sectionRatio_reciprocity,
      `HeckeSkeleton.GramMaskTransport.exact_mask_transport_on,
      `HeckeSkeleton.GramMaskTransport.exists_finite_local_label,
      `HeckeSkeleton.GramMaskTransport.transportMask_eq_of_div_mem,
      `HeckeSkeleton.GramMaskTransport.transportMask_subgroup_mul_right,
      `HeckeSkeleton.BufferedReciprocal.LogarithmicControl.logarithmic_control,
      `HeckeSkeleton.BufferedReciprocal.LogarithmicControl.absorb_polynomial_constant,
      `HeckeSkeleton.BufferedReciprocal.LogarithmicControl.same_height_mem_disk,
      `HeckeSkeleton.BufferedReciprocal.buffered_value_and_reciprocal_of_rectangle,
      `HeckeSkeleton.HeckeBufferedReciprocal.continuation_ne_zero_of_upper,
      `HeckeSkeleton.HeckeBufferedReciprocal.numerator_mem_physicalRowFamily,
      `HeckeSkeleton.HeckeBufferedReciprocal.denominator_mem_physicalRowFamily,
      `HeckeSkeleton.HeckeBufferedReciprocal.hecke_value_and_reciprocal_of_upper,
      `HeckeSkeleton.HeckeBufferedReciprocal.hecke_subpower_of_upper_strip_growth,
      `HeckeSkeleton.ActualEulerLogarithm.idealEulerLog_differentiableOn,
      `HeckeSkeleton.ActualEulerLogarithm.exp_idealEulerLog_eq_series,
      `HeckeSkeleton.ActualEulerLogarithm.exists_uniform_heckeEulerLog_bound,
      `HeckeSkeleton.FunctionalEquationConductor.fltConductorExponent_eq_localConductorExponent,
      `HeckeSkeleton.FunctionalEquationConductor.fltHeckeConductor_eq_discr_mul_finiteConductor,
      `HeckeSkeleton.FunctionalEquationConductor.conductorOf_eq_discr_mul_finiteConductor,
      `HeckeSkeleton.FunctionalEquationConductor.fltHeckeConductor_mul_normTwist,
      `HeckeSkeleton.FunctionalEquationConductor.fltHeckeConductor_normTwist,
      `HeckeSkeleton.ExplicitHeckeFunctionalEquation.exists_completed_functionalEquation_explicitScale_of_nonNorm,
      `HeckeSkeleton.HeckeGammaReciprocal.differentiable_heckeGammaReciprocal,
      `HeckeSkeleton.HeckeGammaReciprocal.heckeGammaProfile_ne_zero_of_re_pos,
      `HeckeSkeleton.HeckeGammaReciprocal.heckeContinuation_eq_canonicalReciprocal_mul_completed_of_nonNorm,
      `HeckeSkeleton.HeckeGammaReciprocal.exists_uncompleted_functionalEquation_left_of_one,
      `HeckeSkeleton.HeckeFixedTypeGammaBound.gamma_real_shift_ratio_bound,
      `HeckeSkeleton.HeckeFixedTypeGammaBound.gammaC_fixedType_reflected_left_bound,
      `HeckeSkeleton.HeckeStripPolynomial.norm_le_on_closed_strip_of_polynomial_boundary,
      `HeckeSkeleton.HeckeGammaQualitativeGrowth.gamma_inverse_strip_exp_bound,
      `HeckeSkeleton.HeckeGammaQualitativeGrowth.gammaC_inverse_shifted_strip_exp_bound,
      `HeckeSkeleton.HeckeGammaQualitativeGrowth.gammaR_inverse_shifted_strip_exp_bound,
      `HeckeSkeleton.HeckeUniformStripGrowth.heckeContinuation_quadratic_strip_growth,
      `HeckeSkeleton.HeckeUniformStripGrowth.exists_uniform_fixedType_strip_bound,
      `HeckeSkeleton.HighNormBackgroundExclusion.norm_twist_parameter_forced,
      `HeckeSkeleton.HighNormBackgroundExclusion.finite_target_rows,
      `HeckeSkeleton.HighNormBackgroundExclusion.eventually_excludes_background_norm_twists,
      `HeckeSkeleton.HighNormBackgroundExclusion.high_rows_exclude_background_norm_twists,
      `HeckeSkeleton.HeckeUniformBufferedControl.exists_uniform_fixedType_buffered_control,
      `HeckeSkeleton.HeckeFiniteBackgroundControl.all_complex_of_primitive12,
      `HeckeSkeleton.HeckeFiniteBackgroundControl.radialParameters_mul_finiteOrder,
      `HeckeSkeleton.HeckeFiniteBackgroundControl.archWeight_mul_finiteOrder_of_complex,
      `HeckeSkeleton.HeckeFiniteBackgroundControl.exists_uniform_finiteBackground_buffered_control,
      `HeckeSkeleton.HeckePhysicalFamilyBufferedControl.physical_member_background_decomposition,
      `HeckeSkeleton.HeckePhysicalFamilyBufferedControl.exists_uniform_physicalFamily_buffered_control,
      `HeckeSkeleton.HeckePhysicalFamilyBufferedControl.exists_uniform_high_physicalFamily_buffered_control,
      `HeckeSkeleton.HeckeDynamicGammaBound.gammaC_reflected_dynamic_bound,
      `HeckeSkeleton.HeckeDynamicGammaBound.canonicalGammaProfile_finiteOrder_of_complex,
      `HeckeSkeleton.HeckeDynamicGammaBound.exists_uniform_finiteOrder_reflectedGamma_bound,
      `HeckeSkeleton.HeckeHighRowLRatio.exists_uniform_high_row_LRatio_bound,
      `HeckeSkeleton.HeckeConductorNorm.finiteConductor_mul_dvd,
      `HeckeSkeleton.HeckeConductorNorm.finiteConductor_mul_norm_le,
      `HeckeSkeleton.HeckeConductorNorm.conductorScale_pos,
      `HeckeSkeleton.HeckeConductorNorm.conductorScale_inv,
      `HeckeSkeleton.HeckeConductorNorm.conductorScale_mul_le,
      `HeckeSkeleton.HeckeConductorNorm.conductorScale_mul_conjugate_le,
      `HeckeSkeleton.HeckeDeletedEulerControl.deletionUpperConstant_pos,
      `HeckeSkeleton.HeckeDeletedEulerControl.deletionInverseConstant_pos,
      `HeckeSkeleton.HeckeDeletedEulerControl.norm_actual_eulerPolynomial_le,
      `HeckeSkeleton.HeckeDeletedEulerControl.norm_actual_localEulerFactor_le,
      `HeckeSkeleton.HeckeDeletedEulerControl.norm_heckeEulerDeletionPolynomial_le,
      `HeckeSkeleton.HeckeDeletedEulerControl.deletionPolynomial_inv_eq_prod_localEulerFactors,
      `HeckeSkeleton.HeckeDeletedEulerControl.norm_heckeEulerDeletionPolynomial_inv_le,
      `HeckeSkeleton.HeckeDeletedEulerControl.exists_uniform_fixedDeletion_bounds,
      `HeckeSkeleton.HeckeDeletedEulerControl.exists_uniform_deletedL_ratio_transfer,
      `HeckeSkeleton.HeckeLRatioConductorBudget.backgroundConductorBudget_pos,
      `HeckeSkeleton.HeckeLRatioConductorBudget.conductorPowers_le_radicalPower,
      `HeckeSkeleton.HeckeLRatioConductorBudget.exists_uniform_conductorPower_budget,
      `HeckeSkeleton.HeckeLRatioConductorBudget.conductorPowers_le_with_radicalDeficit,
      `HeckeSkeleton.FiniteOrderKernelOpen.isOpen_fiber_of_continuous_finite_range,
      `HeckeSkeleton.FiniteOrderKernelOpen.isOpen_ker_of_finite_range,
      `HeckeSkeleton.FiniteOrderKernelOpen.finite_circle_roots,
      `HeckeSkeleton.FiniteOrderKernelOpen.finite_range_circle_of_pow_eq_one,
      `HeckeSkeleton.FiniteOrderKernelOpen.isOpen_ker_circle_of_pow_eq_one,
      `HeckeSkeleton.FiniteOrderKernelOpen.isOpen_ker_circle_of_finiteOrder,
      `HeckeSkeleton.FiniteOrderKernelOpen.isOpen_ker_localComponent_of_finiteOrder,
      `HeckeSkeleton.HighCountAssembly.piece_count_bound,
      `HeckeSkeleton.HighCountAssembly.norm_label_sum_le,
      `HeckeSkeleton.HighCountAssembly.label_loss_bound,
      `HeckeSkeleton.ActualCanonicalRowConsumers.highRadicalBound_for_every_provider,
      `HeckeSkeleton.ActualCanonicalRowConsumers.exists_uniform_actual_high_row_LRatio_bound,
      `HeckeGeneral.ThetaSkeleton.Physical.rowCharacterInput_ne_normTwist_of_not_principal,
      `HeckeGeneral.ThetaSkeleton.Physical.actual_probeIntegralInput,
      `HeckeGeneral.Characters.NormPullbackDraft.mathlibIdeleClassNorm,
      `HeckeSkeleton.Descent.normOnClasses,
      `HeckeGeneral.ThetaSkeleton.Global.thetaGenerator_productNorm] do
    let axioms ← Lean.collectAxioms name
    for a in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unexpected proved-leaf axiom {a} in {name}"
    logInfo m!"PROVED_T_LEAF_AXIOMS|{name}|{String.intercalate "," (axioms.toList.map toString)}"
