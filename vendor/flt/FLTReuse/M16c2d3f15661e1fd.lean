import FLTReuse.Mb34f70d821d13751
import FLTReuse.M8c02cd87427fd145
import FLTReuse.Mfa16ee9aa60c0bfe
import FLTReuse.Mff82fa6a210654a3
import FLTReuse.Ma9ad8acc40984aa2
import FLTReuse.Mb4072e15f985c10c
import FLTReuse.Mb7d8fcabdb78d9cd
import FLTReuse.M1868db956c866c8d
namespace P2MW.S_LanglandsTunnell_HeckeTate_finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi   IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal    Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers  
attribute [-simp] SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul

set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell NumberField.TateGlobal LanglandsTunnell.TateLocal
open LanglandsTunnell.Converse
open scoped nonZeroDivisors

theorem solution
    (F : Type) [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχ : IsAdmissibleTwist F χ) :
    {v : HeightOneSpectrum (𝓞 F) | stdRootNumberAt F v (localChar χ v) ≠ 1}.Finite ∧
      {v : HeightOneSpectrum (𝓞 F) | pinnedExp F χ v ≠ 0}.Finite := by
  have hadm := _hχ
  unfold IsAdmissibleTwist at hadm
  obtain ⟨_, hcont, hunit⟩ := hadm
  refine ⟨?_, finite_setOf_pinnedExp_ne_zero_of_continuous F χ hcont⟩
  obtain ⟨S, hS⟩ := exists_finset_forall_isUnramifiedCharAt_of_continuous F χ hcont
  have hlev : {v : HeightOneSpectrum (𝓞 F) | addCharLevel (NumberField.StandardAddChar.psiLocal F v) ≠ 0}.Finite := by
    have h := FractionalIdeal.finite_factors (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    rwa [addCharLevel_psiLocal_eq_count_differentIdeal F v] at hv
  refine (hlev.union S.finite_toSet).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  by_contra hnot
  simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, not_or, not_not] at hnot
  obtain ⟨hlev0, hvS⟩ := hnot
  exact hv (stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero F v (localChar χ v)
    (hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt F χ v (hS v hvS))
    (hunit _) hlev0 (psiLocal_ne_one F v))
