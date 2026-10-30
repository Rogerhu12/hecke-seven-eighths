import FLTReuse.M3c68c1555d4fc687
import FLTReuse.M1868db956c866c8d
import FLTReuse.M3e65066309eb12af
attribute [-instance] NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers     IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal   
attribute [-simp] NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

theorem LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm (K : Type) [Field K]
    [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :
    modulus x = ‖x‖₊ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm.solution
