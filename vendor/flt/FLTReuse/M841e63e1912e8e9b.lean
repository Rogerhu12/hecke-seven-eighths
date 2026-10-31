import Mathlib
import FLTReuse.M157b087506702f5d
import FLTReuse.M40aeee35a98f067b
import FLTReuse.M0a341b9f001ae4d1
import FLTReuse.M1868db956c866c8d
import FLTReuse.Mbbd20d45a2a367d5
attribute [-instance] NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers     IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal   
attribute [-simp] AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal AutomorphicForm

theorem NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 K) K χ)
    (hχ1 : ∀ x ∈ normOneIdeles K, χ x = 1) :
    ∃ t : ℝ, χ = normPowChar K t := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles.solution
