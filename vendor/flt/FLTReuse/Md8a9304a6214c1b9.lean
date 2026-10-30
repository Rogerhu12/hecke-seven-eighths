import FLTReuse.M157b087506702f5d
import FLTReuse.M0a341b9f001ae4d1
import FLTReuse.M1868db956c866c8d
import FLTReuse.M0178bf39c5ada6d0
-- The removed upstream instance instCountableOfNumberField_definitions is absent in this Mathlib.
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem NumberField.TateGlobal.ideleNorm_uniformizerIdele (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_ideleNorm_uniformizerIdele.solution
