import FLTReuse.M157b087506702f5d
import FLTReuse.M1868db956c866c8d
import FLTReuse.Mea34a23e4d889544
-- The removed upstream instance instCountableOfNumberField_definitions is absent in this Mathlib.
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm

theorem NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult (F : Type) [Field F] [NumberField F]
    (X : AdelicGL2 (𝓞 F) F) (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det X) = ∏ w : InfinitePlace F, archDetNorm w X ^ w.mult := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.solution
