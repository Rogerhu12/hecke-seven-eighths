module

public import FLTReuse.Md2cadaa4525e04a6
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.M4483977df89d59a8

@[expose] public section

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors
theorem NumberField.AdelicBox.exists_ne_zero_forall_addChar_mul_eq_one
    (F : Type) [Field F] [NumberField F]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
      ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_exists_ne_zero_forall_addChar_mul_eq_one.solution
