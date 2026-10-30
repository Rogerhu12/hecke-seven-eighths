import Mathlib
import FLTReuse.M157b087506702f5d
import FLTReuse.M1868db956c866c8d
import FLTReuse.M4a7019b5ddf741a1

set_option autoImplicit false

open NumberField NumberField.TateGlobal NumberField.AdelicLevel IsDedekindDomain

theorem NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous
    (F : Type) [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, IsUnramifiedCharAt χ v := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous.solution
