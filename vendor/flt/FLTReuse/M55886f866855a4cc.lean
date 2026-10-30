import FLTReuse.M55164c2a16500130
import FLTReuse.M1868db956c866c8d
import FLTReuse.Md136db2ac3c0205e

set_option autoImplicit false

open NumberField NumberField.AdelicFourier

theorem NumberField.AdelicFourier.comp_mul_mem_schwartzBruhat
    (F : Type) [Field F] [NumberField F] (y : (AdeleRing (𝓞 F) F)ˣ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    (fun x ↦ f (↑y * x)) ∈ schwartzBruhat F := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_comp_mul_mem_schwartzBruhat.solution
