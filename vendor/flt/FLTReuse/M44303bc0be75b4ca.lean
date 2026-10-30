import FLTReuse.Md2cadaa4525e04a6
import FLTReuse.M1868db956c866c8d
import FLTReuse.M3023cf61fe2bb5e2

open NumberField NumberField.AdelicBox IsDedekindDomain
theorem NumberField.AdelicBox.exists_denom_of_hasCompactSupport
    {F : Type*} [Field F] [NumberField F]
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ κ : F, h (algebraMap F (FiniteAdeleRing (𝓞 F) F) κ) ≠ 0 →
      ∃ a : 𝓞 F, (d : F) * κ = a := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_exists_denom_of_hasCompactSupport.solution
