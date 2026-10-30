import FLTReuse.Md2cadaa4525e04a6
import FLTReuse.M1868db956c866c8d
import FLTReuse.M1eebb5a7f18d0122

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors
theorem NumberField.AdelicBox.isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F] (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    IsLocallyConstant (((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
        (1 : FiniteAdeleRing (𝓞 F) F → ℂ))
      ∧ HasCompactSupport (((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
        (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles.solution
