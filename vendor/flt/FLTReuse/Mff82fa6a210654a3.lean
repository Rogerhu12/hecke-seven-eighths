import FLTReuse.M157b087506702f5d
import FLTReuse.M3c68c1555d4fc687
import FLTReuse.M1868db956c866c8d
import FLTReuse.Md6adbc1b97b373ce

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal LanglandsTunnell.TateLocal

theorem LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt
    (K : Type) [Field K]
    [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (h : IsUnramifiedCharAt μ v) : HasConductorExponentAt K v (localChar μ v) 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt.solution
