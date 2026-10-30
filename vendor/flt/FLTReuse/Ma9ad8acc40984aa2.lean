import FLTReuse.M1d4e501986eb161a
import FLTReuse.M1868db956c866c8d
import FLTReuse.Ma727aa4a1d9866a7

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.StandardAddChar
open scoped nonZeroDivisors

theorem LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    addCharLevel (psiLocal K v)
      = FractionalIdeal.count K v (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal.solution
