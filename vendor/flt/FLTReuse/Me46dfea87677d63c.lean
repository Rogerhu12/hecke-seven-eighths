import FLTReuse.Mb34f70d821d13751
import FLTReuse.M1868db956c866c8d
import FLTReuse.M36478ea94b3f2c22

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse

theorem LanglandsTunnell.CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 K) K μ)
    (w : InfinitePlace K) (u : ℂ) (a : ℤ) (h : IsArchCompAt K μ w u a) :
    u.re = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_re_eq_zero_of_isArchCompAt_of_isUnitaryChar.solution
