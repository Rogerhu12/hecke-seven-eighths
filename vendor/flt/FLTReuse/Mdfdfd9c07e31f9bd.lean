module

public import FLTReuse.M1d4e501986eb161a
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.M2d8ef25f4322f358

@[expose] public section

set_option autoImplicit false

theorem LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers (K : Type) [Field K]
    [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : v.adicCompletion K) (hx : x ∈ v.adicCompletionIntegers K) :
    NumberField.StandardAddChar.psiLocal K v x = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers.solution
