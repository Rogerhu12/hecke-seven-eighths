import FLTReuse.M1d4e501986eb161a
import FLTReuse.M1868db956c866c8d
import FLTReuse.Mc01727b1b0b9bfc1
attribute [-instance] NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers     IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal   

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

theorem LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_ne_zero_of_unramified
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) (hχ : HasConductorExponentAt K v χ 0)
    (hs : ‖(χ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ s ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_ne_zero_of_unramified.solution
