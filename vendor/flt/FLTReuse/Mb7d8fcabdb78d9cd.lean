import FLTReuse.M1d4e501986eb161a
import FLTReuse.M1868db956c866c8d
import FLTReuse.M21078e945a9009ec
attribute [-instance] NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers     IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal   

set_option autoImplicit false

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain

theorem LanglandsTunnell.TateLocal.stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : HasConductorExponentAt K v χ 0)
    (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) (hlev : addCharLevel (psiLocal K v) = 0)
    (hψ : psiLocal K v ≠ 1) :
    stdRootNumberAt K v χ = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero.solution
