import FLTReuse.M1d4e501986eb161a
import FLTReuse.M1868db956c866c8d
import FLTReuse.M0da9a4a2a3715e8f
attribute [-instance] NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers     IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal   

set_option autoImplicit false

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain

theorem LanglandsTunnell.TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ ω : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) (hχ : HasConductorExponentAt K v χ c)
    (hω : HasConductorExponentAt K v ω 0) (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1)
    (huω : ‖(ω (uniformizerUnit K v) : ℂ)‖ = 1) (hψ : psiLocal K v ≠ 1) :
    stdRootNumberAt K v (χ * ω)
      = (ω (uniformizerUnit K v) : ℂ) ^ ((c : ℤ) + addCharLevel (psiLocal K v))
          * stdRootNumberAt K v χ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero.solution
