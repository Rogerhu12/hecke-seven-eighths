import FLTReuse.M1d4e501986eb161a
import FLTReuse.M1868db956c866c8d
import FLTReuse.M17baaab09296e132
attribute [-instance] NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers     IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal   

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_eq_real_image_higherUnitsAt (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (s : ℂ) :
    letI := localBorel K v
    localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ s
      = (((selfDualHaarAt K v).real
            (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a) : ℝ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_real_image_higherUnitsAt.solution
