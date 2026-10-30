import FLTReuse.M1d4e501986eb161a
import FLTReuse.M1868db956c866c8d
import FLTReuse.Mbc9d4338a4e2d269
attribute [-instance] NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers     IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal   

set_option autoImplicit false

open NumberField NumberField.StandardAddChar IsDedekindDomain

theorem LanglandsTunnell.TateLocal.selfDualHaarAt_real_units_eq
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K)) :
    (selfDualHaarAt K v).real {x | Valued.v x = 1}
      = (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
          * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_selfDualHaarAt_real_units_eq.solution
