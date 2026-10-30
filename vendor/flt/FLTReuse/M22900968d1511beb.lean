import FLTReuse.M1d4e501986eb161a
import FLTReuse.M1868db956c866c8d
import FLTReuse.M432f472acf4e7e20
attribute [-instance] NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers     IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal   

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.StandardAddChar

theorem LanglandsTunnell.TateLocal.selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    letI := localBorel K v
    (selfDualHaarAt K v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K))
        * (selfDualHaarAt K v).real
            {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal K v))} = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel.solution
