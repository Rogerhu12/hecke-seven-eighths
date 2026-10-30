import FLTReuse.M1d4e501986eb161a
import FLTReuse.M1868db956c866c8d
import FLTReuse.M2ba01902ed132663
attribute [-instance] NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers     IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal   

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.StandardAddChar

theorem LanglandsTunnell.TateLocal.selfDualHaarAt_real_image_higherUnitsAt (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (a : ℕ) (ha : 1 ≤ a) :
    letI := localBorel K v
    (selfDualHaarAt K v).real (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a)
      = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(a : ℤ))
          * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_selfDualHaarAt_real_image_higherUnitsAt.solution
