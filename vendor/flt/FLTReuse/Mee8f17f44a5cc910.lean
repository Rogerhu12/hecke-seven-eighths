import FLTReuse.Ma6dd0c4d713fb96a
import FLTReuse.M1d4e501986eb161a
import FLTReuse.M1868db956c866c8d
import FLTReuse.M6dcd247431824626

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : v.Extension (𝓞 L))
    (x : w.1.adicCompletion L) :
    psiLocal L w.1 x
      = psiLocal K v (Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace.solution
