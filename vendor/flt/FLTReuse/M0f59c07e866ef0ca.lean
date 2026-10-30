import FLTReuse.Ma6dd0c4d713fb96a
import FLTReuse.Mbfe19ea9534a55ec
import FLTReuse.M1868db956c866c8d
import FLTReuse.Mb546e54f85059c34

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.StandardAddChar

theorem NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace
    (K : Type) [Field K] [NumberField K]
    (x : FiniteAdeleRing (𝓞 K) K)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
    (traceFinHom K x) p
      = ∑ w : p.Extension (𝓞 K),
          Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) (x w.1) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.solution
