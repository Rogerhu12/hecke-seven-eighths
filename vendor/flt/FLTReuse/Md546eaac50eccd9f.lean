import FLTReuse.Mcab7f5d3272e0825
import Mathlib.Analysis.Fourier.FourierTransform
import FLTReuse.M1868db956c866c8d
import FLTReuse.M309e9be61702aef5

open NumberField NumberField.StandardAddChar IsDedekindDomain
theorem NumberField.StandardAddChar.AdelicTraceData.psiK_apply_mk_zero_eq_fourierChar_trace
    (F : Type) [Field F] [NumberField F] (T : AdelicTraceData F) (x : InfiniteAdeleRing F) :
    T.psiK (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_StandardAddChar_AdelicTraceData_psiK_apply_mk_zero_eq_fourierChar_trace.solution
