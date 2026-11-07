module

public import FLTReuse.Mbfe19ea9534a55ec
public import Mathlib.Analysis.Fourier.FourierTransform
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.M66717b69324139ac

@[expose] public section

open NumberField NumberField.StandardAddChar IsDedekindDomain
theorem NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace
    (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    stdAddChar F (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_StandardAddChar_stdAddChar_apply_mk_zero_eq_fourierChar_trace.solution
