module

public import FLTReuse.Mbfe19ea9534a55ec
public import Mathlib.Analysis.Fourier.FourierTransform
public import FLTReuse.Md546eaac50eccd9f
public import FLTReuse.M1868db956c866c8d

@[expose] public section

namespace P2MW.S_NumberField_StandardAddChar_stdAddChar_apply_mk_zero_eq_fourierChar_trace

open NumberField NumberField.StandardAddChar IsDedekindDomain

theorem solution
    (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    stdAddChar F (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) :=
  NumberField.StandardAddChar.AdelicTraceData.psiK_apply_mk_zero_eq_fourierChar_trace F (adelicTraceData F) x
