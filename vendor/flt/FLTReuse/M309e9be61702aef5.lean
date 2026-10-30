import FLTReuse.Mcab7f5d3272e0825
import FLTReuse.Md2cadaa4525e04a6
import FLTReuse.M436eaa679b5c9606
import Mathlib.Analysis.Fourier.FourierTransform
import FLTReuse.M1868db956c866c8d
namespace P2MW.S_NumberField_StandardAddChar_AdelicTraceData_psiK_apply_mk_zero_eq_fourierChar_trace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open NumberField NumberField.StandardAddChar IsDedekindDomain

theorem solution
    (F : Type) [Field F] [NumberField F] (T : AdelicTraceData F) (x : InfiniteAdeleRing F) :
    T.psiK (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by

  set f : InfiniteAdeleRing F → ℂ := fun x => T.psiK (x, 0) with hf
  set g : InfiniteAdeleRing F → ℂ := fun x => (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) with hg
  suffices hfg : f = g from congrFun hfg x
  have hfc : Continuous f :=
    T.continuous_psiK.comp (continuous_id.prodMk continuous_const :
      Continuous (fun x : InfiniteAdeleRing F => ((x, 0) : AdeleRing (𝓞 F) F)))
  have htr : Continuous (fun x : InfiniteAdeleRing F => Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) :=
    (LinearMap.continuous_of_finiteDimensional _).comp
      (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F)
  have hgc : Continuous g := by
    have hg' : g = fun x => Complex.exp (((2 * Real.pi * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) * Complex.I) :=
      funext fun x => Real.fourierChar_apply _
    rw [hg']
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul htr)).mul
      continuous_const)
  refine Continuous.ext_on (InfiniteAdeleRing.denseRange_algebraMap F) hfc hgc ?_
  rintro _ ⟨q, rfl⟩
  simp only [hf, hg]

  rw [AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply, psiQ_apply]
  rw [show ((algebraMap F (InfiniteAdeleRing F) q, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F).1
      = algebraMap F (InfiniteAdeleRing F) q from rfl,
    show ((algebraMap F (InfiniteAdeleRing F) q, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F).2
      = 0 from rfl, map_zero, AddChar.map_zero_eq_one, mul_one, T.traceInf_algebraMap, psiArch_algebraMap]

  rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, NumberField.mixedEmbedding.trace_mixedEmbedding,
    Real.fourierChar_apply]
  push_cast
  ring_nf
