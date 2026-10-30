import Mathlib
import FLTReuse.M55164c2a16500130
import FLTReuse.Md2cadaa4525e04a6
import FLTReuse.Mb875502fbb65df3e
import FLTReuse.M1868db956c866c8d
import FLTReuse.M7a9fd322ab91e73b

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors
theorem NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    fourierIntegral ψ μ f ∈ schwartzBruhat F := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace.solution
