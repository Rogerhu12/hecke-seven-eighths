module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.M6136ad15adda1c11

@[expose] public section

open scoped FourierTransform SchwartzMap
theorem SchwartzMap.exists_coe_eq_vectorFourierIntegral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (f : 𝓢(V, ℂ)) :
    ∃ g : 𝓢(V, ℂ), ⇑g = VectorFourier.fourierIntegral 𝐞 μ B f := by p2m_exact_reverting @_root_.P2MW.S_SchwartzMap_exists_coe_eq_vectorFourierIntegral.solution
