module

public import FLTReuse.M55164c2a16500130
public import FLTReuse.Md2cadaa4525e04a6
public import FLTReuse.Mb875502fbb65df3e
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.M92ded25f906eeb97

@[expose] public section

open NumberField NumberField.AdelicFourier AutomorphicForm
theorem NumberField.AdelicFourier.tsum_eq_inv_measure_mul_tsum_fourierIntegral (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ * ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral.solution
