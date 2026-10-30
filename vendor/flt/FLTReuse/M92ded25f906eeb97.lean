import FLTReuse.M55164c2a16500130
import FLTReuse.Md2cadaa4525e04a6
import FLTReuse.Mb875502fbb65df3e
import FLTReuse.M8dfb4dc6e898564b
import FLTReuse.M1868db956c866c8d
namespace P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
          ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by

  have h := NumberField.AdelicFourier.tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral
    F μ hψ hf 0
  simpa only [zero_add, mul_zero, AddChar.map_zero_eq_one, mul_one] using h
