import FLTReuse.M55164c2a16500130
import FLTReuse.Md2cadaa4525e04a6
import FLTReuse.Mb875502fbb65df3e
import FLTReuse.M791e48edf6c15dd6
import FLTReuse.Md9bb0dc096ff8cbe
import FLTReuse.M8531b1869d254748
import FLTReuse.M1868db956c866c8d
namespace P2MW.S_NumberField_AdelicFourier_tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
        - ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ * ∫ v, f v ∂μ
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
          ∑' ξ : {ξ : F // ξ ≠ 0}, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  have hsum : Summable fun ξ : F ↦ fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
    have := summable_translate_of_mem_schwartzBruhat F
      (fourierIntegral_mem_schwartzBruhat F μ hψ hf) 0
    simpa only [zero_add] using this
  have key : ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) 0)
        + ∑' ξ : {ξ : F // ξ ≠ 0}, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
    rw [← hsum.sum_add_tsum_subtype_compl {0}, Finset.sum_singleton]
    congr 1
    exact tsum_congr_subtype
      (fun ξ : F ↦ fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ)) fun x ↦ by simp
  have h0 : fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) 0) = ∫ v, f v ∂μ := by
    simp [fourierIntegral_def]
  rw [tsum_eq_inv_measure_mul_tsum_fourierIntegral F μ hψ hf, key, h0]
  ring
