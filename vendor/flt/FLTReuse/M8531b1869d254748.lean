import FLTReuse.M55164c2a16500130
import FLTReuse.Mb875502fbb65df3e
import FLTReuse.M1868db956c866c8d
import FLTReuse.Me81399e7f86b24e0

open NumberField NumberField.AdelicFourier AutomorphicForm
theorem NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    fourierIntegral ψ μ f ∈ schwartzBruhat F := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat.solution
