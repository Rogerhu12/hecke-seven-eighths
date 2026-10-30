import FLTReuse.M55164c2a16500130
import FLTReuse.Mc4dd375116d61c53
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import FLTReuse.M1868db956c866c8d
import FLTReuse.M06b1cdb6f87adf15
-- The removed upstream instance instCountableOfNumberField_definitions is absent in this Mathlib.

open NumberField NumberField.AdelicFourier
theorem NumberField.AdelicFourier.fourierIntegral_comp_mul_left (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : AdeleRing (𝓞 F) F → ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) (w : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ (fun v => f (a * v)) w
      = ((MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ) : ℂ)⁻¹ * fourierIntegral ψ μ f (↑a⁻¹ * w) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.solution
