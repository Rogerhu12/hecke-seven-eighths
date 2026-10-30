import FLTReuse.Md2cadaa4525e04a6
import FLTReuse.M55164c2a16500130
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import FLTReuse.M1868db956c866c8d
import FLTReuse.Mf1523d07e287ea2a
-- The removed upstream instance instCountableOfNumberField_definitions is absent in this Mathlib.

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier
  IsDedekindDomain

open scoped Classical in

theorem EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    (w : AdeleRing (𝓞 F) F) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹ *
        fourierIntegral ψ μ (fun x ↦ f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2) w
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
        * (fourierIntegral
              (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
                (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
              MeasureTheory.volume f (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
          * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)⁻¹
              * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν g w.2)) := by p2m_exact_reverting @_root_.P2MW.S_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq.solution
