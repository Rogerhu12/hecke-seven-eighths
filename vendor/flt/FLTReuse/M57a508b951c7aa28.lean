
import FLTReuse.M55164c2a16500130
import FLTReuse.Md2cadaa4525e04a6
import FLTReuse.Mb875502fbb65df3e
import FLTReuse.M1868db956c866c8d
import FLTReuse.Me3c5b58d1cdd8b1c

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors
theorem NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (w : FiniteAdeleRing (𝓞 F) F) :
    (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1)
      ↔ ∃ r : F, r ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)
          ∧ w - algebraMap F (FiniteAdeleRing (𝓞 F) F) r ∈ integralFiniteAdeles (𝓞 F) F := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual.solution
