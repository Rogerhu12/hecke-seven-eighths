module

public import FLTReuse.M55164c2a16500130
public import FLTReuse.Md2cadaa4525e04a6
public import FLTReuse.Mb875502fbb65df3e
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.M2f8449dfe5e9c43f

@[expose] public section

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors
theorem NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (q : F) :
    ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q)
      = (Real.fourierChar (-((Algebra.trace ℚ F q : ℚ) : ℝ)) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace.solution
