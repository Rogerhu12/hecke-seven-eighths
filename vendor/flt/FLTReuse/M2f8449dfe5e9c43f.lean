module

public import FLTReuse.M55164c2a16500130
public import FLTReuse.Md2cadaa4525e04a6
public import FLTReuse.Mb875502fbb65df3e
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import FLTReuse.M436eaa679b5c9606
public import FLTReuse.M1868db956c866c8d

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace P2MW.S_NumberField_AdelicFourier_addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

noncomputable section

theorem solution
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (q : F) :
    ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q)
      = (Real.fourierChar (-((Algebra.trace ℚ F q : ℚ) : ℝ)) : ℂ) := by

  have hιq : algebraMap F (AdeleRing (𝓞 F) F) q
      = (algebraMap F (InfiniteAdeleRing F) q, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) := rfl

  have hsplit : ψ (algebraMap F (AdeleRing (𝓞 F) F) q)
      = ψ (algebraMap F (InfiniteAdeleRing F) q, 0)
        * ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) := by
    rw [hιq, ← AddChar.map_add_eq_mul]
    congr 1
    exact Prod.ext (add_zero _).symm (zero_add _).symm

  have hPI : ψ (algebraMap F (AdeleRing (𝓞 F) F) q) = 1 := hψ.principalInvariant q

  have harch : ψ (algebraMap F (InfiniteAdeleRing F) q, 0)
      = (Real.fourierChar ((Algebra.trace ℚ F q : ℚ) : ℝ) : ℂ) := by
    rw [hψ_inf, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
      NumberField.mixedEmbedding.trace_mixedEmbedding]
  rw [hPI, harch] at hsplit

  have hne : (Real.fourierChar ((Algebra.trace ℚ F q : ℚ) : ℝ) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have hx : ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q)
      = (Real.fourierChar ((Algebra.trace ℚ F q : ℚ) : ℝ) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hsplit.symm
  rw [hx, ← Circle.coe_inv, ← AddChar.map_neg_eq_inv]
