module

public import ThetaGlobal.FiniteNormalizedMellin
public import HeckeGeneral.Characters.InfinityPacket

/-!
# Character orientation of the actual local Mellin pair

The fixed-source direct profile multiplies its Whittaker value by the
positive character `θ`; its reflected profile uses `θ⁻¹`.  Their Gamma
products are consequently `archGammaProduct θ⁻¹` and `archGammaProduct θ`,
respectively.  These identities record that orientation using the actual
Hecke parameters.  They introduce no local Mellin or global reflection
hypothesis, and do not change either profile or the stored multiplier.

In particular, a local convention whose direct profile uses an inverse
character must be applied at `θ⁻¹` when it is connected to this source.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.LocalGammaOrientation

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open scoped NumberField Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

theorem archShift_inv (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    archShift K θ⁻¹ v = archShift K θ v := by
  simp only [archShift, heckeComplexWeight_inv, abs_neg]

theorem archRadial_inv (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    archRadial K θ⁻¹ v = -archRadial K θ v := by
  simp only [archRadial, heckeComplexParameter_inv, neg_neg]

/-- The direct Gamma product uses the inverse character's parameters. -/
theorem directGammaProduct_eq_archGammaProduct_inv
    (θ : HeckeCharacter K) (s : ℂ) :
    FiniteNormalizedMellin.directGammaProduct θ s = archGammaProduct K θ⁻¹ s := by
  simp only [FiniteNormalizedMellin.directGammaProduct, archGammaProduct,
    archShift_inv, archRadial_inv, Complex.ofReal_neg, mul_neg, sub_eq_add_neg]

section LocalPairs

variable {S : SArithmeticData K} {η : RayClassCharacter K S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

/-- Inverting the character exchanges the two stored one-place Gamma pairs. -/
theorem gammaPair_inv_eq_directGammaPair (θ : HeckeCharacter K)
    (w : InfinitePlace K) (s : ℂ) :
    FiniteLocalHighK.gammaPair R θ⁻¹ w s =
      FiniteLocalHighK.directGammaPair R θ w s := by
  simp only [FiniteLocalHighK.gammaPair, FiniteLocalHighK.directGammaPair,
    archShift_inv, archRadial_inv, Complex.ofReal_neg, mul_neg, sub_eq_add_neg]

theorem directGammaPair_inv_eq_gammaPair (θ : HeckeCharacter K)
    (w : InfinitePlace K) (s : ℂ) :
    FiniteLocalHighK.directGammaPair R θ⁻¹ w s =
      FiniteLocalHighK.gammaPair R θ w s := by
  simpa only [inv_inv] using (gammaPair_inv_eq_directGammaPair R θ⁻¹ w s).symm

/-- The finite product of the actual direct local pairs has this same orientation. -/
theorem directGammaPair_product_eq_archGammaProduct_inv
    (θ : HeckeCharacter K) (s : ℂ) :
    (∏ w : InfinitePlace K, FiniteLocalHighK.directGammaPair R θ w s) =
      archGammaProduct K θ⁻¹ s := by
  rw [FiniteNormalizedMellin.directGammaPair_product,
    directGammaProduct_eq_archGammaProduct_inv]

end LocalPairs

/-- The original multiplier is the reflected/direct Gamma quotient in the
fixed source's positive-character convention.  This is an algebraic identity
for every complex `s`, so no Mellin-strip hypothesis is needed here. -/
theorem reflectionMultiplier_eq_gamma_quotient
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) [Fintype S]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (s : ℂ) :
    reflectionMultiplier K S F θ u κ s =
      F.C₀⁻¹ * (F.A₀ : ℂ) ^ (2 * s) * finiteMellinFactor K S F u κ s *
        (archGammaProduct K θ s / archGammaProduct K θ⁻¹ (-s)) := by
  rw [← directGammaProduct_eq_archGammaProduct_inv θ (-s)]
  unfold reflectionMultiplier archGammaProduct FiniteNormalizedMellin.directGammaProduct
  rw [← Finset.prod_div_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  simp only [sub_eq_add_neg]
  exact (mul_div_mul_comm _ _ _ _).symm

end ThetaGlobal.LocalGammaOrientation
