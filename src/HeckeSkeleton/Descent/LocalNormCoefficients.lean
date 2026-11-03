import HeckeSkeleton.Descent.LocalNorm
import HeckeGeneral.Characters.PrimeCoefficients

/-!
Adapted from the 2026-10-11 local-norm cache for the actual Descent interface.

The actual completed norm preserves integral local units and multiplies
the normalized local order by the actual prime inertia degree. Therefore
a downstairs unramified character pulls back to an unramified upstairs
character, whose actual prime coefficient is the corresponding inertia-
degree power of the downstairs coefficient. The extension itself may be
ramified; no extension-unramified assumption occurs anywhere below.

This is a prime-coefficient calibration, NOT an Euler-product factorization.
In particular no equality for deleted/full continuations is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Descent.LocalNorm

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped NumberField
open HeckeGeneral.Characters.NormPullbackDraft

section SingleField

variable (F : Type*) [Field F] [NumberField F]

/-- The upstream order and the project's actual uniformizer have matching sign. -/
@[simp] theorem upstreamLocalOrder_localUniformizerUnit (v : HeightOneSpectrum (𝓞 F)) :
    (_root_.FiniteIdeleGroup.localOrder v (localUniformizerUnit F v)).toAdd = 1 := by
  rw [_root_.FiniteIdeleGroup.localOrder_apply]
  change -WithZero.log (Valued.v (localUniformizer F v)) = 1
  rw [localUniformizer_valuation, WithZero.log_exp]
  rfl

/-- An unramified local component depends only on the actual discrete order. -/
theorem localComponent_eq_of_upstreamLocalOrder (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F)) (hχ : UnramifiedAt F χ v)
    (u z : (v.adicCompletion F)ˣ)
    (horder : (_root_.FiniteIdeleGroup.localOrder v u).toAdd =
      (_root_.FiniteIdeleGroup.localOrder v z).toAdd) :
    localComponent F v χ u = localComponent F v χ z := by
  have hzero : (_root_.FiniteIdeleGroup.localOrder v (u * z⁻¹)).toAdd = 0 := by
    rw [map_mul, map_inv]
    change (_root_.FiniteIdeleGroup.localOrder v u).toAdd +
      -(_root_.FiniteIdeleGroup.localOrder v z).toAdd = 0
    rw [horder, add_neg_cancel]
  have hunit : u * z⁻¹ ∈ (v.adicCompletionIntegers F).units :=
    (_root_.FiniteIdeleGroup.localOrder_eq_zero_iff v _).mp hzero
  have hval := hχ (u * z⁻¹) ((local_norm_one_iff_integral_unit F v _).mpr hunit)
  rw [map_mul, map_inv] at hval
  exact mul_inv_eq_one.mp hval

end SingleField

section Relative

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
variable [Algebra F K] [FiniteDimensional F K]

/-- Integral upstairs units are carried to integral downstairs units by the genuine norm. -/
theorem actualLocalNorm_mem_integerUnits (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v})
    (y : (W.1.adicCompletion K)ˣ) (hy : y ∈ (W.1.adicCompletionIntegers K).units) :
    actualLocalNorm F K v W y ∈ (v.adicCompletionIntegers F).units := by
  letI : Algebra (v.adicCompletion F) (W.1.adicCompletion K) :=
    (_root_.finitePlaceAdicCompletionMap F K v W).toAlgebra
  exact _root_.IdeleGroup.finitePlace_normUnits_mem_integerUnits F K v W ⟨y, hy⟩

/-- The actual norm order formula includes ramified extensions. -/
theorem actualLocalNorm_localOrder (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v})
    (y : (W.1.adicCompletion K)ˣ) :
    (_root_.FiniteIdeleGroup.localOrder v (actualLocalNorm F K v W y)).toAdd =
      (W.1.asIdeal.inertiaDeg (𝓞 F) : ℤ) *
        (_root_.FiniteIdeleGroup.localOrder W.1 y).toAdd := by
  letI : Algebra (v.adicCompletion F) (W.1.adicCompletion K) :=
    (_root_.finitePlaceAdicCompletionMap F K v W).toAlgebra
  exact _root_.FiniteIdeleGroup.localOrder_normUnits F K v W y

/-- A downstairs unramified character stays unramified upstairs, even above
an extension-ramified prime. This is a proved consequence of the actual norm. -/
theorem unramifiedAt_heckeNormPullback (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v})
    (hχ : UnramifiedAt F χ v) : UnramifiedAt K (heckeNormPullback F K χ) W.1 := by
  intro y hy
  rw [localComponent_heckeNormPullback_apply]
  apply hχ
  apply (local_norm_one_iff_integral_unit F v _).mpr
  exact actualLocalNorm_mem_integerUnits F K v W y
    ((local_norm_one_iff_integral_unit K W.1 y).mp hy)

/-- The literal uniformizer value is raised to the actual inertia degree. -/
theorem localComponent_heckeNormPullback_uniformizer (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v})
    (hχ : UnramifiedAt F χ v) :
    localComponent K W.1 (heckeNormPullback F K χ) (localUniformizerUnit K W.1) =
      localComponent F v χ (localUniformizerUnit F v) ^ W.1.asIdeal.inertiaDeg (𝓞 F) := by
  rw [localComponent_heckeNormPullback_apply, ← map_pow]
  apply localComponent_eq_of_upstreamLocalOrder F χ v hχ
  rw [actualLocalNorm_localOrder, upstreamLocalOrder_localUniformizerUnit]
  simp only [map_pow, toAdd_pow, upstreamLocalOrder_localUniformizerUnit,
    nsmul_eq_mul, mul_one]

/-- Actual Euler coefficients, including their genuine unramified tests.
Only chi is assumed unramified below; the field extension need not be. -/
theorem primeCoefficient_heckeNormPullback (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F))
    (W : {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v})
    (hχ : UnramifiedAt F χ v) :
    primeCoefficient K (heckeNormPullback F K χ) W.1 =
      primeCoefficient F χ v ^ W.1.asIdeal.inertiaDeg (𝓞 F) := by
  rw [primeCoefficient_of_unramified K _ W.1 (unramifiedAt_heckeNormPullback F K χ v W hχ),
    primeCoefficient_of_unramified F χ v hχ,
    localComponent_heckeNormPullback_uniformizer F K χ v W hχ, Circle.coe_pow]

end Relative
end HeckeSkeleton.Descent.LocalNorm
