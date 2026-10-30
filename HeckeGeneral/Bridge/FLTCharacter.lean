import HeckeGeneral.Characters.PrimeCoefficients
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Complex-unit valued characters for the Tate-theory bridge

The conversion keeps the character and the positive-valuation uniformizer unchanged.
Taking the inverse supplies the dual character; it is not needed to identify the
untwisted Euler coefficients. Our negative logarithmic norm convention makes its
twist the complex power of the idelic modulus with parameter `-t`.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField HeckeGeneral.Characters
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

/-- The original character pulled back to ideles and embedded into complex units. -/
def complexIdeleCharacter (χ : HeckeCharacter K) : IdeleGroup (𝓞 K) K →* ℂˣ :=
  Circle.toUnits.comp (toIdeleCharacter K χ).toMonoidHom

@[simp] theorem complexIdeleCharacter_coe (χ : HeckeCharacter K)
    (x : IdeleGroup (𝓞 K) K) :
    (complexIdeleCharacter K χ x : ℂ) = (toIdeleCharacter K χ x : ℂ) := rfl

theorem continuous_complexIdeleCharacter_coe (χ : HeckeCharacter K) :
    Continuous (fun x : IdeleGroup (𝓞 K) K => (complexIdeleCharacter K χ x : ℂ)) :=
  continuous_subtype_val.comp (toIdeleCharacter K χ).continuous

theorem continuous_complexIdeleCharacter (χ : HeckeCharacter K) :
    Continuous (complexIdeleCharacter K χ) := by
  apply Units.continuous_iff.mpr
  refine ⟨continuous_complexIdeleCharacter_coe K χ, ?_⟩
  have h := (continuous_complexIdeleCharacter_coe K χ).comp continuous_inv
  change Continuous (fun x : IdeleGroup (𝓞 K) K =>
    (complexIdeleCharacter K χ x⁻¹ : ℂ)) at h
  simpa only [map_inv] using h

theorem norm_complexIdeleCharacter (χ : HeckeCharacter K)
    (x : IdeleGroup (𝓞 K) K) : ‖(complexIdeleCharacter K χ x : ℂ)‖ = 1 :=
  Circle.norm_coe _

@[simp] theorem complexIdeleCharacter_principal (χ : HeckeCharacter K) (u : Kˣ) :
    complexIdeleCharacter K χ (IdeleGroup.unitEmbedding (𝓞 K) K u) = 1 := by
  apply Units.ext
  change (toIdeleCharacter K χ (IdeleGroup.unitEmbedding (𝓞 K) K u) : ℂ) = 1
  rw [toIdeleCharacter_trivial]
  rfl

@[simp] theorem complexIdeleCharacter_one : complexIdeleCharacter K 1 = 1 := by
  ext x
  rfl

@[simp] theorem complexIdeleCharacter_mul (χ ψ : HeckeCharacter K) :
    complexIdeleCharacter K (χ * ψ) =
      complexIdeleCharacter K χ * complexIdeleCharacter K ψ := by
  ext x
  rfl

@[simp] theorem complexIdeleCharacter_inv (χ : HeckeCharacter K) :
    complexIdeleCharacter K χ⁻¹ = (complexIdeleCharacter K χ)⁻¹ := by
  ext x
  rfl

theorem complexIdeleCharacter_inv_coe (χ : HeckeCharacter K)
    (x : IdeleGroup (𝓞 K) K) :
    (complexIdeleCharacter K χ⁻¹ x : ℂ) = star (complexIdeleCharacter K χ x : ℂ) :=
  Circle.coe_inv_eq_conj _

/-- Exactly the algebraic and topological character data used by global Tate theory. -/
def ComplexUnitaryPrincipalTrivial (ψ : IdeleGroup (𝓞 K) K →* ℂˣ) : Prop :=
  Continuous (fun x => (ψ x : ℂ)) ∧ (∀ x, ‖(ψ x : ℂ)‖ = 1) ∧
    ∀ u : Kˣ, ψ (IdeleGroup.unitEmbedding (𝓞 K) K u) = 1

theorem complexIdeleCharacter_properties (χ : HeckeCharacter K) :
    ComplexUnitaryPrincipalTrivial K (complexIdeleCharacter K χ) :=
  ⟨continuous_complexIdeleCharacter_coe K χ, norm_complexIdeleCharacter K χ,
    complexIdeleCharacter_principal K χ⟩

/-- Recover the circle-valued continuous character without adding a finite-order condition. -/
def circleIdeleCharacter (ψ : IdeleGroup (𝓞 K) K →* ℂˣ)
    (hψ : ComplexUnitaryPrincipalTrivial K ψ) : UnitaryCharacter (IdeleGroup (𝓞 K) K) := by
  let f : IdeleGroup (𝓞 K) K → Circle := fun x =>
    ⟨(ψ x : ℂ), by simpa [Submonoid.unitSphere] using hψ.2.1 x⟩
  refine { toFun := f, map_one' := ?_, map_mul' := ?_, continuous_toFun := ?_ }
  ·
    apply Circle.ext
    change (ψ 1 : ℂ) = 1
    rw [map_one]
    rfl
  · intro x y
    apply Circle.ext
    change (ψ (x * y) : ℂ) = (ψ x : ℂ) * (ψ y : ℂ)
    rw [map_mul]
    rfl
  · exact hψ.1.subtype_mk _

theorem circleIdeleCharacter_trivial (ψ : IdeleGroup (𝓞 K) K →* ℂˣ)
    (hψ : ComplexUnitaryPrincipalTrivial K ψ) :
    TrivialOnPrincipal K (circleIdeleCharacter K ψ hψ) := by
  intro u
  apply Circle.ext
  change (ψ (IdeleGroup.unitEmbedding (𝓞 K) K u) : ℂ) = 1
  rw [hψ.2.2 u]
  rfl

def heckeCharacterOfComplex (ψ : IdeleGroup (𝓞 K) K →* ℂˣ)
    (hψ : ComplexUnitaryPrincipalTrivial K ψ) : HeckeCharacter K :=
  descendIdeleCharacter K (circleIdeleCharacter K ψ hψ)
    (circleIdeleCharacter_trivial K ψ hψ)

@[simp] theorem complexIdeleCharacter_ofComplex (ψ : IdeleGroup (𝓞 K) K →* ℂˣ)
    (hψ : ComplexUnitaryPrincipalTrivial K ψ) :
    complexIdeleCharacter K (heckeCharacterOfComplex K ψ hψ) = ψ := by
  ext x
  rfl

@[simp] theorem heckeCharacterOfComplex_toComplex (χ : HeckeCharacter K) :
    heckeCharacterOfComplex K (complexIdeleCharacter K χ)
      (complexIdeleCharacter_properties K χ) = χ := by
  apply ContinuousMonoidHom.ext
  intro x
  refine QuotientGroup.induction_on x fun y => ?_
  rfl

/-- The bridge covers all continuous unitary idele-class characters in both directions. -/
def heckeCharacterEquivComplex :
    HeckeCharacter K ≃ {ψ : IdeleGroup (𝓞 K) K →* ℂˣ //
      ComplexUnitaryPrincipalTrivial K ψ} where
  toFun χ := ⟨complexIdeleCharacter K χ, complexIdeleCharacter_properties K χ⟩
  invFun ψ := heckeCharacterOfComplex K ψ.1 ψ.2
  left_inv := heckeCharacterOfComplex_toComplex K
  right_inv ψ := Subtype.ext (complexIdeleCharacter_ofComplex K ψ.1 ψ.2)

theorem complexIdeleCharacter_injective : Function.Injective (complexIdeleCharacter K) := by
  intro χ ψ h
  apply (heckeCharacterEquivComplex K).injective
  exact Subtype.ext h

@[simp] theorem complexIdeleCharacter_local (χ : HeckeCharacter K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    (complexIdeleCharacter K χ (localIdeleEmbedding K v u) : ℂ) =
      (localComponent K v χ u : ℂ) := rfl

theorem primeCoefficient_eq_complexIdeleCharacter (χ : HeckeCharacter K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    primeCoefficient K χ v = if UnramifiedAt K χ v then
      (complexIdeleCharacter K χ (localIdeleEmbedding K v (localUniformizerUnit K v)) : ℂ)
      else 0 := rfl

/-- The integral-unit formulation used by Tate theory equals our norm-one formulation. -/
theorem unramifiedAt_iff_complex_integral_units (χ : HeckeCharacter K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    UnramifiedAt K χ v ↔
      ∀ u : (v.adicCompletion K)ˣ, u.val ∈ v.adicCompletionIntegers K →
        (u⁻¹).val ∈ v.adicCompletionIntegers K →
        complexIdeleCharacter K χ (localIdeleEmbedding K v u) = 1 := by
  constructor
  · intro h u hu hi
    apply Units.ext
    rw [complexIdeleCharacter_local, h u
      ((local_norm_one_iff_integral_unit K v u).mpr ⟨hu, hi⟩)]
    rfl
  · intro h u hu
    apply Circle.ext
    have hi := (local_norm_one_iff_integral_unit K v u).mp hu
    have he := congrArg Units.val (h u hi.1 hi.2)
    exact he

/-- The sign is negative because our logarithmic norm is minus the logarithm of the modulus. -/
theorem complexIdeleCharacter_normTwist_coe (t : ℝ) (x : IdeleGroup (𝓞 K) K) :
    (complexIdeleCharacter K (heckeNormTwist K t) x : ℂ) =
      (idelicNorm K x : ℂ) ^ (Complex.I * (-t : ℂ)) := by
  change (Circle.exp (t * (-Real.log (idelicNorm K x))) : ℂ) = _
  rw [Circle.coe_exp, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (idelicNorm_pos K x).ne')]
  rw [← Complex.ofReal_log (idelicNorm_pos K x).le]
  congr 1
  push_cast
  ring

end HeckeGeneral.Bridge
