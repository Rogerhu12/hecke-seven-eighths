import HeckeGeneral.Bridge.FLTDefinitions
import HeckeGeneral.Characters.FiniteRamification

/-!
# Actual dual characters in the Tate bridge

The inverse character has the same ramified places. Its Euler coefficient is
the inverse complex unit at an unramified prime and zero at a ramified prime.
Radial and angular infinity parameters change sign. These statements concern
the actual local characters and products; they assume no analytic continuation
or functional equation.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

/-- Inversion preserves the actual unramified condition in both directions. -/
theorem unramifiedAt_inv_iff (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    UnramifiedAt F χ⁻¹ v ↔ UnramifiedAt F χ v := by
  constructor
  · intro h
    simpa only [inv_inv] using UnramifiedAt.inv F h
  · exact UnramifiedAt.inv F

theorem fltUnramifiedAt_inv_iff (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F)) :
    NumberField.TateGlobal.IsUnramifiedCharAt (complexIdeleCharacter F χ⁻¹) v ↔
      NumberField.TateGlobal.IsUnramifiedCharAt (complexIdeleCharacter F χ) v := by
  rw [fltUnramifiedAt_iff, fltUnramifiedAt_iff, unramifiedAt_inv_iff]

/-- The literal dual prime coefficient in the fixed Tate FE statement. -/
def fltDualPrimeCoefficient (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if NumberField.TateGlobal.IsUnramifiedCharAt (complexIdeleCharacter F χ) v then
    (((complexIdeleCharacter F χ (AutomorphicForm.uniformizerIdele F v))⁻¹ : ℂˣ) : ℂ)
  else 0

theorem fltDualPrimeCoefficient_eq (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F)) :
    fltDualPrimeCoefficient F χ v = fltPrimeCoefficient F χ⁻¹ v := by
  unfold fltDualPrimeCoefficient fltPrimeCoefficient
  rw [fltUnramifiedAt_inv_iff]
  split_ifs <;> simp [complexIdeleCharacter_inv]

/-- The literal inverse-coefficient Euler product in the Tate FE statement. -/
def fltDualEulerProduct (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  ∏' v : HeightOneSpectrum (𝓞 F),
    (1 - fltDualPrimeCoefficient F χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹

/-- This equality concerns all total products, not only the convergence half-plane. -/
theorem fltDualEulerProduct_eq (χ : HeckeCharacter F) (s : ℂ) :
    fltDualEulerProduct F χ s = fltEulerProduct F χ⁻¹ s := by
  unfold fltDualEulerProduct fltEulerProduct
  apply tprod_congr
  intro v
  rw [fltDualPrimeCoefficient_eq]

theorem heckeLSeries_inv_eq_fltDualEulerProduct (χ : HeckeCharacter F)
    {s : ℂ} (hs : 1 < s.re) :
    HeckeGeneral.Analysis.heckeLSeries F χ⁻¹ s = fltDualEulerProduct F χ s := by
  rw [fltDualEulerProduct_eq]
  exact heckeLSeries_eq_fltEulerProduct F χ⁻¹ hs

theorem heckeNormTwist_neg (t : ℝ) :
    heckeNormTwist F (-t) = (heckeNormTwist F t)⁻¹ :=
  normTwist_neg (heckeLogNorm F) t

/-- The non-norm branch is closed under duality. -/
theorem nonNorm_inv (χ : HeckeCharacter F)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist F t) :
    ∀ t : ℝ, χ⁻¹ ≠ heckeNormTwist F t := by
  intro t ht
  apply hχ (-t)
  have h := congrArg (fun ψ : HeckeCharacter F => ψ⁻¹) ht
  simpa only [inv_inv, ← heckeNormTwist_neg F t] using h

/-- The radial predicate occurring literally in the Tate existence theorems. -/
def FLTArchRadialCondition (χ : HeckeCharacter F) (τ : InfinitePlace F → ℝ) : Prop :=
  ∀ (v : InfinitePlace F) (x : v.Completionˣ),
    0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
    (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
    ((NumberField.TateGlobal.archLocalChar (complexIdeleCharacter F χ) v x : ℂˣ) : ℂ) =
      ((NumberField.TateGlobal.ideleNorm F (NumberField.TateGlobal.archUnitHom v x) : ℝ) : ℂ) ^
        ((τ v : ℂ) * Complex.I)

/-- The angular predicate occurring literally in the Tate existence theorems. -/
def FLTArchAngularCondition (χ : HeckeCharacter F) (m : InfinitePlace F → ℤ) : Prop :=
  ∀ (v : InfinitePlace F) (x : v.Completionˣ),
    ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
    ((NumberField.TateGlobal.archLocalChar (complexIdeleCharacter F χ) v x : ℂˣ) : ℂ) =
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)

theorem fltArchLocalChar_inv (χ : HeckeCharacter F)
    (v : InfinitePlace F) (x : v.Completionˣ) :
    ((NumberField.TateGlobal.archLocalChar (complexIdeleCharacter F χ⁻¹) v x : ℂˣ) : ℂ) =
      (((NumberField.TateGlobal.archLocalChar (complexIdeleCharacter F χ) v x : ℂˣ) : ℂ))⁻¹ := by
  simp [NumberField.TateGlobal.archLocalChar, complexIdeleCharacter_inv]

/-- The paired radial parameter is the actual pointwise negative. -/
theorem FLTArchRadialCondition.inv {χ : HeckeCharacter F} {τ : InfinitePlace F → ℝ}
    (hτ : FLTArchRadialCondition F χ τ) :
    FLTArchRadialCondition F χ⁻¹ (-τ) := by
  intro v x hre him
  rw [fltArchLocalChar_inv, hτ v x hre him]
  simp only [Pi.neg_apply, Complex.ofReal_neg, neg_mul, Complex.cpow_neg]

/-- The paired angular parameter is the actual pointwise negative. -/
theorem FLTArchAngularCondition.inv {χ : HeckeCharacter F} {m : InfinitePlace F → ℤ}
    (hm : FLTArchAngularCondition F χ m) :
    FLTArchAngularCondition F χ⁻¹ (-m) := by
  intro v x hx
  rw [fltArchLocalChar_inv, hm v x hx]
  simp only [Pi.neg_apply, zpow_neg]

end HeckeGeneral.Bridge
