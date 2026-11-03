import HeckeAxiom.SignalAdapter
import HeckeGeneral.Characters.InfinityType

/-!
# The infinity type of the correction character `Λ`

At each complex place the correction records `Λ` as the inverse of the
angular character `z / |z|` or of its conjugate, according to whether the
place restricts to the orientation embedding of the cubic subfield. In the
skeleton's standard complex coordinate this means: the angular weight of `Λ`
is `-1` or `1`, and its radial parameter is `0`.

The coordinates agree: the skeleton's complex coordinate of a complex place is
Mathlib's `ringEquivComplexOfIsComplex`, which is `extensionEmbedding`, the map
in which the correction states its infinite component.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain ComplexConjugate
open DedekindZetaZeroFree DedekindZetaZeroFree.SArithmeticData
open HeckeGeneral.Characters

variable {F : Type} [Field F] [NumberField F]

namespace ArithmeticChoice

variable {S₀ : Finset (HeightOneSpectrum (𝓞 F))} {root12 : F} {σ : F →+* ℂ}
variable (X : ArithmeticChoice F S₀ root12 σ)

/-- The orientation embedding of the cubic subfield in the correction. -/
abbrev cubicEmbedding : DHCubic.E0 F X.A →+* ℂ := σ.comp (algebraMap (DHCubic.E0 F X.A) F)

/-- The complex component of `Λ` in the standard coordinate. -/
theorem complexHeckeComponent_Lambda (v : InfinitePlace F) (hv : v.IsComplex) (z : ℂˣ) :
    ((complexHeckeComponent F v hv X.Lambda z : Circle) : ℂ) =
      (DHCubic.infinityComponent (DHCubic.E0 F X.A) F X.cubicEmbedding v (z : ℂ))⁻¹ := by
  have h := X.C.correction.Λ_infinity v (complexUnitsToCompletion hv z)
  have hz : InfinitePlace.Completion.extensionEmbedding v
      ((complexUnitsToCompletion hv z : v.Completionˣ) : v.Completion) = (z : ℂ) := by
    change InfinitePlace.Completion.extensionEmbedding v
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm (z : ℂ)) = (z : ℂ)
    rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hv, RingEquiv.apply_symm_apply]
  rw [hz] at h
  exact h

private theorem angular_circle (c : Circle) : DHCubic.angular (c : ℂ) = c := by
  simp [DHCubic.angular]

private theorem angular_exp (x : ℝ) : DHCubic.angular ((Real.exp x : ℝ) : ℂ) = 1 := by
  have hpos := Real.exp_pos x
  rw [DHCubic.angular, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  exact div_self (Complex.ofReal_ne_zero.mpr hpos.ne')

/-- The angular weight of `Λ` at every complex place is `1` or `-1`. -/
theorem Lambda_weight (v : InfinitePlace F) (hv : v.IsComplex) :
    heckeComplexWeight F v hv X.Lambda = 1 ∨ heckeComplexWeight F v hv X.Lambda = -1 := by
  by_cases ho : v.embedding.comp (algebraMap (DHCubic.E0 F X.A) F) = X.cubicEmbedding
  · right
    refine (circleWeight_eq_iff _ _).mpr fun c => Circle.ext ?_
    have h := X.complexHeckeComponent_Lambda v hv (complexCircleEmbedding c)
    rw [complexCircleEmbedding_val, DHCubic.infinityComponent, ite_eq_left ho, angular_circle] at h
    simpa using h
  · left
    refine (circleWeight_eq_iff _ _).mpr fun c => Circle.ext ?_
    have h := X.complexHeckeComponent_Lambda v hv (complexCircleEmbedding c)
    rw [complexCircleEmbedding_val, DHCubic.infinityComponent, ite_eq_right ho, angular_circle] at h
    have hc : (conj (c : ℂ))⁻¹ = (c : ℂ) := by
      rw [← Circle.coe_inv_eq_conj, ← Circle.coe_inv, inv_inv]
    simpa [hc] using h

/-- The radial parameter of `Λ` at every complex place is `0`. -/
theorem Lambda_parameter (v : InfinitePlace F) (hv : v.IsComplex) :
    heckeComplexParameter F v hv X.Lambda = 0 := by
  have hfreq : complexFrequency (complexHeckeComponent F v hv X.Lambda) = 0 := by
    refine (realFrequency_eq_iff _ _).mpr fun x => Circle.ext ?_
    have h := X.complexHeckeComponent_Lambda v hv (complexRadialExponential (Multiplicative.ofAdd x))
    have hval : ((complexRadialExponential (Multiplicative.ofAdd x) : ℂˣ) : ℂ) =
        ((Real.exp x : ℝ) : ℂ) := rfl
    rw [hval, DHCubic.infinityComponent, angular_exp] at h
    have h1 : ((complexHeckeComponent F v hv X.Lambda
        (complexRadialExponential (Multiplicative.ofAdd x)) : Circle) : ℂ) = 1 := by
      rw [h]
      split_ifs <;> simp
    simpa using h1
  simp [heckeComplexParameter, hfreq]

end ArithmeticChoice

end HeckeAxiom
