import HeckeGeneral.Characters.LocalComponent

/-!
# Unramified local components of actual Hecke characters

Triviality is imposed on the actual local unit subgroup, equivalently on
elements of local norm one. This file does not assume or prove that the
ramified set is finite. Uniformizer independence follows from this definition.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (K : Type*) [Field K] [NumberField K]

/-- The usual unramified condition on the actual continuous local component. -/
def UnramifiedAt (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ u : (v.adicCompletion K)ˣ, ‖u.val‖ = 1 → localComponent K v χ u = 1

theorem local_norm_one_iff_integral_unit (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ‖u.val‖ = 1 ↔ u ∈ (v.adicCompletionIntegers K).units := by
  rw [Valued.toNormedField.norm_eq_one_iff (L := v.adicCompletion K)
    (Γ₀ := WithZero (Multiplicative ℤ)), adicCompletionIntegers.mem_units_iff_valued_eq_one]

theorem unramifiedAt_iff_integral_units (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) :
    UnramifiedAt K χ v ↔
      ∀ u : (v.adicCompletion K)ˣ, u ∈ (v.adicCompletionIntegers K).units →
        localComponent K v χ u = 1 := by
  simp only [UnramifiedAt, local_norm_one_iff_integral_unit]

theorem unramifiedAt_one (v : HeightOneSpectrum (𝓞 K)) :
    UnramifiedAt K 1 v := by
  intro u _
  rfl

theorem UnramifiedAt.mul {χ ψ : HeckeCharacter K} {v : HeightOneSpectrum (𝓞 K)}
    (hχ : UnramifiedAt K χ v) (hψ : UnramifiedAt K ψ v) :
    UnramifiedAt K (χ * ψ) v := by
  intro u hu
  change localComponent K v χ u * localComponent K v ψ u = 1
  rw [hχ u hu, hψ u hu, mul_one]

theorem UnramifiedAt.inv {χ : HeckeCharacter K} {v : HeightOneSpectrum (𝓞 K)}
    (hχ : UnramifiedAt K χ v) : UnramifiedAt K χ⁻¹ v := by
  intro u hu
  change (localComponent K v χ u)⁻¹ = 1
  rw [hχ u hu, inv_one]

theorem unramifiedAt_normTwist (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    UnramifiedAt K (heckeNormTwist K t) v := by
  intro u hu
  rw [heckeNormTwist_local, hu]
  simp

theorem unramifiedAt_mul_normTwist_iff (χ : HeckeCharacter K) (t : ℝ)
    (v : HeightOneSpectrum (𝓞 K)) :
    UnramifiedAt K (χ * heckeNormTwist K t) v ↔ UnramifiedAt K χ v := by
  constructor
  · intro h u hu
    have hh := h u hu
    change localComponent K v χ u * localComponent K v (heckeNormTwist K t) u = 1 at hh
    rw [unramifiedAt_normTwist K t v u hu, mul_one] at hh
    exact hh
  · intro h
    exact h.mul K (unramifiedAt_normTwist K t v)

/-- An unramified component takes equal values on local elements of equal norm.
In particular, it is independent of the chosen local uniformizer. -/
theorem UnramifiedAt.eq_of_norm_eq {χ : HeckeCharacter K} {v : HeightOneSpectrum (𝓞 K)}
    (hχ : UnramifiedAt K χ v) (u w : (v.adicCompletion K)ˣ)
    (hw : ‖u.val‖ = ‖w.val‖) : localComponent K v χ u = localComponent K v χ w := by
  have hn : ‖(u * w⁻¹).val‖ = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    rw [norm_mul, norm_inv, hw, mul_inv_cancel₀ (norm_ne_zero_iff.mpr w.ne_zero)]
  have hh := hχ (u * w⁻¹) hn
  rw [map_mul, map_inv] at hh
  exact mul_inv_eq_one.mp hh

end HeckeGeneral.Characters
