import HeckePort.Moments.ReflectionDeletion

/-!
# Normalized reflection from the plain reflection

Port of the formal part of openai/math `OAI/NumberTheory/DirichletL/Moments/ComparisonReflection.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

openai proves `primitive_plain_reflection` (the Poisson/Gauss-sum reflection of a primitive
character, summed over *elements* `z : ℤ[ω]` and converted to a sum over ideals with the factor `6 =
#ℤ[ω]ˣ` by `radial_ideal_reindex`) and deduces `primitive_normalized_reflection`.
The element-to-ideal conversion uses the finite unit group of `ℤ[ω]` and has no analogue over
a general field (the unit group is infinite; the project's replacement is the finite sector
decomposition by `SixthUnitClasses`, i.e. `HeckeGeneral`'s theta reflection), so
`radial_ideal_reindex`, `primitive_plain_reflection`, `bounded_radial_summable`, `residue_zero` and
`reflected_profile_height_control` (which uses the cubic kernel `paperRadialFourier`) are not ported.

Ported: `residue_nontrivial` (a nontrivial character forces a nontrivial ring),
`inverse_half_power`, and `primitive_normalized_reflection`, the formal passage from the plain
reflection (hypothesis `hplain`, with `c0 = |c|` the archimedean size of the conductor, so
that `N(conductor) = c0 ^ 2`) to the normalized polynomial reflection.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators

variable {K : Type*} [Field K] [NumberField K]

lemma residue_nontrivial {R : Type*} [CommRing R] (χ : MulChar R ℂ) (hχ : χ ≠ 1) :
    Nontrivial R := by
  by_contra h
  have : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
  apply hχ
  ext x
  have hx : x = 1 := Subsingleton.elim _ _
  simp [hx]

lemma inverse_half_power (X : ℝ) (hX : 0 ≤ X) :
    (X : ℂ) ^ (-(1 / 2 : ℂ)) = (Real.sqrt X : ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    (Complex.ofReal_cpow hX (1 / 2)).symm

/-- openai `primitive_normalized_reflection`, from the plain reflection `hplain`
(openai `primitive_plain_reflection`, with `‖eisEmbedding c‖ = c0`). -/
theorem primitive_normalized_reflection (a ai : Ideal (𝓞 K) → ℂ) (W F : ℝ → ℂ) (G : ℂ)
    (c0 : ℝ) (hc0 : 0 < c0) (X : ℝ) (hX : 0 < X)
    (hplain : (∑' I : NI K, a I.val * W (inorm I / X)) =
      ((X : ℂ) * G / (c0 : ℂ)) * ∑' I : NI K, ai I.val * F (inorm I / (c0 ^ 2 / X))) :
    plainPoly a W X = G * plainPoly ai F (c0 ^ 2 / X) := by
  have hY : 0 < c0 ^ 2 / X := div_pos (sq_pos_of_pos hc0) hX
  unfold plainPoly
  rw [hplain]
  have hs : Real.sqrt (c0 ^ 2 / X) = c0 / Real.sqrt X := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hc0.le]
  have hx : (Real.sqrt X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  have hcn : (c0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc0.ne'
  have hsq : (Real.sqrt X : ℂ) ^ 2 = (X : ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  have hfac : (Real.sqrt X : ℂ)⁻¹ * ((X : ℂ) * G / (c0 : ℂ)) =
      G * (Real.sqrt (c0 ^ 2 / X) : ℂ)⁻¹ := by
    rw [hs, Complex.ofReal_div]
    field_simp
    rw [hsq]
  rw [← mul_assoc, hfac, mul_assoc]

end HeckePort.Moments

end
