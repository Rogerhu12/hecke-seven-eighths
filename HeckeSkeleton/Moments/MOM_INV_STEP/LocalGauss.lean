module

public import HeckeSkeleton.Moments.MOM_INV_STEP.LocalDigits
public import Mathlib.NumberTheory.GaussSum

/-!
# The finite Fourier coefficient at an active first-source prime

The transformed row is the inverse of the actual active character. The
formula includes zero frequency: both sides vanish there. The normalized
Gauss coefficient has norm one for a nontrivial additive character.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.LocalGauss

open CubeAlgebra LocalDigits
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]

theorem nonprincipal_fourier (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (k : F) :
    (∑ x : F, χ x * ψ (k * x)) = star (χ k) * gaussSum χ ψ := by
  by_cases hk : k = 0
  · subst k
    simpa only [zero_mul, AddChar.map_zero_eq_one, mul_one,
      MulChar.map_zero, star_zero, zero_mul] using MulChar.sum_eq_zero_of_ne_one hχ
  · have h := gaussSum_mulShift_eq χ ψ (Units.mk0 k hk)
    simpa only [gaussSum, AddChar.mulShift_apply, Units.val_mk0,
      ← MulChar.star_apply'] using h

theorem nonprincipal_gauss_norm_sq (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ (AddChar.IsPrimitive.of_ne_one hψ)
  rw [← star_gaussSum_eq, Complex.star_def, Complex.mul_conj'] at h
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.natCast_re] using
    congrArg Complex.re h

theorem nonprincipal_gauss_norm (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  rw [← nonprincipal_gauss_norm_sq χ hχ ψ hψ, Real.sqrt_sq (norm_nonneg _)]

def normalizedGauss (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  gaussSum χ ψ / (Real.sqrt (Fintype.card F : ℝ) : ℂ)

theorem normalizedGauss_norm (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) : ‖normalizedGauss χ ψ‖ = 1 := by
  have hcard : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < Real.sqrt (Fintype.card F : ℝ) := Real.sqrt_pos.mpr hcard
  rw [normalizedGauss, norm_div, nonprincipal_gauss_norm χ hχ ψ hψ,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_self (ne_of_gt hpos)]

/-- The primitive finite Fourier formula for the actual local source
digit, with scalar powers reduced only after source support is known. -/
theorem active_source_fourier (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (ε₁ ε₂ : Bool) (v₁ v₂ : ℕ)
    (hv : 0 < bit ε₁ + bit ε₂ + v₁ + v₂)
    (ht : conductorExponent (parity (v₁ + v₂)) ε₁ ε₂ ≠ 0) (k : F) :
    (∑ x : F, (χ x ^ (bit ε₁ + 3 * v₁) * star (χ x ^ (bit ε₂ + 3 * v₂))) *
      ψ (k * x)) =
    star ((χ ^ (conductorExponent (parity (v₁ + v₂)) ε₁ ε₂).val) k) *
      gaussSum (χ ^ (conductorExponent (parity (v₁ + v₂)) ε₁ ε₂).val) ψ := by
  have h6 : χ ^ 6 = 1 := by
    rw [← hχ]
    exact pow_orderOf_eq_one _
  simp_rw [local_source_reduction_of_supported χ h6 ε₁ ε₂ v₁ v₂ hv]
  apply nonprincipal_fourier
  exact fun h => ht ((local_conductor_principal_iff χ hχ ε₁ ε₂ v₁ v₂).mp h)

theorem active_normalizedGauss_norm (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (ε₁ ε₂ : Bool) (v₁ v₂ : ℕ)
    (ht : conductorExponent (parity (v₁ + v₂)) ε₁ ε₂ ≠ 0) :
    ‖normalizedGauss (χ ^ (conductorExponent (parity (v₁ + v₂)) ε₁ ε₂).val) ψ‖ = 1 := by
  apply normalizedGauss_norm _ _ ψ hψ
  exact fun h => ht ((local_conductor_principal_iff χ hχ ε₁ ε₂ v₁ v₂).mp h)

end HeckeSkeleton.Moments.MOM_INV_STEP.LocalGauss

end
