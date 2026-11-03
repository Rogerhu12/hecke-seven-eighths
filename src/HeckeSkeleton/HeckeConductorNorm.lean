import HeckeGeneral.Characters.ConductorArithmetic
import HeckeSkeleton.ExplicitHeckeFunctionalEquation
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic

/-!
Actual global conductor bounds from the proved local max inequality.
All characters are continuous unitary Hecke characters; no ramification or
finite-order hypothesis is added. The remaining high-row radical bound is
an arithmetic property of its specific Kummer constructor.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HeckeConductorNorm

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open scoped nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The quotient ideal is built from the difference of actual conductor
exponents; local cancellation can only make the product conductor smaller. -/
theorem finiteConductor_mul_dvd (χ ψ : HeckeCharacter K) :
    (finiteConductor K (χ * ψ)).val ∣
      (finiteConductor K χ).val * (finiteConductor K ψ).val := by
  let q := idealOfPrimeExponents
    (conductorExponents K χ + conductorExponents K ψ - conductorExponents K (χ * ψ))
  have hexp : conductorExponents K (χ * ψ) +
      (conductorExponents K χ + conductorExponents K ψ - conductorExponents K (χ * ψ)) =
      conductorExponents K χ + conductorExponents K ψ := by
    ext p
    have hp := localConductorExponent_mul_le_max K χ ψ p
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, conductorExponents_apply]
    omega
  have hq : finiteConductor K (χ * ψ) * q = finiteConductor K χ * finiteConductor K ψ := by
    change idealOfPrimeExponents (conductorExponents K (χ * ψ)) *
      idealOfPrimeExponents _ = idealOfPrimeExponents _ * idealOfPrimeExponents _
    rw [← idealOfPrimeExponents_add, hexp, idealOfPrimeExponents_add]
  refine ⟨q.val, ?_⟩
  simpa only [Submonoid.coe_mul] using (congrArg Subtype.val hq).symm

theorem finiteConductor_mul_norm_le (χ ψ : HeckeCharacter K) :
    (finiteConductor K (χ * ψ)).val.absNorm ≤
      (finiteConductor K χ).val.absNorm * (finiteConductor K ψ).val.absNorm := by
  have hd := map_dvd Ideal.absNorm (finiteConductor_mul_dvd K χ ψ)
  have hpos := mul_pos (Ideal.absNorm_pos_of_nonZeroDivisors (finiteConductor K χ))
    (Ideal.absNorm_pos_of_nonZeroDivisors (finiteConductor K ψ))
  apply Nat.le_of_dvd hpos
  simpa only [map_mul] using hd

theorem conductorScale_pos (χ : HeckeCharacter K) : 0 < heckeConductorScale K χ := by
  unfold heckeConductorScale
  exact mul_pos (Nat.cast_pos.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)))
    (Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors (finiteConductor K χ)))

@[simp] theorem conductorScale_inv (χ : HeckeCharacter K) :
    heckeConductorScale K χ⁻¹ = heckeConductorScale K χ := by
  simp only [heckeConductorScale, finiteConductor_inv]

/-- A fixed background costs only its finite conductor norm. The
discriminant appears once, in the varying character's actual FE scale. -/
theorem conductorScale_mul_le (β χ : HeckeCharacter K) :
    heckeConductorScale K (β * χ) ≤
      ((finiteConductor K β).val.absNorm : ℝ) * heckeConductorScale K χ := by
  have hn : ((finiteConductor K (β * χ)).val.absNorm : ℝ) ≤
      ((finiteConductor K β).val.absNorm : ℝ) * ((finiteConductor K χ).val.absNorm : ℝ) := by
    exact_mod_cast finiteConductor_mul_norm_le K β χ
  unfold heckeConductorScale
  exact (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)).trans_eq (by ring)

theorem conductorScale_mul_conjugate_le (β χ : HeckeCharacter K) :
    heckeConductorScale K (β * conjugate χ) ≤
      ((finiteConductor K β).val.absNorm : ℝ) * heckeConductorScale K χ := by
  simpa only [conjugate, conductorScale_inv] using conductorScale_mul_le K β χ⁻¹

end HeckeSkeleton.HeckeConductorNorm
