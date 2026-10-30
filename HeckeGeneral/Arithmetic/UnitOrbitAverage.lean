import HeckeGeneral.Arithmetic.FiniteFourierBounds

/-!
# Actual averaging over a subgroup of residue-ring units

The finite group is a subgroup of the real unit group of the ring.
Averaging is defined by its finite sum, yields an invariant function,
and commutes with the finite Fourier transform after inversion of units.
This is the finite front end of unit-sector invariance; it does not
replace an infinite S-unit quotient by a finite group.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.PeriodicFourier

open scoped BigOperators Classical

variable {R : Type*} [CommRing R] [Fintype R]

instance fintypeUnitSubgroup (Γ : Subgroup Rˣ) : Fintype Γ := Fintype.ofFinite _

def unitAverage (Γ : Subgroup Rˣ) (f : R → ℂ) (a : R) : ℂ :=
  (Fintype.card Γ : ℂ)⁻¹ * ∑ u : Γ, f ((u.val : R) * a)

theorem unitAverage_invariant (Γ : Subgroup Rˣ) (f : R → ℂ) :
    UnitInvariant Γ (unitAverage Γ f) := by
  intro v hv a
  unfold unitAverage
  congr 1
  refine Fintype.sum_bijective _ (Equiv.mulRight (⟨v, hv⟩ : Γ)).bijective _ _ (fun u => ?_)
  congr 1
  change (u.val : R) * ((v : R) * a) = ((u.val * v : Rˣ) : R) * a
  simp only [Units.val_mul, mul_assoc]

theorem unitAverage_of_invariant (Γ : Subgroup Rˣ) (f : R → ℂ)
    (hf : UnitInvariant Γ f) : unitAverage Γ f = f := by
  funext a
  unfold unitAverage
  simp only [hf _ (Subtype.property _), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem unitAverage_idempotent (Γ : Subgroup Rˣ) (f : R → ℂ) :
    unitAverage Γ (unitAverage Γ f) = unitAverage Γ f :=
  unitAverage_of_invariant Γ _ (unitAverage_invariant Γ f)

theorem unitAverage_eq_self_iff (Γ : Subgroup Rˣ) (f : R → ℂ) :
    unitAverage Γ f = f ↔ UnitInvariant Γ f := by
  constructor
  · intro h
    rw [← h]
    exact unitAverage_invariant Γ f
  · exact unitAverage_of_invariant Γ f

theorem unitAverage_add (Γ : Subgroup Rˣ) (f g : R → ℂ) :
    unitAverage Γ (fun a => f a + g a) = fun a => unitAverage Γ f a + unitAverage Γ g a := by
  funext a
  simp [unitAverage, Finset.sum_add_distrib, mul_add]

theorem unitAverage_const_mul (Γ : Subgroup Rˣ) (f : R → ℂ) (c : ℂ) :
    unitAverage Γ (fun a => c * f a) = fun a => c * unitAverage Γ f a := by
  funext a
  simp [unitAverage, Finset.mul_sum, mul_left_comm]

theorem unitAverage_dilate (Γ : Subgroup Rˣ) (f : R → ℂ) (d : R) :
    unitAverage Γ (dilate d f) = dilate d (unitAverage Γ f) := by
  funext a
  unfold unitAverage dilate
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  ring

theorem fourier_unitAverage (Γ : Subgroup Rˣ) (ψ : AddChar R ℂ) (f : R → ℂ) :
    fourier ψ (unitAverage Γ f) = unitAverage Γ (fourier ψ f) := by
  funext h
  unfold unitAverage
  rw [fourier_const_mul, fourier_sum Finset.univ]
  change (Fintype.card Γ : ℂ)⁻¹ * (∑ u : Γ, fourier ψ (dilate (u.val : R) f) h) = _
  simp only [fourier_dilate_unit]
  congr 1
  refine Fintype.sum_bijective _ (Equiv.inv Γ).bijective _ _ (fun u => ?_)
  rfl

theorem unitAverage_zero_frequency (Γ : Subgroup Rˣ) (ψ : AddChar R ℂ) (f : R → ℂ) :
    fourier ψ (unitAverage Γ f) 0 = fourier ψ f 0 := by
  rw [fourier_unitAverage]
  unfold unitAverage
  simp only [mul_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem sum_unitAverage (Γ : Subgroup Rˣ) (f : R → ℂ) :
    ∑ a : R, unitAverage Γ f a = ∑ a : R, f a := by
  unfold unitAverage
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hs (u : Γ) : (∑ a : R, f ((u.val : R) * a)) = ∑ a : R, f a :=
    Fintype.sum_bijective _ u.val.mulLeft_bijective _ _ (fun _ => rfl)
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem norm_unitAverage_le (Γ : Subgroup Rˣ) (f : R → ℂ) (a : R) :
    ‖unitAverage Γ f a‖ ≤ (Fintype.card Γ : ℝ)⁻¹ * ∑ u : Γ, ‖f ((u.val : R) * a)‖ := by
  unfold unitAverage
  rw [norm_mul]
  have hc : ‖(Fintype.card Γ : ℂ)⁻¹‖ = (Fintype.card Γ : ℝ)⁻¹ := by simp
  rw [hc]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

theorem l1Mass_unitAverage_le (Γ : Subgroup Rˣ) (f : R → ℂ) :
    l1Mass (unitAverage Γ f) ≤ l1Mass f := by
  calc
    l1Mass (unitAverage Γ f) ≤ (Fintype.card Γ : ℝ)⁻¹ *
        ∑ a : R, ∑ u : Γ, ‖f ((u.val : R) * a)‖ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun a _ => norm_unitAverage_le Γ f a)
    _ = l1Mass f := by
      rw [Finset.sum_comm]
      have hs (u : Γ) : (∑ a : R, ‖f ((u.val : R) * a)‖) = l1Mass f :=
        Fintype.sum_bijective _ u.val.mulLeft_bijective _ _ (fun _ => rfl)
      simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hc : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end HeckeGeneral.Arithmetic.PeriodicFourier
