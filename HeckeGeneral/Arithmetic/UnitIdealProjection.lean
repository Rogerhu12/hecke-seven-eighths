import HeckeGeneral.Arithmetic.UnitOrbitAverage
import HeckeGeneral.Arithmetic.IdealFourierProjection

/-!
# Unit averaging and ideal masks are commuting contractions

The physical mask is stable under every actual unit because ideal
membership is stable under unit multiplication. This proves commutation
with finite unit averaging. Fourier conjugation transfers commutation to
the dual annihilator projection. The energy estimate for averaging is
derived by finite Cauchy–Schwarz, not stipulated as an operator bound.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.PeriodicFourier

open IdealMobiusMask IdealFourierOrthogonality
open scoped BigOperators Classical

variable {R : Type*} [CommRing R] [Fintype R]

theorem norm_sum_sq_le_card_energy {A : Type*} [Fintype A] (v : A → ℂ) :
    ‖∑ a : A, v a‖ ^ 2 ≤ (Fintype.card A : ℝ) * energy v := by
  have hn : ‖∑ a : A, v a‖ ≤ Real.sqrt (Fintype.card A) * l2Norm v :=
    (norm_sum_le _ _).trans (l1Mass_le_sqrt_card_mul_l2Norm v)
  have hs := (sq_le_sq₀ (norm_nonneg (∑ a : A, v a))
    (mul_nonneg (Real.sqrt_nonneg _) (l2Norm_nonneg v))).mpr hn
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), l2Norm_sq] using hs

theorem norm_unitAverage_sq_le (Γ : Subgroup Rˣ) (f : R → ℂ) (a : R) :
    ‖unitAverage Γ f a‖ ^ 2 ≤ (Fintype.card Γ : ℝ)⁻¹ *
      ∑ u : Γ, ‖f ((u.val : R) * a)‖ ^ 2 := by
  have hs := norm_sum_sq_le_card_energy (fun u : Γ => f ((u.val : R) * a))
  unfold unitAverage
  rw [norm_mul, mul_pow]
  have hc : ‖(Fintype.card Γ : ℂ)⁻¹‖ = (Fintype.card Γ : ℝ)⁻¹ := by simp
  rw [hc]
  calc
    _ ≤ (Fintype.card Γ : ℝ)⁻¹ ^ 2 * ((Fintype.card Γ : ℝ) *
        energy (fun u : Γ => f ((u.val : R) * a))) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by
      have hn : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      unfold energy
      field_simp

theorem energy_unitAverage_le (Γ : Subgroup Rˣ) (f : R → ℂ) :
    energy (unitAverage Γ f) ≤ energy f := by
  calc
    energy (unitAverage Γ f) ≤ (Fintype.card Γ : ℝ)⁻¹ *
        ∑ a : R, ∑ u : Γ, ‖f ((u.val : R) * a)‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun a _ => norm_unitAverage_sq_le Γ f a)
    _ = energy f := by
      rw [Finset.sum_comm]
      have hs (u : Γ) : (∑ a : R, ‖f ((u.val : R) * a)‖ ^ 2) = energy f :=
        Fintype.sum_bijective _ u.val.mulLeft_bijective _ _ (fun _ => rfl)
      simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hc : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem l2Norm_unitAverage_le (Γ : Subgroup Rˣ) (f : R → ℂ) :
    l2Norm (unitAverage Γ f) ≤ l2Norm f :=
  Real.sqrt_le_sqrt (energy_unitAverage_le Γ f)

omit [Fintype R] in
theorem unit_mul_mem_ideal_iff (I : Ideal R) (u : Rˣ) (a : R) :
    (u : R) * a ∈ I ↔ a ∈ I := by
  constructor
  · intro h
    have hi := I.mul_mem_left (↑(u⁻¹) : R) h
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using hi
  · exact I.mul_mem_left (u : R)

omit [Fintype R] in
theorem membershipIndicator_unit (I : Ideal R) (u : Rˣ) (a : R) :
    membershipIndicator I ((u : R) * a) = membershipIndicator I a := by
  simp only [membershipIndicator, unit_mul_mem_ideal_iff]

theorem unitAverage_idealMask (Γ : Subgroup Rˣ) (I : Ideal R) (f : R → ℂ) :
    unitAverage Γ (idealMask I f) = idealMask I (unitAverage Γ f) := by
  funext a
  unfold unitAverage idealMask
  simp only [membershipIndicator_unit, ← Finset.sum_mul, mul_assoc]

omit [Fintype R] in
theorem idealMask_preserves_invariance (Γ : Subgroup Rˣ) (I : Ideal R) (f : R → ℂ)
    (hf : UnitInvariant Γ f) : UnitInvariant Γ (idealMask I f) := by
  intro u hu a
  simp only [idealMask, membershipIndicator_unit, hf u hu]

theorem unitAverage_dualIdealAverage (Γ : Subgroup Rˣ) (I : Ideal R)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (g : R → ℂ) :
    unitAverage Γ (dualIdealAverage I g) = dualIdealAverage I (unitAverage Γ g) := by
  obtain ⟨f, rfl⟩ := fourier_surjective ψ hψ g
  have hmask (f : R → ℂ) : dualIdealAverage I (fourier ψ f) = fourier ψ (idealMask I f) := by
    funext h
    exact (fourier_idealMask ψ hψ I f h).symm
  rw [hmask, ← fourier_unitAverage, unitAverage_idealMask,
    ← fourier_unitAverage, hmask]

theorem energy_combinedProjection_le (Γ : Subgroup Rˣ) (I : Ideal R)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (g : R → ℂ) :
    energy (unitAverage Γ (dualIdealAverage I g)) ≤ energy g :=
  (energy_unitAverage_le Γ _).trans (energy_dualIdealAverage_le ψ hψ I g)

end HeckeGeneral.Arithmetic.PeriodicFourier
