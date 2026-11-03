import HeckeGeneral.Characters.FiniteCircleDual

/-! Finite Fourier inversion for the actual circle-valued character group. -/

noncomputable section

namespace HeckeGeneral.Characters

open scoped Classical

variable (G : Type*) [CommGroup G] [Fintype G] [Fintype (G →* Circle)]

theorem sum_circleDual (x : G) :
    (∑ χ : G →* Circle, (χ x : ℂ)) = if x = 1 then (Nat.card G : ℂ) else 0 := by
  by_cases hx : x = 1
  · subst x
    simp only [map_one, Circle.coe_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ite_true]
    exact_mod_cast (Nat.card_eq_fintype_card (α := G →* Circle)).symm.trans (natCard_circleDual G)
  · simp only [ite_eq_right hx]
    exact sum_circleDual_eq_zero G hx

theorem sum_circleDual_mul_inv (x y : G) :
    (∑ χ : G →* Circle, (χ x : ℂ) * (χ y : ℂ)⁻¹) =
      if x = y then (Nat.card G : ℂ) else 0 := by
  simpa only [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv, mul_inv_eq_one] using
    sum_circleDual G (x * y⁻¹)

def finiteFourierCoeff (F : G → ℂ) (χ : G →* Circle) : ℂ :=
  ∑ x, F x * (χ x : ℂ)⁻¹

def finiteFourierInverse (A : (G →* Circle) → ℂ) (x : G) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ χ, A χ * (χ x : ℂ)

theorem finiteFourier_reconstruction_sum (F : G → ℂ) (x : G) :
    (∑ χ : G →* Circle, finiteFourierCoeff G F χ * (χ x : ℂ)) =
      (Nat.card G : ℂ) * F x := by
  simp only [finiteFourierCoeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (y : G) :
      (∑ χ : G →* Circle, F y * (χ y : ℂ)⁻¹ * (χ x : ℂ)) =
        F y * (if x = y then (Nat.card G : ℂ) else 0) := by
    rw [← sum_circleDual_mul_inv G x y, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    ring
  simp_rw [he]
  simp [mul_comm]

@[simp] theorem finiteFourier_inverse_coeff (F : G → ℂ) :
    finiteFourierInverse G (finiteFourierCoeff G F) = F := by
  funext x
  rw [finiteFourierInverse, finiteFourier_reconstruction_sum, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne'), one_mul]

@[simp] theorem finiteFourier_coeff_inverse (A : (G →* Circle) → ℂ) :
    finiteFourierCoeff G (finiteFourierInverse G A) = A := by
  funext ψ
  simp only [finiteFourierCoeff, finiteFourierInverse]
  calc
    _ = (Nat.card G : ℂ)⁻¹ * ∑ χ, A χ *
        (∑ x : G, (χ x : ℂ) * (ψ x : ℂ)⁻¹) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (Nat.card G : ℂ)⁻¹ * (A ψ * Nat.card G) := by
      simp_rw [sum_circleCharacter_mul_inv]
      simp
    _ = A ψ := by
      rw [mul_left_comm, inv_mul_cancel₀
        (Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne'), mul_one]

omit [Fintype (G →* Circle)] in
theorem finiteFourierCoeff_add (F H : G → ℂ) :
    finiteFourierCoeff G (F + H) = finiteFourierCoeff G F + finiteFourierCoeff G H := by
  funext χ
  simp [finiteFourierCoeff, add_mul, Finset.sum_add_distrib]

omit [Fintype (G →* Circle)] in
theorem finiteFourierCoeff_smul (c : ℂ) (F : G → ℂ) :
    finiteFourierCoeff G (c • F) = c • finiteFourierCoeff G F := by
  funext χ
  simp [finiteFourierCoeff, mul_assoc, Finset.mul_sum]

theorem finiteFourierCoeff_injective : Function.Injective (finiteFourierCoeff G) := by
  intro F H h
  have := congrArg (finiteFourierInverse G) h
  simpa using this

theorem finiteFourierCoeff_surjective : Function.Surjective (finiteFourierCoeff G) := by
  intro A
  exact ⟨finiteFourierInverse G A, finiteFourier_coeff_inverse G A⟩

def finiteFourierLinearEquiv : (G → ℂ) ≃ₗ[ℂ] ((G →* Circle) → ℂ) where
  toFun := finiteFourierCoeff G
  invFun := finiteFourierInverse G
  left_inv := finiteFourier_inverse_coeff G
  right_inv := finiteFourier_coeff_inverse G
  map_add' := finiteFourierCoeff_add G
  map_smul' := finiteFourierCoeff_smul G

omit [Fintype (G →* Circle)] in
theorem finiteFourierCoeff_character (χ ψ : G →* Circle) :
    finiteFourierCoeff G (fun x => (χ x : ℂ)) ψ =
      if χ = ψ then (Nat.card G : ℂ) else 0 :=
  sum_circleCharacter_mul_inv G χ ψ

def finitePointMass (a : G) : G → ℂ := fun x => if x = a then 1 else 0

omit [Fintype (G →* Circle)] in
@[simp] theorem finiteFourierCoeff_pointMass (a : G) (χ : G →* Circle) :
    finiteFourierCoeff G (finitePointMass G a) χ = (χ a : ℂ)⁻¹ := by
  simp [finiteFourierCoeff, finitePointMass]

omit [Fintype (G →* Circle)] in
theorem finiteFourierCoeff_translate (a : G) (F : G → ℂ) (χ : G →* Circle) :
    finiteFourierCoeff G (fun x => F (a * x)) χ = (χ a : ℂ) * finiteFourierCoeff G F χ := by
  have hsum := (Group.mulLeft_bijective a).sum_comp
    (fun x : G => F x * (χ x : ℂ)⁻¹)
  simp only [finiteFourierCoeff]
  rw [← hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [map_mul, Circle.coe_mul, mul_inv_rev]
  field_simp

omit [Fintype (G →* Circle)] in
theorem finiteFourierCoeff_modulate (ψ : G →* Circle) (F : G → ℂ) (χ : G →* Circle) :
    finiteFourierCoeff G (fun x => F x * (ψ x : ℂ)) χ =
      finiteFourierCoeff G F (χ * ψ⁻¹) := by
  simp only [finiteFourierCoeff, MonoidHom.mul_apply, MonoidHom.inv_apply,
    Circle.coe_mul, Circle.coe_inv, mul_inv_rev, inv_inv]
  apply Finset.sum_congr rfl
  intro x _
  ring

end HeckeGeneral.Characters
