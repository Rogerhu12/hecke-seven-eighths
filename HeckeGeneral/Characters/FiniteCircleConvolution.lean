import HeckeGeneral.Characters.FiniteCircleFourier

/-! Convolution is diagonalized by the finite circle-valued character transform. -/

noncomputable section

namespace HeckeGeneral.Characters

open scoped Classical

variable (G : Type*) [CommGroup G] [Fintype G] [Fintype (G →* Circle)]

def finiteGroupConvolution (F H : G → ℂ) (x : G) : ℂ :=
  ∑ y, F y * H (y⁻¹ * x)

omit [Fintype (G →* Circle)] in
theorem finiteGroupConvolution_add_left (F H A : G → ℂ) :
    finiteGroupConvolution G (F + H) A =
      finiteGroupConvolution G F A + finiteGroupConvolution G H A := by
  funext x
  simp [finiteGroupConvolution, add_mul, Finset.sum_add_distrib]

omit [Fintype (G →* Circle)] in
theorem finiteGroupConvolution_add_right (F H A : G → ℂ) :
    finiteGroupConvolution G F (H + A) =
      finiteGroupConvolution G F H + finiteGroupConvolution G F A := by
  funext x
  simp [finiteGroupConvolution, mul_add, Finset.sum_add_distrib]

omit [Fintype (G →* Circle)] in
theorem finiteFourierCoeff_convolution (F H : G → ℂ) :
    finiteFourierCoeff G (finiteGroupConvolution G F H) =
      finiteFourierCoeff G F * finiteFourierCoeff G H := by
  funext χ
  simp only [finiteFourierCoeff, finiteGroupConvolution, Pi.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have hs := (Group.mulLeft_bijective y).sum_comp
    (fun x : G => F y * H (y⁻¹ * x) * (χ x : ℂ)⁻¹)
  rw [← hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [inv_mul_cancel_left, map_mul, Circle.coe_mul, mul_inv_rev]
  ring

theorem finiteGroupConvolution_comm (F H : G → ℂ) :
    finiteGroupConvolution G F H = finiteGroupConvolution G H F := by
  apply finiteFourierCoeff_injective G
  rw [finiteFourierCoeff_convolution, finiteFourierCoeff_convolution, mul_comm]

theorem finiteGroupConvolution_assoc (F H A : G → ℂ) :
    finiteGroupConvolution G (finiteGroupConvolution G F H) A =
      finiteGroupConvolution G F (finiteGroupConvolution G H A) := by
  apply finiteFourierCoeff_injective G
  simp only [finiteFourierCoeff_convolution, mul_assoc]

@[simp] theorem finiteGroupConvolution_pointMass_one_left (F : G → ℂ) :
    finiteGroupConvolution G (finitePointMass G 1) F = F := by
  apply finiteFourierCoeff_injective G
  rw [finiteFourierCoeff_convolution]
  have h : finiteFourierCoeff G (finitePointMass G 1) = 1 := by
    funext χ
    simp
  rw [h, one_mul]

@[simp] theorem finiteGroupConvolution_pointMass_one_right (F : G → ℂ) :
    finiteGroupConvolution G F (finitePointMass G 1) = F := by
  rw [finiteGroupConvolution_comm, finiteGroupConvolution_pointMass_one_left]

omit [Fintype (G →* Circle)] in
theorem finiteGroupConvolution_pointMass (a : G) (F : G → ℂ) (x : G) :
    finiteGroupConvolution G (finitePointMass G a) F x = F (a⁻¹ * x) := by
  simp [finiteGroupConvolution, finitePointMass]

theorem finiteFourierInverse_mul (A B : (G →* Circle) → ℂ) :
    finiteFourierInverse G (A * B) =
      finiteGroupConvolution G (finiteFourierInverse G A) (finiteFourierInverse G B) := by
  apply finiteFourierCoeff_injective G
  rw [finiteFourier_coeff_inverse, finiteFourierCoeff_convolution,
    finiteFourier_coeff_inverse, finiteFourier_coeff_inverse]

omit [Fintype (G →* Circle)] in
theorem finiteGroupConvolution_smul_left (c : ℂ) (F H : G → ℂ) :
    finiteGroupConvolution G (c • F) H = c • finiteGroupConvolution G F H := by
  funext x
  simp [finiteGroupConvolution, mul_assoc, Finset.mul_sum]

theorem finiteGroupConvolution_smul_right (c : ℂ) (F H : G → ℂ) :
    finiteGroupConvolution G F (c • H) = c • finiteGroupConvolution G F H := by
  rw [finiteGroupConvolution_comm, finiteGroupConvolution_smul_left,
    finiteGroupConvolution_comm]

omit [Fintype (G →* Circle)] in
theorem finiteGroupConvolution_character (χ ψ : G →* Circle) (x : G) :
    finiteGroupConvolution G (fun y => (χ y : ℂ)) (fun y => (ψ y : ℂ)) x =
      if χ = ψ then (Nat.card G : ℂ) * (χ x : ℂ) else 0 := by
  have he : finiteGroupConvolution G (fun y => (χ y : ℂ)) (fun y => (ψ y : ℂ)) x =
      (ψ x : ℂ) * ∑ y : G, (χ y : ℂ) * (ψ y : ℂ)⁻¹ := by
    simp only [finiteGroupConvolution, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [he, sum_circleCharacter_mul_inv]
  by_cases h : χ = ψ
  · subst ψ
    simp [mul_comm]
  · simp [h]

omit [Fintype (G →* Circle)] in
theorem finiteGroupConvolution_eigencharacter (F : G → ℂ) (χ : G →* Circle) (x : G) :
    finiteGroupConvolution G F (fun y => (χ y : ℂ)) x =
      finiteFourierCoeff G F χ * (χ x : ℂ) := by
  simp only [finiteGroupConvolution, finiteFourierCoeff, map_mul, map_inv,
    Circle.coe_mul, Circle.coe_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  ring

end HeckeGeneral.Characters
