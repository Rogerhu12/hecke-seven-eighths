import HeckeGeneral.Arithmetic.FiniteFourierBounds

/-!
# Convolution and correlation in the actual finite residue ring

The Fourier sign is positive and the transform is unnormalized. Every
translation, convolution and correlation here is a finite sum on the
ring itself. The Gram identities are consequently algebraic foundations
for a common kernel; they supply no archimedean or orbital estimate.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.PeriodicFourier

open scoped BigOperators ComplexConjugate Classical

variable {R : Type*} [CommRing R] [Fintype R]

def translate (b : R) (f : R → ℂ) (a : R) : ℂ := f (a + b)

def modulate (ψ : AddChar R ℂ) (b : R) (f : R → ℂ) (a : R) : ℂ :=
  ψ (b * a) * f a

def reflectConjugate (f : R → ℂ) (a : R) : ℂ := conj (f (-a))

def convolution (f g : R → ℂ) (x : R) : ℂ := ∑ a : R, f a * g (x - a)

def correlation (f g : R → ℂ) (b : R) : ℂ := ∑ a : R, f (a + b) * conj (g a)

omit [Fintype R] in
@[simp] theorem translate_zero (f : R → ℂ) : translate 0 f = f := by
  funext a
  simp [translate]

omit [Fintype R] in
theorem translate_translate (b c : R) (f : R → ℂ) :
    translate b (translate c f) = translate (b + c) f := by
  funext a
  simp [translate, add_assoc]

theorem sum_translate (f : R → ℂ) (b : R) :
    ∑ a : R, translate b f a = ∑ a : R, f a := by
  unfold translate
  exact Fintype.sum_bijective _ (Equiv.addRight b).bijective _ _ (fun _ => rfl)

theorem l1Mass_translate (f : R → ℂ) (b : R) : l1Mass (translate b f) = l1Mass f := by
  unfold l1Mass translate
  exact Fintype.sum_bijective _ (Equiv.addRight b).bijective _ _ (fun _ => rfl)

theorem energy_translate (f : R → ℂ) (b : R) : energy (translate b f) = energy f := by
  unfold energy translate
  exact Fintype.sum_bijective _ (Equiv.addRight b).bijective _ _ (fun _ => rfl)

theorem l2Norm_translate (f : R → ℂ) (b : R) : l2Norm (translate b f) = l2Norm f := by
  simp only [l2Norm, energy_translate]

theorem fourier_translate (ψ : AddChar R ℂ) (f : R → ℂ) (b h : R) :
    fourier ψ (translate b f) h = ψ (-(h * b)) * fourier ψ f h := by
  unfold fourier translate
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective _ (Equiv.addRight b).bijective _ _ (fun a => ?_)
  change f (a + b) * ψ (h * a) = ψ (-(h * b)) * (f (a + b) * ψ (h * (a + b)))
  rw [← mul_assoc, mul_comm (ψ (-(h * b))) (f (a + b)), mul_assoc,
    ← ψ.map_add_eq_mul]
  congr 2
  ring

theorem fourier_modulate (ψ : AddChar R ℂ) (f : R → ℂ) (b h : R) :
    fourier ψ (modulate ψ b f) h = fourier ψ f (h + b) := by
  unfold fourier modulate
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm (ψ (b * a)) (f a), mul_assoc, ← ψ.map_add_eq_mul]
  congr 2
  ring

theorem energy_modulate (ψ : AddChar R ℂ) (f : R → ℂ) (b : R) :
    energy (modulate ψ b f) = energy f := by
  simp [energy, modulate, AddChar.norm_apply]

theorem fourier_reflectConjugate (ψ : AddChar R ℂ) (f : R → ℂ) (h : R) :
    fourier ψ (reflectConjugate f) h = conj (fourier ψ f h) := by
  unfold fourier reflectConjugate
  rw [map_sum]
  refine Fintype.sum_bijective _ (Equiv.neg R).bijective _ _ (fun a => ?_)
  simp [map_mul, AddChar.map_neg_eq_conj]

theorem convolution_eq_correlation (f g : R → ℂ) :
    convolution f (reflectConjugate g) = correlation f g := by
  funext b
  unfold convolution reflectConjugate correlation
  refine Fintype.sum_bijective _ (Equiv.addRight (-b)).bijective _ _ (fun a => ?_)
  simp [sub_eq_add_neg]

theorem fourier_convolution (ψ : AddChar R ℂ) (f g : R → ℂ) (h : R) :
    fourier ψ (convolution f g) h = fourier ψ f h * fourier ψ g h := by
  unfold fourier convolution
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  symm
  refine Fintype.sum_bijective _ (Equiv.addRight a).bijective _ _ (fun b => ?_)
  change f a * ψ (h * a) * (g b * ψ (h * b)) =
    f a * g (b + a - a) * ψ (h * (b + a))
  simp only [add_sub_cancel_right]
  rw [show h * (b + a) = h * a + h * b by ring, ψ.map_add_eq_mul]
  ring

theorem fourier_correlation (ψ : AddChar R ℂ) (f g : R → ℂ) (h : R) :
    fourier ψ (correlation f g) h = fourier ψ f h * conj (fourier ψ g h) := by
  rw [← convolution_eq_correlation, fourier_convolution, fourier_reflectConjugate]

theorem fourier_autocorrelation (ψ : AddChar R ℂ) (f : R → ℂ) (h : R) :
    fourier ψ (correlation f f) h = (‖fourier ψ f h‖ ^ 2 : ℝ) := by
  rw [fourier_correlation, Complex.mul_conj']
  simp

theorem correlation_zero_re (f : R → ℂ) : (correlation f f 0).re = energy f := by
  have hsq (z : ℂ) : (z * conj z).re = ‖z‖ ^ 2 := by
    simp [Complex.mul_conj', pow_two]
  simp [correlation, energy, hsq]

theorem correlation_hermitian (f g : R → ℂ) (b : R) :
    correlation f g (-b) = conj (correlation g f b) := by
  unfold correlation
  rw [map_sum]
  refine Fintype.sum_bijective _ (Equiv.addRight (-b)).bijective _ _ (fun a => ?_)
  simp [map_mul, mul_comm]

theorem convolution_zero_left (f : R → ℂ) : convolution (fun _ => 0) f = fun _ => 0 := by
  funext x
  simp [convolution]

theorem convolution_zero_right (f : R → ℂ) : convolution f (fun _ => 0) = fun _ => 0 := by
  funext x
  simp [convolution]

theorem convolution_add_left (f₁ f₂ g : R → ℂ) :
    convolution (fun x => f₁ x + f₂ x) g = fun x => convolution f₁ g x + convolution f₂ g x := by
  funext x
  simp [convolution, add_mul, Finset.sum_add_distrib]

theorem convolution_add_right (f g₁ g₂ : R → ℂ) :
    convolution f (fun x => g₁ x + g₂ x) = fun x => convolution f g₁ x + convolution f g₂ x := by
  funext x
  simp [convolution, mul_add, Finset.sum_add_distrib]

theorem convolution_const_mul_left (f g : R → ℂ) (c : ℂ) :
    convolution (fun x => c * f x) g = fun x => c * convolution f g x := by
  funext x
  simp [convolution, Finset.mul_sum, mul_assoc]

theorem convolution_const_mul_right (f g : R → ℂ) (c : ℂ) :
    convolution f (fun x => c * g x) = fun x => c * convolution f g x := by
  funext x
  simp [convolution, Finset.mul_sum, mul_left_comm]

theorem norm_convolution_le (f g : R → ℂ) (x : R) :
    ‖convolution f g x‖ ≤ ∑ a : R, ‖f a‖ * ‖g (x - a)‖ := by
  simpa only [convolution, norm_mul] using norm_sum_le Finset.univ (fun a => f a * g (x - a))

theorem energy_convolution (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f g : R → ℂ) :
    (Fintype.card R : ℝ) * energy (convolution f g) =
      ∑ h : R, ‖fourier ψ f h‖ ^ 2 * ‖fourier ψ g h‖ ^ 2 := by
  rw [← energy_fourier ψ hψ]
  simp [energy, fourier_convolution, mul_pow]

theorem energy_correlation (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f g : R → ℂ) :
    (Fintype.card R : ℝ) * energy (correlation f g) =
      ∑ h : R, ‖fourier ψ f h‖ ^ 2 * ‖fourier ψ g h‖ ^ 2 := by
  rw [← energy_fourier ψ hψ]
  simp [energy, fourier_correlation, mul_pow]

end HeckeGeneral.Arithmetic.PeriodicFourier
