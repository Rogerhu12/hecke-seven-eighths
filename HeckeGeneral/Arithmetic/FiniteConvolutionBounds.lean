import HeckeGeneral.Arithmetic.FiniteFourierConvolution

/-!
# Norm bounds for finite convolution and correlation

The cardinality in Plancherel cancels from Young's L1–L2 inequality.
The pointwise Cauchy bound and the L1 inequality do not require a primitive
pairing; the frequency proof of the L2 inequality states that hypothesis
explicitly. No infinite sum or orbital convergence input occurs here.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.PeriodicFourier

open scoped BigOperators ComplexConjugate Classical

variable {R : Type*} [CommRing R] [Fintype R]

def subtractEquiv (x : R) : R ≃ R where
  toFun a := x - a
  invFun a := x - a
  left_inv a := by ring
  right_inv a := by ring

theorem sum_subtract {M : Type*} [AddCommMonoid M] (f : R → M) (x : R) :
    ∑ a : R, f (x - a) = ∑ a : R, f a :=
  (subtractEquiv x).sum_comp f

theorem norm_convolution_le_l2 (f g : R → ℂ) (x : R) :
    ‖convolution f g x‖ ≤ l2Norm f * l2Norm g := by
  apply (norm_convolution_le f g x).trans
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun a : R => ‖f a‖) (fun a : R => ‖g (x - a)‖)
  rw [sum_subtract (fun a => ‖g a‖ ^ 2)] at h
  exact h

theorem norm_correlation_le_l2 (f g : R → ℂ) (b : R) :
    ‖correlation f g b‖ ≤ l2Norm f * l2Norm g := by
  calc
    ‖correlation f g b‖ ≤ ∑ a : R, ‖f (a + b)‖ * ‖g a‖ := by
      simpa [correlation] using
        norm_sum_le Finset.univ (fun a => f (a + b) * conj (g a))
    _ ≤ l2Norm f * l2Norm g := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun a : R => ‖translate b f a‖) (fun a : R => ‖g a‖)
      change (∑ a : R, ‖f (a + b)‖ * ‖g a‖) ≤ l2Norm (translate b f) * l2Norm g at h
      rw [l2Norm_translate] at h
      exact h

theorem l1Mass_convolution_le (f g : R → ℂ) :
    l1Mass (convolution f g) ≤ l1Mass f * l1Mass g := by
  calc
    l1Mass (convolution f g) ≤ ∑ x : R, ∑ a : R, ‖f a‖ * ‖g (x - a)‖ := by
      exact Finset.sum_le_sum (fun x _ => norm_convolution_le f g x)
    _ = l1Mass f * l1Mass g := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      have hs (a : R) : (∑ x : R, ‖g (x - a)‖) = l1Mass g := by
        simpa [l1Mass, sub_eq_add_neg] using
          Equiv.sum_comp (Equiv.addRight (-a)) (fun x => ‖g x‖)
      simp only [hs, ← Finset.sum_mul, l1Mass]

theorem energy_convolution_le_l1_l2 (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f g : R → ℂ) : energy (convolution f g) ≤ l1Mass f ^ 2 * energy g := by
  have hfreq : (∑ h : R, ‖fourier ψ f h‖ ^ 2 * ‖fourier ψ g h‖ ^ 2) ≤
      l1Mass f ^ 2 * energy (fourier ψ g) := by
    rw [energy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (sq_le_sq₀ (norm_nonneg _) (l1Mass_nonneg f)).mpr (norm_fourier_le_l1Mass ψ f h)
  rw [← energy_convolution ψ hψ f g, energy_fourier ψ hψ g] at hfreq
  have hcard : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  nlinarith

theorem l2Norm_convolution_le_l1_l2 (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f g : R → ℂ) : l2Norm (convolution f g) ≤ l1Mass f * l2Norm g := by
  have h := energy_convolution_le_l1_l2 ψ hψ f g
  have he := l2Norm_sq (convolution f g)
  have hg := l2Norm_sq g
  have hn := l2Norm_nonneg (convolution f g)
  have hr := mul_nonneg (l1Mass_nonneg f) (l2Norm_nonneg g)
  nlinarith

theorem energy_correlation_le_l1_l2 (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f g : R → ℂ) : energy (correlation f g) ≤ l1Mass f ^ 2 * energy g := by
  have hfreq : (∑ h : R, ‖fourier ψ f h‖ ^ 2 * ‖fourier ψ g h‖ ^ 2) ≤
      l1Mass f ^ 2 * energy (fourier ψ g) := by
    rw [energy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (sq_le_sq₀ (norm_nonneg _) (l1Mass_nonneg f)).mpr (norm_fourier_le_l1Mass ψ f h)
  rw [← energy_correlation ψ hψ f g, energy_fourier ψ hψ g] at hfreq
  have hcard : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  nlinarith

theorem l2Norm_correlation_le_l1_l2 (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f g : R → ℂ) : l2Norm (correlation f g) ≤ l1Mass f * l2Norm g := by
  have h := energy_correlation_le_l1_l2 ψ hψ f g
  have he := l2Norm_sq (correlation f g)
  have hg := l2Norm_sq g
  have hn := l2Norm_nonneg (correlation f g)
  have hr := mul_nonneg (l1Mass_nonneg f) (l2Norm_nonneg g)
  nlinarith

end HeckeGeneral.Arithmetic.PeriodicFourier
