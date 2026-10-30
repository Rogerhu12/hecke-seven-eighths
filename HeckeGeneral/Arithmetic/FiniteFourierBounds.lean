import HeckeGeneral.Arithmetic.PeriodicFourier
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Energy and operator bounds for the actual finite Fourier transform

All sums use the finite ring itself. Parseval follows from the primitive
additive pairing and the finite Poisson identity. Character values have
norm one because the additive group is finite, rather than by an assumed
bound on a Fourier matrix. Nonunit dilations are handled by their actual
fibres, so no permutation or energy-preservation claim is made for them.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.PeriodicFourier

open scoped BigOperators ComplexConjugate Classical

variable {R : Type*} [Fintype R]

def l1Mass (f : R → ℂ) : ℝ := ∑ a : R, ‖f a‖

def energy (f : R → ℂ) : ℝ := ∑ a : R, ‖f a‖ ^ 2

def l2Norm (f : R → ℂ) : ℝ := Real.sqrt (energy f)

theorem l1Mass_nonneg (f : R → ℂ) : 0 ≤ l1Mass f :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem energy_nonneg (f : R → ℂ) : 0 ≤ energy f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem l2Norm_nonneg (f : R → ℂ) : 0 ≤ l2Norm f := Real.sqrt_nonneg _

theorem l2Norm_sq (f : R → ℂ) : l2Norm f ^ 2 = energy f :=
  Real.sq_sqrt (energy_nonneg f)

@[simp] theorem l1Mass_zero : l1Mass (fun _ : R => (0 : ℂ)) = 0 := by
  simp [l1Mass]

@[simp] theorem energy_zero : energy (fun _ : R => (0 : ℂ)) = 0 := by
  simp [energy]

theorem energy_eq_zero_iff (f : R → ℂ) : energy f = 0 ↔ ∀ a, f a = 0 := by
  rw [energy, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, sq_eq_zero_iff, norm_eq_zero]

theorem energy_const_mul (c : ℂ) (f : R → ℂ) :
    energy (fun a => c * f a) = ‖c‖ ^ 2 * energy f := by
  simp only [energy, norm_mul, mul_pow, Finset.mul_sum]

variable [CommRing R]

theorem fourier_conjugate (ψ : AddChar R ℂ) (f : R → ℂ) (h : R) :
    fourier ψ (fun a => conj (f a)) (-h) = conj (fourier ψ f h) := by
  simp only [fourier, map_sum, map_mul, neg_mul, AddChar.map_neg_eq_conj]

/-- The Hermitian pairing includes conjugation and the exact cardinality factor. -/
theorem parseval_pairing (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f g : R → ℂ) :
    (Fintype.card R : ℂ) * (∑ a : R, f a * conj (g a)) =
      ∑ h : R, fourier ψ f h * conj (fourier ψ g h) := by
  simpa only [fourier_conjugate] using finite_poisson ψ hψ f (fun a => conj (g a))

/-- Plancherel with the unnormalized finite transform. -/
theorem energy_fourier (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f : R → ℂ) :
    energy (fourier ψ f) = (Fintype.card R : ℝ) * energy f := by
  have h := congrArg Complex.re (parseval_pairing ψ hψ f f)
  have hsq (z : ℂ) : (z * conj z).re = ‖z‖ ^ 2 := by
    simp [Complex.mul_conj', pow_two]
  simpa [energy, hsq] using h.symm

theorem norm_fourier_le_l1Mass (ψ : AddChar R ℂ) (f : R → ℂ) (h : R) :
    ‖fourier ψ f h‖ ≤ l1Mass f := by
  unfold fourier l1Mass
  calc
    ‖∑ a : R, f a * ψ (h * a)‖ ≤ ∑ a : R, ‖f a * ψ (h * a)‖ := norm_sum_le _ _
    _ = ∑ a : R, ‖f a‖ := by simp [AddChar.norm_apply]

omit [CommRing R] in
theorem l1Mass_le_sqrt_card_mul_l2Norm (f : R → ℂ) :
    l1Mass f ≤ Real.sqrt (Fintype.card R) * l2Norm f := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun a : R => ‖f a‖) (fun _ => 1)
  simpa [l1Mass, l2Norm, energy, mul_comm] using h

/-- The exact elementary L2-to-pointwise operator bound. -/
theorem norm_fourier_le_sqrt_card_mul_l2Norm (ψ : AddChar R ℂ) (f : R → ℂ) (h : R) :
    ‖fourier ψ f h‖ ≤ Real.sqrt (Fintype.card R) * l2Norm f :=
  (norm_fourier_le_l1Mass ψ f h).trans (l1Mass_le_sqrt_card_mul_l2Norm f)

theorem norm_fourier_sq_le_card_mul_energy (ψ : AddChar R ℂ) (f : R → ℂ) (h : R) :
    ‖fourier ψ f h‖ ^ 2 ≤ (Fintype.card R : ℝ) * energy f := by
  have hn := norm_fourier_le_sqrt_card_mul_l2Norm ψ f h
  have hsq := sq_le_sq₀ (norm_nonneg (fourier ψ f h))
    (mul_nonneg (Real.sqrt_nonneg (Fintype.card R : ℝ)) (l2Norm_nonneg f))
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), l2Norm_sq] at hsq
  exact hsq.mpr hn

theorem l2Norm_fourier (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f : R → ℂ) :
    l2Norm (fourier ψ f) = Real.sqrt (Fintype.card R) * l2Norm f := by
  unfold l2Norm
  rw [energy_fourier ψ hψ, Real.sqrt_mul (Nat.cast_nonneg _)]

/-- A unit dilation preserves the actual energy, by changing residue variables. -/
theorem energy_dilate_unit (f : R → ℂ) (u : Rˣ) : energy (dilate (u : R) f) = energy f := by
  unfold energy dilate
  exact Fintype.sum_bijective _ u.mulLeft_bijective _ _ (fun _ => rfl)

theorem l1Mass_dilate_unit (f : R → ℂ) (u : Rˣ) : l1Mass (dilate (u : R) f) = l1Mass f := by
  unfold l1Mass dilate
  exact Fintype.sum_bijective _ u.mulLeft_bijective _ _ (fun _ => rfl)

theorem energy_divisorTransform (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f : R → ℂ) (d : R) :
    energy (divisorTransform ψ f d) =
      (Fintype.card R : ℝ) * energy (dilate d f) := energy_fourier ψ hψ _

/-- This bound keeps the full nonunit-divisor pullback in its mass. -/
theorem norm_divisorTransform_le_pullback_mass (ψ : AddChar R ℂ) (f : R → ℂ) (d h : R) :
    ‖divisorTransform ψ f d h‖ ≤ ∑ a : R, ‖f (d * a)‖ :=
  norm_fourier_le_l1Mass ψ (dilate d f) h

/-- Exact fibre decomposition, valid also for zero divisors and `d = 0`. -/
theorem energy_dilate_fibres (f : R → ℂ) (d : R) :
    energy (dilate d f) =
      ∑ b : R, (Finset.univ.filter (fun a : R => d * a = b)).card * ‖f b‖ ^ 2 := by
  unfold energy dilate
  calc
    (∑ a : R, ‖f (d * a)‖ ^ 2) =
        ∑ a : R, ∑ b : R, if d * a = b then ‖f b‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ b : R, ∑ a : R, if d * a = b then ‖f b‖ ^ 2 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_filter]
      simp

/-- Any actual fibre-cardinality bound gives the corresponding dilation bound. -/
theorem energy_dilate_le_fibre_bound (f : R → ℂ) (d : R) (B : ℝ)
    (hB : ∀ b : R, ((Finset.univ.filter (fun a : R => d * a = b)).card : ℝ) ≤ B) :
    energy (dilate d f) ≤ B * energy f := by
  rw [energy_dilate_fibres, energy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_right (hB b) (sq_nonneg _)

end HeckeGeneral.Arithmetic.PeriodicFourier
