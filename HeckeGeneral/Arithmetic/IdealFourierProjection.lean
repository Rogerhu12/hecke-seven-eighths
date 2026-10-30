import HeckeGeneral.Arithmetic.IdealFourierOrthogonality
import HeckeGeneral.Arithmetic.FiniteFourierProducts

/-!
# An ideal mask is an exact dual averaging projection

Multiplication by actual ideal membership is conjugated by Fourier to
averaging over the corresponding annihilator coset. The normalization
comes from the ideal/annihilator cardinality identity. Idempotence and
the energy bound are proved from the actual mask operator.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.IdealFourierOrthogonality

open PeriodicFourier IdealMobiusMask
open scoped BigOperators Classical

variable {R : Type*} [CommRing R] [Fintype R]

def idealMask (I : Ideal R) (f : R → ℂ) (a : R) : ℂ := f a * membershipIndicator I a

def dualIdealAverage (I : Ideal R) (g : R → ℂ) (h : R) : ℂ :=
  (idealCard (annihilatorIdeal I) : ℂ)⁻¹ * ∑ k : R,
    if h - k ∈ annihilatorIdeal I then g k else 0

omit [Fintype R] in
theorem indicator_idempotent (I : Ideal R) (a : R) :
    membershipIndicator I a * membershipIndicator I a = membershipIndicator I a := by
  unfold membershipIndicator
  split_ifs <;> norm_num

omit [Fintype R] in
theorem idealMask_idempotent (I : Ideal R) (f : R → ℂ) :
    idealMask I (idealMask I f) = idealMask I f := by
  funext a
  simp only [idealMask, mul_assoc, indicator_idempotent]

omit [Fintype R] in
theorem idealMask_add (I : Ideal R) (f g : R → ℂ) :
    idealMask I (fun a => f a + g a) = fun a => idealMask I f a + idealMask I g a := by
  funext a
  exact add_mul _ _ _

omit [Fintype R] in
theorem idealMask_const_mul (I : Ideal R) (f : R → ℂ) (c : ℂ) :
    idealMask I (fun a => c * f a) = fun a => c * idealMask I f a := by
  funext a
  exact mul_assoc _ _ _

omit [Fintype R] in
theorem norm_idealMask_le (I : Ideal R) (f : R → ℂ) (a : R) :
    ‖idealMask I f a‖ ≤ ‖f a‖ := by
  unfold idealMask membershipIndicator
  split_ifs <;> simp

theorem energy_idealMask_le (I : Ideal R) (f : R → ℂ) :
    energy (idealMask I f) ≤ energy f := by
  apply Finset.sum_le_sum
  intro a _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_idealMask_le I f a)

theorem l1Mass_idealMask_le (I : Ideal R) (f : R → ℂ) :
    l1Mass (idealMask I f) ≤ l1Mass f :=
  Finset.sum_le_sum (fun a _ => norm_idealMask_le I f a)

theorem ideal_normalization (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (I : Ideal R) :
    (Fintype.card R : ℂ)⁻¹ * (idealCard I : ℂ) =
      (idealCard (annihilatorIdeal I) : ℂ)⁻¹ := by
  have h := idealCard_mul_annihilator_nat ψ hψ I
  have hc : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hi : (idealCard I : ℂ) ≠ 0 := by exact_mod_cast (idealCard_pos I).ne'
  have ha : (idealCard (annihilatorIdeal I) : ℂ) ≠ 0 := by
    exact_mod_cast (idealCard_pos (annihilatorIdeal I)).ne'
  have hcast : (idealCard I : ℂ) * idealCard (annihilatorIdeal I) = Fintype.card R := by
    exact_mod_cast h
  field_simp
  exact hcast

theorem fourier_idealMask (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (I : Ideal R) (f : R → ℂ) (h : R) :
    fourier ψ (idealMask I f) h = dualIdealAverage I (fourier ψ f) h := by
  unfold idealMask dualIdealAverage
  rw [fourier_product ψ hψ]
  unfold convolution
  simp_rw [fourier_indicator ψ hψ, mul_ite, mul_zero]
  have hs : (∑ a : R, if h - a ∈ annihilatorIdeal I then
      fourier ψ f a * (idealCard I : ℂ) else 0) =
      (idealCard I : ℂ) * ∑ a : R, if h - a ∈ annihilatorIdeal I then fourier ψ f a else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp [mul_comm]
  rw [hs, ← mul_assoc, ideal_normalization ψ hψ I]

theorem fourier_idealMask_zero (ψ : AddChar R ℂ) (I : Ideal R) (f : R → ℂ) :
    fourier ψ (idealMask I f) 0 = ∑ a : I, f a.val := by
  rw [fourier_zero]
  exact sum_membershipIndicator I f

theorem dualIdealAverage_idempotent (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (I : Ideal R) (g : R → ℂ) : dualIdealAverage I (dualIdealAverage I g) = dualIdealAverage I g := by
  obtain ⟨f, rfl⟩ := fourier_surjective ψ hψ g
  have hf (f : R → ℂ) : fourier ψ (idealMask I f) = dualIdealAverage I (fourier ψ f) := by
    funext h
    exact fourier_idealMask ψ hψ I f h
  rw [← hf, ← hf, idealMask_idempotent]

theorem energy_dualIdealAverage_le (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (I : Ideal R) (g : R → ℂ) : energy (dualIdealAverage I g) ≤ energy g := by
  obtain ⟨f, rfl⟩ := fourier_surjective ψ hψ g
  have hf : dualIdealAverage I (fourier ψ f) = fourier ψ (idealMask I f) := by
    funext h
    exact (fourier_idealMask ψ hψ I f h).symm
  rw [hf, energy_fourier ψ hψ, energy_fourier ψ hψ]
  exact mul_le_mul_of_nonneg_left (energy_idealMask_le I f) (Nat.cast_nonneg _)

end HeckeGeneral.Arithmetic.IdealFourierOrthogonality
