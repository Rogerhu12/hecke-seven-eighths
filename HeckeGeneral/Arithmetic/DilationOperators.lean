import HeckeGeneral.Arithmetic.FiniteFourierBounds
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

/-!
# Actual multiplication fibres and dilation operator bounds

Every nonempty fibre of multiplication by `d` is an additive translate of
its kernel. The resulting exact multiplicity controls mass and energy of
the nonunit divisor pullback in the masked Poisson formula. The unit case
is a proved specialization, while zero divisors retain their multiplicity.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.PeriodicFourier

open scoped BigOperators Classical

variable {R : Type*} [CommRing R] [Fintype R]

abbrev DilationFibre (d b : R) := {a : R // d * a = b}

def fibreCard (d b : R) : ℕ := (Finset.univ.filter (fun a : R => d * a = b)).card

theorem fibreCard_eq_card (d b : R) : fibreCard d b = Fintype.card (DilationFibre d b) :=
  (Fintype.card_subtype (fun a : R => d * a = b)).symm

/-- Translation by a chosen actual fibre point identifies the fibre with the kernel. -/
def dilationFibreEquivKernel (d b a₀ : R) (ha₀ : d * a₀ = b) :
    DilationFibre d b ≃ DilationFibre d 0 where
  toFun a := ⟨a.val - a₀, by rw [mul_sub, a.property, ha₀, sub_self]⟩
  invFun a := ⟨a.val + a₀, by rw [mul_add, a.property, ha₀, zero_add]⟩
  left_inv a := Subtype.ext (sub_add_cancel a.val a₀)
  right_inv a := Subtype.ext (add_sub_cancel_right a.val a₀)

theorem fibreCard_eq_kernel_of_exists (d b : R) (hb : ∃ a : R, d * a = b) :
    fibreCard d b = fibreCard d 0 := by
  obtain ⟨a₀, ha₀⟩ := hb
  rw [fibreCard_eq_card, fibreCard_eq_card]
  exact Fintype.card_congr (dilationFibreEquivKernel d b a₀ ha₀)

theorem fibreCard_eq_zero_of_not_exists (d b : R) (hb : ¬ ∃ a : R, d * a = b) :
    fibreCard d b = 0 := by
  unfold fibreCard
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact hb ⟨a, (Finset.mem_filter.mp ha).2⟩

/-- A fibre is either empty or has exactly the kernel's cardinality. -/
theorem fibreCard_eq_ite (d b : R) :
    fibreCard d b = if ∃ a : R, d * a = b then fibreCard d 0 else 0 := by
  split_ifs with hb
  · exact fibreCard_eq_kernel_of_exists d b hb
  · exact fibreCard_eq_zero_of_not_exists d b hb

theorem fibreCard_le_kernel (d b : R) : fibreCard d b ≤ fibreCard d 0 := by
  rw [fibreCard_eq_ite]
  split_ifs <;> omega

theorem one_le_kernelCard (d : R) : 1 ≤ fibreCard d 0 := by
  apply Finset.one_le_card.mpr
  exact ⟨0, by simp⟩

theorem kernelCard_unit (u : Rˣ) : fibreCard (u : R) 0 = 1 := by
  unfold fibreCard
  have hfilter : Finset.univ.filter (fun a : R => (u : R) * a = 0) = {0} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact u.mulLeft_bijective.injective (h.trans (mul_zero (u : R)).symm)
    · intro h
      simp [h]
  rw [hfilter]
  simp

theorem fibreCard_unit (u : Rˣ) (b : R) : fibreCard (u : R) b = 1 := by
  rw [fibreCard_eq_kernel_of_exists _ _
    ⟨(u⁻¹ : Rˣ) * b, by simp⟩, kernelCard_unit]

theorem energy_dilate_le_kernelCard (f : R → ℂ) (d : R) :
    energy (dilate d f) ≤ (fibreCard d 0 : ℝ) * energy f :=
  energy_dilate_le_fibre_bound f d _ (fun b => Nat.cast_le.mpr (fibreCard_le_kernel d b))

/-- The L1 pullback also retains the exact fibre multiplicity. -/
theorem l1Mass_dilate_fibres (f : R → ℂ) (d : R) :
    l1Mass (dilate d f) = ∑ b : R, (fibreCard d b : ℝ) * ‖f b‖ := by
  unfold l1Mass dilate
  calc
    (∑ a : R, ‖f (d * a)‖) =
        ∑ a : R, ∑ b : R, if d * a = b then ‖f b‖ else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ b : R, ∑ a : R, if d * a = b then ‖f b‖ else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_filter]
      simp [fibreCard]

theorem l1Mass_dilate_le_kernelCard (f : R → ℂ) (d : R) :
    l1Mass (dilate d f) ≤ (fibreCard d 0 : ℝ) * l1Mass f := by
  rw [l1Mass_dilate_fibres, l1Mass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (fibreCard_le_kernel d b)) (norm_nonneg _)

/-- Pointwise dual bounds use the actual multiplication kernel. -/
theorem norm_divisorTransform_le_kernelCard_mass (ψ : AddChar R ℂ)
    (f : R → ℂ) (d h : R) :
    ‖divisorTransform ψ f d h‖ ≤ (fibreCard d 0 : ℝ) * l1Mass f :=
  (norm_fourier_le_l1Mass ψ (dilate d f) h).trans (l1Mass_dilate_le_kernelCard f d)

theorem energy_divisorTransform_le_kernelCard (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f : R → ℂ) (d : R) :
    energy (divisorTransform ψ f d) ≤
      (Fintype.card R : ℝ) * (fibreCard d 0 : ℝ) * energy f := by
  rw [energy_divisorTransform ψ hψ]
  exact (mul_le_mul_of_nonneg_left (energy_dilate_le_kernelCard f d)
    (Nat.cast_nonneg _)).trans_eq (mul_assoc _ _ _).symm

/-- This is a concrete squared L2-to-pointwise bound, including nonunit divisors. -/
theorem norm_divisorTransform_sq_le_kernelCard_energy (ψ : AddChar R ℂ)
    (f : R → ℂ) (d h : R) :
    ‖divisorTransform ψ f d h‖ ^ 2 ≤
      (Fintype.card R : ℝ) * (fibreCard d 0 : ℝ) * energy f := by
  exact (norm_fourier_sq_le_card_mul_energy ψ (dilate d f) h).trans
    ((mul_le_mul_of_nonneg_left (energy_dilate_le_kernelCard f d)
      (Nat.cast_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

/-- Pushforward of a finite sum counts each actual multiplication fibre. -/
theorem sum_dilate_fibres (f : R → ℂ) (d : R) :
    (∑ a : R, f (d * a)) = ∑ b : R, (fibreCard d b : ℂ) * f b := by
  calc
    (∑ a : R, f (d * a)) =
        ∑ a : R, ∑ b : R, if d * a = b then f b else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ b : R, ∑ a : R, if d * a = b then f b else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_filter]
      simp [fibreCard]

theorem sum_dilate_eq_kernelCard_mul_image_sum (f : R → ℂ) (d : R) :
    (∑ a : R, f (d * a)) = (fibreCard d 0 : ℂ) *
      ∑ b : R, if ∃ a : R, d * a = b then f b else 0 := by
  rw [sum_dilate_fibres, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [fibreCard_eq_ite]
  split_ifs <;> simp

theorem kernelCard_complex_ne_zero (d : R) : (fibreCard d 0 : ℂ) ≠ 0 := by
  exact_mod_cast Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one (one_le_kernelCard d))

/-- This exact image-sum identity is the finite change-of-variables rule for
a nonunit divisor. The kernel factor must not be silently dropped. -/
theorem image_sum_eq_inverse_kernelCard_mul (f : R → ℂ) (d : R) :
    (∑ b : R, if ∃ a : R, d * a = b then f b else 0) =
      (fibreCard d 0 : ℂ)⁻¹ * ∑ a : R, f (d * a) := by
  rw [sum_dilate_eq_kernelCard_mul_image_sum, ← mul_assoc,
    inv_mul_cancel₀ (kernelCard_complex_ne_zero d), one_mul]

theorem fourier_image_mask (ψ : AddChar R ℂ) (f : R → ℂ) (d h : R) :
    fourier ψ (fun a => if ∃ b : R, d * b = a then f a else 0) h =
      (fibreCard d 0 : ℂ)⁻¹ * fourier ψ (dilate d f) (d * h) := by
  unfold fourier
  have hmask : (∑ a : R, (if ∃ b : R, d * b = a then f a else 0) * ψ (h * a)) =
      ∑ a : R, if ∃ b : R, d * b = a then f a * ψ (h * a) else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [hmask, image_sum_eq_inverse_kernelCard_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  unfold dilate
  congr 1
  congr 1
  ring

end HeckeGeneral.Arithmetic.PeriodicFourier
