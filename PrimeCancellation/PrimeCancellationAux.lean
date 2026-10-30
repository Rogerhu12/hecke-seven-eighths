import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-!
# Finite algebra for prime-slot cancellation

This file proves only finite-sum, sparse-mask, normalization, product, and
row-count transfer lemmas. It does not prove an analytic estimate for a Hecke
L-function. In particular, `hslot` below is explicitly an input, not an
abbreviation for a zero-free hypothesis.

The file is independent of the unavailable HeckeSkeleton project.
-/

open scoped BigOperators

namespace PrimeCancellationAux

variable {ι ρ : Type*}

/-- The exceptional row set must contain the inverse of each slot coefficient. -/
theorem mul_ne_one_of_not_mem {G : Type*} [Group G] (theta : Finset G)
    (row coeff : G) (hcoeff : coeff⁻¹ ∈ theta) (hrow : row ∉ theta) :
    row * coeff ≠ 1 := by
  intro h
  exact hrow ((eq_inv_of_mul_eq_one_left h).symm ▸ hcoeff)

/-- The Boolean mask used by a prime polynomial. -/
noncomputable def maskedSum (s : Finset ι) (f : ι → ℂ) (keep : ι → Bool) : ℂ :=
  ∑ i ∈ s, f i * (if keep i then 1 else 0)

/-- Deleting a Boolean mask is an exact subtraction of the deleted terms. -/
theorem maskedSum_eq_sub_deleted (s : Finset ι) (f : ι → ℂ) (keep : ι → Bool) :
    maskedSum s f keep =
      (∑ i ∈ s, f i) - ∑ i ∈ s.filter (fun i => keep i = false), f i := by
  classical
  rw [maskedSum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases keep i <;> simp

/-- A mask costs at most the number of deleted terms times their uniform norm. -/
theorem norm_maskedSum_le (s : Finset ι) (f : ι → ℂ) (keep : ι → Bool)
    (C : ℝ) (hf : ∀ i ∈ s, keep i = false → ‖f i‖ ≤ C) :
    ‖maskedSum s f keep‖ ≤
      ‖∑ i ∈ s, f i‖ + (s.filter (fun i => keep i = false)).card * C := by
  classical
  rw [maskedSum_eq_sub_deleted]
  refine (norm_sub_le _ _).trans (add_le_add (le_refl _) ?_)
  calc
    ‖∑ i ∈ s.filter (fun i => keep i = false), f i‖ ≤
        ∑ i ∈ s.filter (fun i => keep i = false), ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s.filter (fun i => keep i = false), C := by
      apply Finset.sum_le_sum
      intro i hi
      exact hf i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
    _ = _ := by simp

/-- The sparse-mask interface separates analytic cancellation from deletion. -/
theorem norm_maskedSum_le_of_card (s : Finset ι) (f : ι → ℂ) (keep : ι → Bool)
    (C D : ℝ) (hC : 0 ≤ C)
    (hf : ∀ i ∈ s, keep i = false → ‖f i‖ ≤ C)
    (hcard : ((s.filter (fun i => keep i = false)).card : ℝ) ≤ D) :
    ‖maskedSum s f keep‖ ≤ ‖∑ i ∈ s, f i‖ + D * C := by
  exact (norm_maskedSum_le s f keep C hf).trans
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcard hC))

/-- Square-root normalization contributes exactly one inverse power of P. -/
theorem norm_normalized_sq (P : ℝ) (hP : 0 < P) (S : ℂ) :
    ‖(Real.sqrt P : ℂ)⁻¹ * S‖ ^ 2 = ‖S‖ ^ 2 / P := by
  have hsqrt : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt,
    mul_pow, inv_pow, Real.sq_sqrt hP.le]
  ring

/-- A genuine prime-sum input with exponent β gives the normalized squared
exponent `2 * β - 1`. -/
theorem norm_normalized_sq_le_rpow (P β C : ℝ) (hP : 0 < P) (hC : 0 ≤ C)
    (S : ℂ) (hS : ‖S‖ ≤ C * P ^ β) :
    ‖(Real.sqrt P : ℂ)⁻¹ * S‖ ^ 2 ≤ C ^ 2 * P ^ (2 * β - 1) := by
  have hsq : ‖S‖ ^ 2 ≤ (C * P ^ β) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hS hS (norm_nonneg S) (mul_nonneg hC (Real.rpow_nonneg hP.le _))
  have hpow : (P ^ β) ^ 2 = P ^ (2 * β) := by
    simpa [mul_comm] using (Real.rpow_mul_natCast hP.le β 2).symm
  calc
    ‖(Real.sqrt P : ℂ)⁻¹ * S‖ ^ 2 = ‖S‖ ^ 2 / P := norm_normalized_sq P hP S
    _ ≤ (C * P ^ β) ^ 2 / P := div_le_div_of_nonneg_right hsq hP.le
    _ = C ^ 2 * P ^ (2 * β - 1) := by
      rw [mul_pow, hpow, Real.rpow_sub_one hP.ne']
      ring

/-- Finite multiplication of squared norm bounds. -/
theorem norm_product_sq_le (s : Finset ι) (Q : ι → ℂ) (B : ι → ℝ)
    (hslot : ∀ i ∈ s, ‖Q i‖ ^ 2 ≤ B i) :
    ‖∏ i ∈ s, Q i‖ ^ 2 ≤ ∏ i ∈ s, B i := by
  rw [norm_prod, ← Finset.prod_pow]
  exact Finset.prod_le_prod₀ (fun i _ => sq_nonneg ‖Q i‖) hslot

/-- Combining the slot exponents does not introduce a loss per row. -/
theorem norm_product_sq_le_rpow (s : Finset ι) (Q : ι → ℂ)
    (C ell loss : ι → ℝ) (Z κ : ℝ) (hZ : 0 < Z)
    (hslot : ∀ i ∈ s, ‖Q i‖ ^ 2 ≤ C i * Z ^ (κ * ell i + loss i)) :
    ‖∏ i ∈ s, Q i‖ ^ 2 ≤
      (∏ i ∈ s, C i) * Z ^ (κ * (∑ i ∈ s, ell i) + ∑ i ∈ s, loss i) := by
  calc
    ‖∏ i ∈ s, Q i‖ ^ 2 ≤ ∏ i ∈ s, C i * Z ^ (κ * ell i + loss i) :=
      norm_product_sq_le s Q _ hslot
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hZ,
        Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Only the total loss is relevant; no positive lower slot length is assumed. -/
theorem norm_product_sq_le_rpow_of_total_loss (s : Finset ι) (Q : ι → ℂ)
    (C ell loss : ι → ℝ) (Z κ ε : ℝ) (hZ : 1 ≤ Z)
    (hC : ∀ i ∈ s, 0 ≤ C i)
    (hslot : ∀ i ∈ s, ‖Q i‖ ^ 2 ≤ C i * Z ^ (κ * ell i + loss i))
    (hloss : (∑ i ∈ s, loss i) ≤ ε) :
    ‖∏ i ∈ s, Q i‖ ^ 2 ≤
      (∏ i ∈ s, C i) * Z ^ (κ * (∑ i ∈ s, ell i) + ε) := by
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  refine (norm_product_sq_le_rpow s Q C ell loss Z κ hZpos hslot).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact Real.rpow_le_rpow_of_exponent_le hZ (add_le_add (le_refl _) hloss)
  · exact Finset.prod_nonneg hC

/-- Summing a uniform per-row estimate introduces exactly the row-count factor. -/
theorem sum_sq_le_of_card (rows : Finset ρ) (F : ρ → ℂ)
    (Z Crow C e b : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hrows : (rows.card : ℝ) ≤ Crow * Z ^ e)
    (hrow : ∀ u ∈ rows, ‖F u‖ ^ 2 ≤ C * Z ^ b) :
    (∑ u ∈ rows, ‖F u‖ ^ 2) ≤ (Crow * C) * Z ^ (e + b) := by
  calc
    (∑ u ∈ rows, ‖F u‖ ^ 2) ≤ ∑ _u ∈ rows, C * Z ^ b :=
      Finset.sum_le_sum hrow
    _ = (rows.card : ℝ) * (C * Z ^ b) := by simp
    _ ≤ (Crow * Z ^ e) * (C * Z ^ b) :=
      mul_le_mul_of_nonneg_right hrows (mul_nonneg hC (Real.rpow_nonneg hZ.le _))
    _ = (Crow * C) * Z ^ (e + b) := by rw [Real.rpow_add hZ]; ring

/-- The finite-dimensional conclusion matching the paired prime moment exponent.

The nontrivial analytic input is the explicit hypothesis `hslot`.  This theorem
does not derive that input from zero-free regions.
-/
theorem paired_sum_le_of_slot_bounds (rows : Finset ρ) (slots : Finset ι)
    (Q : ρ → ι → ℂ) (C ell loss : ι → ℝ) (Z κ ε Crows e : ℝ)
    (hZ : 1 ≤ Z) (hC : ∀ i ∈ slots, 0 ≤ C i)
    (hrows : (rows.card : ℝ) ≤ Crows * Z ^ e)
    (hloss : (∑ i ∈ slots, loss i) ≤ ε)
    (hslot : ∀ u ∈ rows, ∀ i ∈ slots,
      ‖Q u i‖ ^ 2 ≤ C i * Z ^ (κ * ell i + loss i)) :
    (∑ u ∈ rows, ‖∏ i ∈ slots, Q u i‖ ^ 2) ≤
      (Crows * ∏ i ∈ slots, C i) *
        Z ^ (e + (κ * (∑ i ∈ slots, ell i) + ε)) := by
  apply sum_sq_le_of_card rows (fun u => ∏ i ∈ slots, Q u i)
    Z Crows (∏ i ∈ slots, C i) e (κ * (∑ i ∈ slots, ell i) + ε)
    (lt_of_lt_of_le zero_lt_one hZ) (Finset.prod_nonneg hC) hrows
  intro u hu
  exact norm_product_sq_le_rpow_of_total_loss slots (Q u) C ell loss Z κ ε
    hZ hC (hslot u hu) hloss

#print axioms mul_ne_one_of_not_mem
#print axioms maskedSum_eq_sub_deleted
#print axioms norm_maskedSum_le
#print axioms norm_maskedSum_le_of_card
#print axioms norm_normalized_sq
#print axioms norm_normalized_sq_le_rpow
#print axioms norm_product_sq_le
#print axioms norm_product_sq_le_rpow
#print axioms norm_product_sq_le_rpow_of_total_loss
#print axioms sum_sq_le_of_card
#print axioms paired_sum_le_of_slot_bounds

end PrimeCancellationAux
