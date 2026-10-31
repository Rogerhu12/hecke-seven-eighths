module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic

/-!
# Finite Schwartz sums on a sparse source

A proved height count of exponent δ ≤ 1 and cubic decay give a uniform
finite-sum bound at every coordinate scale 0 < α ≤ 1. The loss is α⁻δ.
The proof partitions the original finite source into integer shells;
it assumes neither an infinite orbital sum nor its convergence.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SparseFiniteSum

open scoped Classical BigOperators

def inverseSquareMass : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹

theorem inverseSquareMass_nonneg : 0 ≤ inverseSquareMass :=
  tsum_nonneg (fun _ => by positivity)

/-- A finite sparse source with a cubic weighted pointwise estimate.
All constants precede the source, and the scale is genuinely variable. -/
theorem finite_sum_le {ι : Type*} (s : Finset ι) (height f : ι → ℝ)
    (C Q δ α : ℝ) (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hheight : ∀ i ∈ s, 0 ≤ height i) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hpoint : ∀ i ∈ s, (1 + α * height i) ^ 3 * f i ≤ Q)
    (hcount : ∀ H : ℝ, 1 ≤ H → ∀ t : Finset ι, t ⊆ s →
      (∀ i ∈ t, height i ≤ H) → (t.card : ℝ) ≤ C * H ^ δ) :
    (∑ i ∈ s, f i) ≤ 2 * C * Q * α ^ (-δ) * inverseSquareMass := by
  let k : ι → ℕ := fun i => ⌊1 + α * height i⌋₊
  have hkpos (i : ι) (hi : i ∈ s) : 1 ≤ k i := by
    apply Nat.le_floor
    norm_num
    exact mul_nonneg hα.le (hheight i hi)
  have hshell (n : ℕ) (hn : n ∈ s.image k) :
      (∑ i ∈ s with k i = n, f i) ≤
        (2 * C * Q * α ^ (-δ)) * ((n : ℝ) ^ 2)⁻¹ := by
    obtain ⟨i₀, hi₀, hi₀n⟩ := Finset.mem_image.mp hn
    have hn1 : 1 ≤ n := hi₀n ▸ hkpos i₀ hi₀
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
    let t := s.filter (fun i => k i = n)
    have ht (i : ι) (hi : i ∈ t) : i ∈ s := (Finset.mem_filter.mp hi).1
    have ht_height (i : ι) (hi : i ∈ t) : height i ≤ ((n : ℝ) + 1) / α := by
      have hu := Nat.lt_floor_add_one (1 + α * height i)
      change 1 + α * height i < (k i : ℝ) + 1 at hu
      rw [(Finset.mem_filter.mp hi).2] at hu
      apply (le_div_iff₀ hα).mpr
      nlinarith
    have hH : 1 ≤ ((n : ℝ) + 1) / α := by
      apply (le_div_iff₀ hα).mpr
      nlinarith
    have htcard := hcount (((n : ℝ) + 1) / α) hH t
      (fun i hi => ht i hi) ht_height
    have htpoint (i : ι) (hi : i ∈ t) : f i ≤ Q / (n : ℝ) ^ 3 := by
      have hnle := Nat.floor_le (show 0 ≤ 1 + α * height i by
        exact add_nonneg zero_le_one (mul_nonneg hα.le (hheight i (ht i hi))))
      change (k i : ℝ) ≤ 1 + α * height i at hnle
      rw [(Finset.mem_filter.mp hi).2] at hnle
      apply (le_div_iff₀ (pow_pos hnpos 3)).mpr
      calc
        _ = (n : ℝ) ^ 3 * f i := mul_comm _ _
        _ ≤ (1 + α * height i) ^ 3 * f i :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnpos.le hnle 3) (hf i (ht i hi))
        _ ≤ Q := hpoint i (ht i hi)
    have hpow : (((n : ℝ) + 1) / α) ^ δ ≤ 2 * (n : ℝ) * α ^ (-δ) := by
      rw [Real.div_rpow (by positivity) hα.le,
        div_eq_mul_inv, ← Real.rpow_neg hα.le]
      have hp : ((n : ℝ) + 1) ^ δ ≤ (n : ℝ) + 1 := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1) hδ1
      exact mul_le_mul_of_nonneg_right (hp.trans (by linarith))
        (Real.rpow_nonneg hα.le _)
    change (∑ i ∈ t, f i) ≤ _
    calc
      _ ≤ ∑ _i ∈ t, Q / (n : ℝ) ^ 3 := Finset.sum_le_sum htpoint
      _ = (t.card : ℝ) * (Q / (n : ℝ) ^ 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C * (((n : ℝ) + 1) / α) ^ δ) * (Q / (n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right htcard (div_nonneg hQ (pow_nonneg hnpos.le _))
      _ ≤ (C * (2 * (n : ℝ) * α ^ (-δ))) * (Q / (n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC)
          (div_nonneg hQ (pow_nonneg hnpos.le _))
      _ = _ := by field_simp; ring
  have hfactor : 0 ≤ 2 * C * Q * α ^ (-δ) := by positivity
  have hmass := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).sum_le_tsum
    (s.image k) (fun _ _ => by positivity)
  calc
    _ = ∑ n ∈ s.image k, ∑ i ∈ s with k i = n, f i :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem k hi) f).symm
    _ ≤ ∑ n ∈ s.image k, (2 * C * Q * α ^ (-δ)) * ((n : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum hshell
    _ = (2 * C * Q * α ^ (-δ)) * ∑ n ∈ s.image k, ((n : ℝ) ^ 2)⁻¹ :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass hfactor

end HeckeSkeleton.Moments.MOM_INV_STEP.SparseFiniteSum

end
