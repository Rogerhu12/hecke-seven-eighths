import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform finite harmonic bounds from a convergent Dirichlet majorant

This file supplies the small-power absorption used by the weighted hybrid
normal form. The constants are chosen before finite supports and scales.
The number-field majorant is constructed, rather than assumed, in
`IdealMass.lean`.
-/

namespace HeckeSkeleton.LowEnergy

open scoped BigOperators
noncomputable section

/-- A convergent Dirichlet majorant controls every finite harmonic sum.
Only the selected elements have to have positive norm. -/
theorem reciprocal_sum_le_rpow_tsum {ι : Type*}
    (normI : ι → ℝ) (delta X : ℝ) (hdelta : 0 ≤ delta) (hX : 0 ≤ X)
    (hN : ∀ i, 0 ≤ normI i)
    (hsum : Summable (fun i => normI i ^ (-1 - delta)))
    (s : Finset ι) (hpos : ∀ i ∈ s, 0 < normI i)
    (hcut : ∀ i ∈ s, normI i ≤ X) :
    (∑ i ∈ s, 1 / normI i) ≤
      (∑' i, normI i ^ (-1 - delta)) * X ^ delta := by
  have hterm (i : ι) (hi : i ∈ s) :
      1 / normI i = normI i ^ (-1 - delta) * normI i ^ delta := by
    rw [← Real.rpow_add (hpos i hi)]
    norm_num [Real.rpow_neg_one]
  calc
    _ = ∑ i ∈ s, normI i ^ (-1 - delta) * normI i ^ delta :=
      Finset.sum_congr rfl hterm
    _ ≤ ∑ i ∈ s, normI i ^ (-1 - delta) * X ^ delta := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hN i) (hcut i hi) hdelta)
        (Real.rpow_nonneg (hN i) _)
    _ = (∑ i ∈ s, normI i ^ (-1 - delta)) * X ^ delta :=
      (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (hsum.sum_le_tsum s (fun i _ => Real.rpow_nonneg (hN i) _))
      (Real.rpow_nonneg hX _)

/-- Version with the ambient nonnegative scale made explicit. -/
theorem reciprocal_sum_le_majorant {ι : Type*}
    (normI : ι → ℝ) (delta X C : ℝ) (hdelta : 0 ≤ delta)
    (hX : 0 ≤ X) (hN : ∀ i, 0 ≤ normI i)
    (hsum : Summable (fun i => normI i ^ (-1 - delta)))
    (hC : (∑' i, normI i ^ (-1 - delta)) ≤ C)
    (s : Finset ι) (hpos : ∀ i ∈ s, 0 < normI i)
    (hcut : ∀ i ∈ s, normI i ≤ X) :
    (∑ i ∈ s, 1 / normI i) ≤ C * X ^ delta := by
  exact (reciprocal_sum_le_rpow_tsum normI delta X hdelta hX hN hsum s hpos hcut).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hX _))

/-- Arbitrarily small powers follow uniformly from absolute convergence to
the right of the line of degree one. -/
theorem reciprocal_sum_small_power {ι : Type*}
    (normI : ι → ℝ) (hN : ∀ i, 0 ≤ normI i)
    (hsum : ∀ delta : ℝ, 0 < delta →
      Summable (fun i => normI i ^ (-1 - delta)))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ s : Finset ι, (∀ i ∈ s, 0 < normI i) →
        (∀ i ∈ s, normI i ≤ X) →
        (∑ i ∈ s, 1 / normI i) ≤ C * X ^ eps := by
  let C : ℝ := max 1 (∑' i, normI i ^ (-1 - eps))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro X hX s hpos hcut
  exact reciprocal_sum_le_majorant normI eps X C heps.le (zero_le_one.trans hX)
    hN (hsum eps heps) (le_max_right _ _) s hpos hcut

/-- Products keep the product of the *actual* cutoffs. This avoids replacing
several independent scales by their largest value. -/
theorem harmonic_product_le {ι σ : Type*} [Fintype σ]
    (normI : ι → ℝ) (delta C : ℝ) (hdelta : 0 ≤ delta)
    (hC : 0 ≤ C) (hN : ∀ i, 0 ≤ normI i)
    (hsum : Summable (fun i => normI i ^ (-1 - delta)))
    (hmajorant : (∑' i, normI i ^ (-1 - delta)) ≤ C)
    (sets : σ → Finset ι) (X : σ → ℝ)
    (hX : ∀ j, 0 ≤ X j)
    (hpos : ∀ j i, i ∈ sets j → 0 < normI i)
    (hcut : ∀ j i, i ∈ sets j → normI i ≤ X j) :
    (∏ j, ∑ i ∈ sets j, 1 / normI i) ≤
      C ^ Fintype.card σ * (∏ j, X j) ^ delta := by
  classical
  have hprod :
      (∏ j, ∑ i ∈ sets j, 1 / normI i) ≤ ∏ j, C * (X j) ^ delta := by
    apply Finset.prod_le_prod₀
    · intro j _
      exact Finset.sum_nonneg (fun i hi => (one_div_pos.mpr (hpos j i hi)).le)
    · intro j _
      exact reciprocal_sum_le_majorant normI delta (X j) C hdelta (hX j)
        hN hsum hmajorant (sets j) (hpos j) (hcut j)
  apply hprod.trans_eq
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Real.finsetProd_rpow Finset.univ X (fun j _ => hX j)]

/-- A bounded number of harmonic masses, including repeated masses, can be
absorbed into an arbitrary prescribed small power of their common cutoff.
The constant precedes the index type, supports and cutoff in the quantifiers. -/
theorem bounded_harmonic_product_small_power {ι : Type*}
    (normI : ι → ℝ) (hN : ∀ i, 0 ≤ normI i)
    (hsum : ∀ delta : ℝ, 0 < delta →
      Summable (fun i => normI i ^ (-1 - delta)))
    (rmax : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {σ : Type*} [Fintype σ],
      Fintype.card σ ≤ rmax → ∀ X : ℝ, 1 ≤ X →
      ∀ sets : σ → Finset ι,
      (∀ j i, i ∈ sets j → 0 < normI i) →
      (∀ j i, i ∈ sets j → normI i ≤ X) →
      (∏ j, ∑ i ∈ sets j, 1 / normI i) ≤ C * X ^ eps := by
  classical
  let delta : ℝ := eps / (rmax + 1)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  let D : ℝ := max 1 (∑' i, normI i ^ (-1 - delta))
  have hD : 1 ≤ D := le_max_left _ _
  refine ⟨D ^ rmax, one_le_pow₀ hD, ?_⟩
  intro σ _ hcard X hX sets hpos hcut
  have hb := harmonic_product_le normI delta D hdelta.le (zero_le_one.trans hD) hN
    (hsum delta hdelta) (le_max_right _ _) sets (fun _ => X)
    (fun _ => zero_le_one.trans hX) hpos hcut
  have hpow : (X ^ Fintype.card σ) ^ delta = X ^ ((Fintype.card σ : ℝ) * delta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hX)]
  have hdegree : (Fintype.card σ : ℝ) * delta ≤ eps := by
    have hc : (Fintype.card σ : ℝ) ≤ rmax := by exact_mod_cast hcard
    have hden : (rmax : ℝ) + 1 ≠ 0 := by positivity
    have heq : ((rmax : ℝ) + 1) * delta = eps := by
      dsimp [delta]
      field_simp
    nlinarith
  simp only [Finset.prod_const, Finset.card_univ] at hb
  rw [hpow] at hb
  exact hb.trans (mul_le_mul
    (pow_le_pow_right₀ hD hcard)
    (Real.rpow_le_rpow_of_exponent_le hX hdegree)
    (Real.rpow_nonneg (zero_le_one.trans hX) _)
    (pow_nonneg (zero_le_one.trans hD) _))

/-- The squared Minkowski cost of finitely many inactive-slot harmonic
masses. No disjointness assumption is needed for this positive estimate. -/
theorem squared_harmonic_product_small_power {ι : Type*}
    (normI : ι → ℝ) (hN : ∀ i, 0 ≤ normI i)
    (hsum : ∀ delta : ℝ, 0 < delta →
      Summable (fun i => normI i ^ (-1 - delta)))
    (rmax : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {σ : Type*} [Fintype σ],
      Fintype.card σ ≤ rmax → ∀ X : ℝ, 1 ≤ X →
      ∀ sets : σ → Finset ι,
      (∀ j i, i ∈ sets j → 0 < normI i) →
      (∀ j i, i ∈ sets j → normI i ≤ X) →
      (∏ j, ∑ i ∈ sets j, 1 / normI i) ^ 2 ≤ C * X ^ eps := by
  obtain ⟨C, hC, hb⟩ := bounded_harmonic_product_small_power normI hN hsum
    rmax (eps / 2) (by positivity)
  refine ⟨C ^ 2, one_le_pow₀ hC, ?_⟩
  intro σ _ hcard X hX sets hpos hcut
  have hproduct : 0 ≤ ∏ j, ∑ i ∈ sets j, 1 / normI i := by
    exact Finset.prod_nonneg (fun j _ => Finset.sum_nonneg
      (fun i hi => (one_div_pos.mpr (hpos j i hi)).le))
  calc
    _ ≤ (C * X ^ (eps / 2)) ^ 2 :=
      pow_le_pow_left₀ hproduct (hb hcard X hX sets hpos hcut) _
    _ = C ^ 2 * X ^ eps := by
      rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hX)]
      congr 1
      congr 1
      norm_num

#print axioms reciprocal_sum_le_rpow_tsum
#print axioms reciprocal_sum_small_power
#print axioms harmonic_product_le
#print axioms bounded_harmonic_product_small_power
#print axioms squared_harmonic_product_small_power

end
end HeckeSkeleton.LowEnergy
