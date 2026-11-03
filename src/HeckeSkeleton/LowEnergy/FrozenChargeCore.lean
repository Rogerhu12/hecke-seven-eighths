import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

/-! Exact finite products for the minimum-exponent charges. -/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.FrozenChargeCore

open scoped BigOperators Classical

def localMajorant (q : ℝ) (j m : ℕ) : ℝ :=
  if m = 0 then
    if j = 0 ∨ j = 4 then (Real.sqrt q)⁻¹ else 1
  else if j = 4 then
    if m = 1 then 1 else if m = 3 then (Real.sqrt q)⁻¹ else 0
  else 0

def smallCharge (j m : ℕ) : Prop := m = 0 ∧ (j = 0 ∨ j = 4)

theorem localMajorant_nonneg (q : ℝ) (j m : ℕ) : 0 ≤ localMajorant q j m := by
  unfold localMajorant
  split_ifs <;> positivity

theorem localMajorant_sq_le (q : ℝ) (j m : ℕ) (hq : 0 < q)
    (hm : m = 0 ∨ m = 1 ∨ m = 3) :
    localMajorant q j m ^ 2 ≤
      (if smallCharge j m then q⁻¹ else 1) * (if m = 3 then q⁻¹ else 1) := by
  rcases hm with rfl | rfl | rfl
  · by_cases hj : j = 0 ∨ j = 4
    · simp [localMajorant, smallCharge, hj, inv_pow, Real.sq_sqrt hq.le]
    · simp [localMajorant, smallCharge, hj]
  · by_cases hj : j = 4 <;> simp [localMajorant, smallCharge, hj]
  · by_cases hj : j = 4
    · simp [localMajorant, smallCharge, hj, inv_pow, Real.sq_sqrt hq.le]
    · simpa [localMajorant, smallCharge, hj] using (inv_nonneg.mpr hq.le)

variable {ι : Type*}

def linearPrimes (T : Finset ι) (m : ι → ℕ) : Finset ι := T.filter (fun p => m p = 1)

def cubePrimes (T : Finset ι) (m : ι → ℕ) : Finset ι := T.filter (fun p => m p = 3)

def smallPrimes (T : Finset ι) (j m : ι → ℕ) : Finset ι :=
  T.filter (fun p => smallCharge (j p) (m p))

theorem minimum_norm_identity (T : Finset ι) (q : ι → ℝ) (m : ι → ℕ)
    (hm : ∀ p ∈ T, m p = 0 ∨ m p = 1 ∨ m p = 3) :
    (∏ p ∈ T, q p ^ m p) =
      (∏ p ∈ linearPrimes T m, q p) * (∏ p ∈ cubePrimes T m, q p) ^ 3 := by
  unfold linearPrimes cubePrimes
  rw [Finset.prod_filter, Finset.prod_filter, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rcases hm p hp with h | h | h <;> simp [h]

theorem linear_norm_le_active (T : Finset ι) (q : ι → ℝ) (m : ι → ℕ)
    (hq : ∀ p ∈ T, 1 ≤ q p) :
    (∏ p ∈ linearPrimes T m, q p) ≤ ∏ p ∈ T, q p := by
  unfold linearPrimes
  rw [Finset.prod_filter]
  apply Finset.prod_le_prod₀
  · intro p hp
    split_ifs <;> linarith [hq p hp]
  · intro p hp
    split_ifs
    · exact le_rfl
    · exact hq p hp

theorem frozen_majorant_square_le (T : Finset ι) (q : ι → ℝ) (j m : ι → ℕ)
    (hq : ∀ p ∈ T, 0 < q p)
    (hm : ∀ p ∈ T, m p = 0 ∨ m p = 1 ∨ m p = 3) :
    (∏ p ∈ T, localMajorant (q p) (j p) (m p)) ^ 2 ≤
      ((∏ p ∈ smallPrimes T j m, q p) * (∏ p ∈ cubePrimes T m, q p))⁻¹ := by
  calc
    _ = ∏ p ∈ T, localMajorant (q p) (j p) (m p) ^ 2 :=
      (Finset.prod_pow T 2 _).symm
    _ ≤ ∏ p ∈ T, (if smallCharge (j p) (m p) then (q p)⁻¹ else 1) *
        (if m p = 3 then (q p)⁻¹ else 1) := by
      apply Finset.prod_le_prod₀
      · intro p _
        exact sq_nonneg _
      · intro p hp
        exact localMajorant_sq_le _ _ _ (hq p hp) (hm p hp)
    _ = (∏ p ∈ smallPrimes T j m, (q p)⁻¹) *
        (∏ p ∈ cubePrimes T m, (q p)⁻¹) := by
      rw [Finset.prod_mul_distrib]
      simp only [smallPrimes, cubePrimes, Finset.prod_filter]
    _ = _ := by rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib, mul_inv_rev, mul_comm]

#print axioms minimum_norm_identity
#print axioms linear_norm_le_active
#print axioms frozen_majorant_square_le

end HeckeSkeleton.LowEnergy.FrozenChargeCore
