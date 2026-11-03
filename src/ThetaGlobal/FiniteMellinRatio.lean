import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The same-vector Mellin normalization

Both transforms below retain the actual Fourier coefficient of the same
pure tensor at one.  The direct finite factor is its actual cutoff volume.
The two archimedean constants may differ, including the phase from the
chosen Weyl convention.  The normalization constant is therefore their
explicit ratio, rather than an unrelated nonzero complex number.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.FiniteMellinRatio

open scoped BigOperators

variable {I : Type*} [Fintype I]

theorem ofReal_prod_cpow {J : Type*} (t : Finset J) (a : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (s : ℂ) :
    ((∏ i ∈ t, a i : ℝ) : ℂ) ^ s = ∏ i ∈ t, (a i : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ha i) (Finset.prod_nonneg (fun j _ => ha j)),
      ih, Finset.prod_insert hi]

def normalization (finiteVolume directConstant reflectedConstant : ℂ) : ℂ :=
  finiteVolume * directConstant / reflectedConstant

theorem normalization_ne_zero
    {finiteVolume directConstant reflectedConstant : ℂ}
    (hv : finiteVolume ≠ 0) (hd : directConstant ≠ 0) (hr : reflectedConstant ≠ 0) :
    normalization finiteVolume directConstant reflectedConstant ≠ 0 :=
  div_ne_zero (mul_ne_zero hv hd) hr

/-- Cancellation of the same actual source scalar and the exact Haar and
local Mellin constants.  No nonvanishing of the gamma factors is needed
for this algebraic identity: division is the field's total division. -/
theorem same_vector_ratio
    (W finiteVolume directConstant reflectedConstant : ℂ)
    (hW : W ≠ 0) (hv : finiteVolume ≠ 0)
    (hd : directConstant ≠ 0) (hr : reflectedConstant ≠ 0)
    (A : ℝ) (hA : 0 < A) (s : ℂ) (finiteFactor : ℂ)
    (numerator denominator : I → ℂ) :
    (W * reflectedConstant * (A : ℂ) ^ s * finiteFactor * ∏ i, numerator i) /
      (W * finiteVolume * directConstant * (A : ℂ) ^ (-s) * ∏ i, denominator i) =
    (normalization finiteVolume directConstant reflectedConstant)⁻¹ *
      (A : ℂ) ^ (2 * s) * finiteFactor * ∏ i, numerator i / denominator i := by
  have hAc : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hAs : (A : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hAc]
    exact Complex.exp_ne_zero _
  rw [Finset.prod_div_distrib, Complex.cpow_neg, two_mul,
    Complex.cpow_add _ _ hAc]
  unfold normalization
  by_cases hg : (∏ i, denominator i) = 0
  · simp only [hg, mul_zero, div_zero, zero_mul]
  · field_simp [hW, hv, hd, hr, hAs, hg]
    <;> ring

/-- A form used when the local gamma pair is stored as two factors. -/
theorem product_pair_quotient
    (n₁ n₂ d₁ d₂ : I → ℂ) :
    (∏ i, (n₁ i * n₂ i) / (d₁ i * d₂ i)) =
      ∏ i, (n₁ i / d₁ i) * (n₂ i / d₂ i) := by
  apply Finset.prod_congr rfl
  intro i _
  exact mul_div_mul_comm _ _ _ _

end ThetaGlobal.FiniteMellinRatio

#print axioms ThetaGlobal.FiniteMellinRatio.same_vector_ratio
