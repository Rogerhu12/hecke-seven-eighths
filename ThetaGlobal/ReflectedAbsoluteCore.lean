import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A coarse absolute-convergence theorem for marked reflected theta sums

This module uses only Mathlib.  A fixed reflected row needs no sharp Euler
majorant: bounded arithmetic coefficients and a quadratic tail for the
kernel suffice, after enlarging the frozen numerator to all integral ideals.
The three ideal variables are kept distinct.  All hypotheses are elementary
local bounds, a kernel bound, or a positive Dirichlet-series majorant; the
conclusion is not among the hypotheses.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedAbsolute

open scoped BigOperators

/-- Zero-extended unitary values remain bounded after taking inverse powers.
The assertion `‖z‖ ≤ 1` alone would not justify this step. -/
def ZeroOrUnitNorm (z : ℂ) : Prop := z = 0 ∨ ‖z‖ = 1

theorem ZeroOrUnitNorm.norm_le {z : ℂ} (hz : ZeroOrUnitNorm z) : ‖z‖ ≤ 1 := by
  rcases hz with rfl | hz
  · simp
  · exact hz.le

theorem ZeroOrUnitNorm.one : ZeroOrUnitNorm (1 : ℂ) := Or.inr (by simp)

theorem ZeroOrUnitNorm.zero : ZeroOrUnitNorm (0 : ℂ) := Or.inl rfl

theorem ZeroOrUnitNorm.mul {z w : ℂ} (hz : ZeroOrUnitNorm z)
    (hw : ZeroOrUnitNorm w) : ZeroOrUnitNorm (z * w) := by
  rcases hz with rfl | hz
  · simp [ZeroOrUnitNorm]
  rcases hw with rfl | hw
  · simp [ZeroOrUnitNorm]
  · exact Or.inr (by rw [norm_mul, hz, hw, one_mul])

theorem ZeroOrUnitNorm.inv {z : ℂ} (hz : ZeroOrUnitNorm z) :
    ZeroOrUnitNorm z⁻¹ := by
  rcases hz with rfl | hz
  · simp [ZeroOrUnitNorm]
  · exact Or.inr (by rw [norm_inv, hz, inv_one])

theorem ZeroOrUnitNorm.pow {z : ℂ} (hz : ZeroOrUnitNorm z) (n : ℕ) :
    ZeroOrUnitNorm (z ^ n) := by
  induction n with
  | zero => simpa using ZeroOrUnitNorm.one
  | succ n ih => simpa only [pow_succ] using ih.mul hz

theorem ZeroOrUnitNorm.zpow {z : ℂ} (hz : ZeroOrUnitNorm z) (n : ℤ) :
    ZeroOrUnitNorm (z ^ n) := by
  cases n with
  | ofNat n =>
      change ZeroOrUnitNorm (z ^ (n : ℤ))
      simpa only [zpow_natCast] using hz.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hz.pow (n + 1)).inv

theorem ZeroOrUnitNorm.finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, ZeroOrUnitNorm (f i)) :
    ZeroOrUnitNorm (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ZeroOrUnitNorm.one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem ZeroOrUnitNorm.multiset_prod (s : Multiset ℂ)
    (hs : ∀ z ∈ s, ZeroOrUnitNorm z) : ZeroOrUnitNorm s.prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using ZeroOrUnitNorm.one
  | @cons z s ih =>
    rw [Multiset.prod_cons]
    exact (hs z (Multiset.mem_cons_self z s)).mul
      (ih (fun w hw => hs w (Multiset.mem_cons_of_mem hw)))

/-- The inverse-square ideal weight. -/
def inverseSquare (N : ℝ) : ℝ := (N ^ 2)⁻¹

theorem inverseSquare_nonneg (N : ℝ) : 0 ≤ inverseSquare N := by
  exact inv_nonneg.mpr (sq_nonneg N)

/-- Enlarging the cubic variable to a linear variable is valid since all
integral ideal norms are at least one. -/
theorem cubic_scale_inverse_square_le (a c n t : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hn : 1 ≤ n) (ht : 0 < t) :
    inverseSquare (t * a * c * n ^ 3) ≤
      t⁻¹ ^ 2 * inverseSquare a * inverseSquare c * inverseSquare n := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hn2 : 1 ≤ n ^ 2 := one_le_pow₀ hn
  have hn3 : n ≤ n ^ 3 := by
    calc
      n = n * 1 := by ring
      _ ≤ n * n ^ 2 := mul_le_mul_of_nonneg_left hn2 hn0.le
      _ = n ^ 3 := by ring
  have hlin : 0 < t * a * c * n := by positivity
  have hcub : t * a * c * n ≤ t * a * c * n ^ 3 :=
    mul_le_mul_of_nonneg_left hn3 (by positivity)
  have hsq : (t * a * c * n) ^ 2 ≤ (t * a * c * n ^ 3) ^ 2 :=
    pow_le_pow_left₀ hlin.le hcub 2
  calc
    inverseSquare (t * a * c * n ^ 3) ≤ inverseSquare (t * a * c * n) :=
      inv_le_inv₀ (sq_pos_of_pos (hlin.trans_le hcub)) (sq_pos_of_pos hlin) |>.mpr hsq
    _ = t⁻¹ ^ 2 * inverseSquare a * inverseSquare c * inverseSquare n := by
      simp only [inverseSquare, mul_pow, mul_inv_rev, inv_pow]
      ring

/-- Three independent convergent positive series give the ideal majorant.
No squarefree or coprimality restriction is required after positive extension. -/
theorem summable_triple_inverseSquare {I : Type*} (N : I → ℝ)
    (hN : Summable (fun a => inverseSquare (N a))) :
    Summable (fun x : I × I × I =>
      inverseSquare (N x.1) * inverseSquare (N x.2.1) * inverseSquare (N x.2.2)) := by
  have htwo := hN.mul_of_nonneg hN
    (fun a => inverseSquare_nonneg (N a)) (fun a => inverseSquare_nonneg (N a))
  have hthree := hN.mul_of_nonneg htwo
    (fun a => inverseSquare_nonneg (N a))
    (fun x => mul_nonneg (inverseSquare_nonneg (N x.1))
      (inverseSquare_nonneg (N x.2)))
  simpa only [mul_assoc] using hthree

/-- Generic fixed-row reflected sum.  The encoding retains all discrete
data and is injective; therefore no multiplicity is silently dropped. -/
theorem summable_reflected_of_quadratic_tail
    {B I J C : Type*} [Finite B]
    (N : I → ℝ) (hNpos : ∀ a, 1 ≤ N a)
    (hNsum : Summable (fun a => inverseSquare (N a)))
    (encode : J → B × I × I × I) (hencode : Function.Injective encode)
    (sector : J → C) (scale arithmeticBound : B → ℝ)
    (hscale : ∀ b, 0 < scale b) (hbound : ∀ b, 0 ≤ arithmeticBound b)
    (coefficient : J → ℂ)
    (hcoefficient : ∀ j, ‖coefficient j‖ ≤ arithmeticBound (encode j).1)
    (kernel : C → ℝ → ℂ) (kernelBound : ℝ) (hkernelBound : 0 ≤ kernelBound)
    (hkernel : ∀ c y, 0 < y → ‖kernel c y‖ ≤ kernelBound * inverseSquare y) :
    Summable (fun j => coefficient j * kernel (sector j)
      (scale (encode j).1 * N (encode j).2.1 * N (encode j).2.2.1 *
        N (encode j).2.2.2 ^ 3)) := by
  let branchBound : B → ℝ := fun b => arithmeticBound b * kernelBound * (scale b)⁻¹ ^ 2
  have hb : Summable branchBound := Summable.of_finite
  have hb0 : ∀ b, 0 ≤ branchBound b := by
    intro b
    exact mul_nonneg (mul_nonneg (hbound b) hkernelBound) (sq_nonneg _)
  have hthree := summable_triple_inverseSquare N hNsum
  have hprod := hb.mul_of_nonneg hthree hb0
    (fun x => mul_nonneg
      (mul_nonneg (inverseSquare_nonneg _) (inverseSquare_nonneg _))
      (inverseSquare_nonneg _))
  have hmajor := hprod.comp_injective hencode
  apply Summable.of_norm_bounded hmajor
  intro j
  have ha : 0 < N (encode j).2.1 := lt_of_lt_of_le zero_lt_one (hNpos _)
  have hc : 0 < N (encode j).2.2.1 := lt_of_lt_of_le zero_lt_one (hNpos _)
  have hn : 0 < N (encode j).2.2.2 := lt_of_lt_of_le zero_lt_one (hNpos _)
  have hy : 0 < scale (encode j).1 * N (encode j).2.1 * N (encode j).2.2.1 *
      N (encode j).2.2.2 ^ 3 := by
    exact mul_pos (mul_pos (mul_pos (hscale _) ha) hc) (pow_pos hn _)
  rw [norm_mul]
  calc
    _ ≤ arithmeticBound (encode j).1 *
        (kernelBound * inverseSquare
          (scale (encode j).1 * N (encode j).2.1 * N (encode j).2.2.1 *
            N (encode j).2.2.2 ^ 3)) :=
      mul_le_mul (hcoefficient j) (hkernel _ _ hy) (norm_nonneg _) (hbound _)
    _ ≤ arithmeticBound (encode j).1 * kernelBound *
        ((scale (encode j).1)⁻¹ ^ 2 * inverseSquare (N (encode j).2.1) *
          inverseSquare (N (encode j).2.2.1) * inverseSquare (N (encode j).2.2.2)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (cubic_scale_inverse_square_le _ _ _ _ ha hc (hNpos _) (hscale _))
        (mul_nonneg (hbound _) hkernelBound)
    _ = _ := by dsimp [branchBound, Function.comp_def]; ring

end ThetaGlobal.ReflectedAbsolute
