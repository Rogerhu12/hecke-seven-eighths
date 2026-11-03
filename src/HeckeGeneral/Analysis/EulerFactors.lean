import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import HeckeGeneral.Analysis.MeromorphicDescent

/-!
# Deleting finitely many unitary Euler factors

The residue cardinalities and character values are explicit data. These
lemmas apply to any number field once its local Euler coefficients are
identified. No infinite Euler product or analytic continuation is assumed.
-/

namespace HeckeGeneral.Analysis

noncomputable section

open scoped BigOperators

/-- The polynomial removed when one local Euler factor is deleted. -/
def eulerPolynomial (q : ℝ) (a : ℂ) (s : ℂ) : ℂ := 1 - a * (q : ℂ) ^ (-s)

theorem norm_localTerm_lt_one {q : ℝ} {a s : ℂ}
    (hq : 1 < q) (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) :
    ‖a * (q : ℂ) ^ (-s)‖ < 1 := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  simp only [Complex.neg_re]
  calc
    ‖a‖ * q ^ (-s.re) ≤ 1 * q ^ (-s.re) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hq0.le _)
    _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs)

theorem eulerPolynomial_ne_zero {q : ℝ} {a s : ℂ}
    (hq : 1 < q) (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) :
    eulerPolynomial q a s ≠ 0 := by
  intro hzero
  have heq : a * (q : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hzero).symm
  have hlt := norm_localTerm_lt_one hq ha hs
  rw [heq, norm_one] at hlt
  exact lt_irrefl 1 hlt

theorem eulerPolynomial_differentiable {q : ℝ} (hq : 0 < q) (a : ℂ) :
    Differentiable ℂ (eulerPolynomial q a) := by
  have hpow : Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ (-s)) :=
    differentiable_neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hq.ne'))
  exact (differentiable_const 1).sub ((differentiable_const a).mul hpow)

theorem eulerPolynomial_analyticAt {q : ℝ} (hq : 0 < q) (a s : ℂ) :
    AnalyticAt ℂ (eulerPolynomial q a) s :=
  (eulerPolynomial_differentiable hq a).analyticAt s

/-- Finite deletion does not change nonvanishing on the positive half-plane. -/
theorem finite_euler_deletion_ne_zero_iff {ι : Type*} (S : Finset ι)
    (q : ι → ℝ) (a : ι → ℂ) (L : ℂ → ℂ) {s : ℂ}
    (hq : ∀ i ∈ S, 1 < q i) (ha : ∀ i ∈ S, ‖a i‖ ≤ 1) (hs : 0 < s.re) :
    ((∏ i ∈ S, eulerPolynomial (q i) (a i) s) * L s ≠ 0) ↔ L s ≠ 0 := by
  have hP : (∏ i ∈ S, eulerPolynomial (q i) (a i) s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => eulerPolynomial_ne_zero (hq i hi) (ha i hi) hs)
  exact mul_ne_zero_iff.trans (and_iff_right hP)

/-- Even at a pole of `L`, multiplication by a finite Euler polynomial leaves
the actual meromorphic order unchanged. -/
theorem euler_deletion_order_eq {q : ℝ} {a s : ℂ} (L : ℂ → ℂ)
    (hq : 1 < q) (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) :
    meromorphicOrderAt (fun z => eulerPolynomial q a z * L z) s =
      meromorphicOrderAt L s := by
  exact meromorphicOrderAt_mul_of_ne_zero
    (eulerPolynomial_analyticAt (lt_trans zero_lt_one hq) a s)
    (eulerPolynomial_ne_zero hq ha hs)

/-- Finite local deletion preserves meromorphicity, as well as its order.
This prevents using the fallback order of a nonmeromorphic function as
evidence that an analytic continuation has been constructed. -/
theorem euler_deletion_meromorphicAt_iff {q : ℝ} {a s : ℂ} (L : ℂ → ℂ)
    (hq : 1 < q) (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) :
    MeromorphicAt (fun z => eulerPolynomial q a z * L z) s ↔ MeromorphicAt L s :=
  meromorphicAt_mul_iff_of_ne_zero
    (eulerPolynomial_analyticAt (lt_trans zero_lt_one hq) a s)
    (eulerPolynomial_ne_zero hq ha hs)

/-- The polynomial for deleting an actual finite set of local factors. -/
def finiteEulerPolynomial {ι : Type*} (S : Finset ι)
    (q : ι → ℝ) (a : ι → ℂ) (s : ℂ) : ℂ :=
  ∏ i ∈ S, eulerPolynomial (q i) (a i) s

theorem finiteEulerPolynomial_analyticAt {ι : Type*} (S : Finset ι)
    (q : ι → ℝ) (a : ι → ℂ) (s : ℂ) (hq : ∀ i ∈ S, 0 < q i) :
    AnalyticAt ℂ (finiteEulerPolynomial S q a) s :=
  S.analyticAt_fun_prod (fun i hi => eulerPolynomial_analyticAt (hq i hi) (a i) s)

theorem finiteEulerPolynomial_ne_zero {ι : Type*} (S : Finset ι)
    (q : ι → ℝ) (a : ι → ℂ) {s : ℂ}
    (hq : ∀ i ∈ S, 1 < q i) (ha : ∀ i ∈ S, ‖a i‖ ≤ 1) (hs : 0 < s.re) :
    finiteEulerPolynomial S q a s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i hi => eulerPolynomial_ne_zero (hq i hi) (ha i hi) hs)

/-- Finite deletion preserves order even at the possible norm-character pole. -/
theorem finite_euler_deletion_order_eq {ι : Type*} (S : Finset ι)
    (q : ι → ℝ) (a : ι → ℂ) (L : ℂ → ℂ) {s : ℂ}
    (hq : ∀ i ∈ S, 1 < q i) (ha : ∀ i ∈ S, ‖a i‖ ≤ 1) (hs : 0 < s.re) :
    meromorphicOrderAt (fun z => finiteEulerPolynomial S q a z * L z) s =
      meromorphicOrderAt L s :=
  meromorphicOrderAt_mul_of_ne_zero
    (finiteEulerPolynomial_analyticAt S q a s (fun i hi => lt_trans zero_lt_one (hq i hi)))
    (finiteEulerPolynomial_ne_zero S q a hq ha hs)

theorem finite_euler_deletion_meromorphicAt_iff {ι : Type*} (S : Finset ι)
    (q : ι → ℝ) (a : ι → ℂ) (L : ℂ → ℂ) {s : ℂ}
    (hq : ∀ i ∈ S, 1 < q i) (ha : ∀ i ∈ S, ‖a i‖ ≤ 1) (hs : 0 < s.re) :
    MeromorphicAt (fun z => finiteEulerPolynomial S q a z * L z) s ↔ MeromorphicAt L s :=
  meromorphicAt_mul_iff_of_ne_zero
    (finiteEulerPolynomial_analyticAt S q a s (fun i hi => lt_trans zero_lt_one (hq i hi)))
    (finiteEulerPolynomial_ne_zero S q a hq ha hs)

/-- Removing any finite collection of unitary local Euler factors preserves
genuine meromorphic zero-freeness on every subset of the positive half-plane. -/
theorem finite_euler_deletion_zeroFreeOn_iff {ι : Type*} (S : Finset ι)
    (q : ι → ℝ) (a : ι → ℂ) (L : ℂ → ℂ) (U : Set ℂ)
    (hq : ∀ i ∈ S, 1 < q i) (ha : ∀ i ∈ S, ‖a i‖ ≤ 1)
    (hU : ∀ s ∈ U, 0 < s.re) :
    MeromorphicZeroFreeOn (fun z => finiteEulerPolynomial S q a z * L z) U ↔
      MeromorphicZeroFreeOn L U := by
  constructor
  · rintro ⟨hm, ho⟩
    refine ⟨fun s hs => (finite_euler_deletion_meromorphicAt_iff S q a L hq ha
      (hU s hs)).mp (hm s hs), ?_⟩
    intro s hs
    rw [← finite_euler_deletion_order_eq S q a L hq ha (hU s hs)]
    exact ho s hs
  · rintro ⟨hm, ho⟩
    refine ⟨fun s hs => (finite_euler_deletion_meromorphicAt_iff S q a L hq ha
      (hU s hs)).mpr (hm s hs), ?_⟩
    intro s hs
    rw [finite_euler_deletion_order_eq S q a L hq ha (hU s hs)]
    exact ho s hs

end

end HeckeGeneral.Analysis
