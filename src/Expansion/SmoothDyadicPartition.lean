import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
An explicit smooth dyadic partition for actual ideal norms.  The same
annular profile works at every scale.  Finite decomposition and extraction
are proved for arbitrary finite coefficient sets, preserving all zero masks.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Dyadic
open scoped Classical BigOperators ContDiff

def cutoff (x : ℝ) : ℝ := 1 - Real.smoothTransition (x - 1)

theorem cutoff_smooth : ContDiff ℝ ∞ cutoff := by
  unfold cutoff
  fun_prop

theorem cutoff_range (x : ℝ) : 0 ≤ cutoff x ∧ cutoff x ≤ 1 := by
  unfold cutoff
  constructor <;> linarith [Real.smoothTransition.nonneg (x - 1),
    Real.smoothTransition.le_one (x - 1)]

theorem cutoff_one {x : ℝ} (hx : x ≤ 1) : cutoff x = 1 := by
  simp only [cutoff, Real.smoothTransition.zero_of_nonpos (by linarith : x - 1 ≤ 0),
    sub_zero]

theorem cutoff_zero {x : ℝ} (hx : 2 ≤ x) : cutoff x = 0 := by
  simp only [cutoff, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x - 1),
    sub_self]

theorem cutoff_antitone : Antitone cutoff := by
  intro x y hxy
  exact sub_le_sub_left (Real.smoothTransition.monotone (sub_le_sub_right hxy 1)) 1

def annular (x : ℝ) : ℝ := cutoff x - cutoff (2 * x)
def annularProfile (x : ℝ) : ℂ := annular x

theorem annular_smooth : ContDiff ℝ ∞ annular := by
  exact cutoff_smooth.sub (cutoff_smooth.comp (contDiff_const.mul contDiff_id))

theorem annularProfile_smooth : ContDiff ℝ ∞ annularProfile := by
  unfold annularProfile
  exact Complex.ofRealCLM.contDiff.comp annular_smooth

theorem annular_zero_of_le {x : ℝ} (hx : x ≤ 1 / 2) : annular x = 0 := by
  rw [annular, cutoff_one (by linarith), cutoff_one (by linarith), sub_self]

theorem annular_zero_of_ge {x : ℝ} (hx : 2 ≤ x) : annular x = 0 := by
  rw [annular, cutoff_zero hx, cutoff_zero (by linarith), sub_self]

theorem annular_range (x : ℝ) : 0 ≤ annular x ∧ annular x ≤ 1 := by
  by_cases hx : x ≤ 1 / 2
  · simp [annular_zero_of_le hx]
  · have hx0 : 0 ≤ x := by linarith
    have hm := cutoff_antitone (show x ≤ 2 * x by linarith)
    unfold annular
    constructor <;> linarith [(cutoff_range x).1, (cutoff_range x).2,
      (cutoff_range (2 * x)).1]

theorem annularProfile_norm_le (x : ℝ) : ‖annularProfile x‖ ≤ 1 := by
  simpa only [annularProfile, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (annular_range x).1] using (annular_range x).2

theorem annular_nonzero_bounds {x : ℝ} (hx : annular x ≠ 0) :
    1 / 2 < x ∧ x < 2 := by
  exact ⟨lt_of_not_ge (fun h => hx (annular_zero_of_le h)),
    lt_of_not_ge (fun h => hx (annular_zero_of_ge h))⟩

theorem annularProfile_support :
    Function.support annularProfile ⊆ Set.Icc (1 / 2) 2 := by
  intro x hx
  have hn : annular x ≠ 0 := by
    intro h
    exact hx (by simp [annularProfile, h])
  exact ⟨(annular_nonzero_bounds hn).1.le,
    (annular_nonzero_bounds hn).2.le⟩

theorem annularProfile_compact : HasCompactSupport annularProfile :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc annularProfile_support

/-- The endpoint terms are explicit, so this identity holds for every real x. -/
theorem sum_annular_telescope (x : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), annular (x / (2 : ℝ) ^ j)) =
      cutoff (x / (2 : ℝ) ^ n) - cutoff (2 * x) := by
  induction n with
  | zero => simp [annular]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, annular]
    have he : 2 * (x / (2 : ℝ) ^ (n + 1)) = x / (2 : ℝ) ^ n := by
      rw [pow_succ]
      field_simp
    rw [he]
    ring

theorem sum_annular_eq_one {x : ℝ} (hx : 1 ≤ x) (n : ℕ)
    (hxn : x ≤ (2 : ℝ) ^ n) :
    (∑ j ∈ Finset.range (n + 1), annular (x / (2 : ℝ) ^ j)) = 1 := by
  rw [sum_annular_telescope, cutoff_one ((div_le_one (by positivity)).mpr hxn),
    cutoff_zero (by linarith), sub_zero]

theorem sum_annularProfile_eq_one {x : ℝ} (hx : 1 ≤ x) (n : ℕ)
    (hxn : x ≤ (2 : ℝ) ^ n) :
    (∑ j ∈ Finset.range (n + 1), annularProfile (x / (2 : ℝ) ^ j)) = 1 := by
  simpa only [annularProfile, ← Complex.ofReal_sum, Complex.ofReal_one] using
    congrArg Complex.ofReal (sum_annular_eq_one hx n hxn)

variable {ι κ : Type*}

def pairBlock (pairs : Finset (ι × κ)) (a : ι × κ → ℂ)
    (N : ι → ℝ) (M : κ → ℝ) (j k : ℕ) : ℂ :=
  ∑ p ∈ pairs, a p * annularProfile (N p.1 / (2 : ℝ) ^ j) *
    annularProfile (M p.2 / (2 : ℝ) ^ k)

/-- Exact two-dimensional dyadic decomposition.  Neither coefficients nor
their ramified zero values are replaced or divided out. -/
theorem sum_pairBlocks (pairs : Finset (ι × κ)) (a : ι × κ → ℂ)
    (N : ι → ℝ) (M : κ → ℝ) (n m : ℕ)
    (hN : ∀ p ∈ pairs, a p ≠ 0 → 1 ≤ N p.1 ∧ N p.1 ≤ (2 : ℝ) ^ n)
    (hM : ∀ p ∈ pairs, a p ≠ 0 → 1 ≤ M p.2 ∧ M p.2 ≤ (2 : ℝ) ^ m) :
    (∑ q ∈ Finset.range (n + 1) ×ˢ Finset.range (m + 1),
      pairBlock pairs a N M q.1 q.2) = ∑ p ∈ pairs, a p := by
  unfold pairBlock
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hap : a p = 0
  · simp [hap]
  rw [Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [sum_annularProfile_eq_one (hM p hp hap).1 m (hM p hp hap).2]
  simp only [mul_one]
  rw [← Finset.mul_sum, sum_annularProfile_eq_one (hN p hp hap).1 n (hN p hp hap).2, mul_one]

/-- A source of size c supplies one actual dyadic block, with precisely the
finite pair-count loss.  This extracts a block, not yet a Fourier witness. -/
theorem exists_large_pairBlock (pairs : Finset (ι × κ)) (a : ι × κ → ℂ)
    (N : ι → ℝ) (M : κ → ℝ) (n m : ℕ)
    (hN : ∀ p ∈ pairs, a p ≠ 0 → 1 ≤ N p.1 ∧ N p.1 ≤ (2 : ℝ) ^ n)
    (hM : ∀ p ∈ pairs, a p ≠ 0 → 1 ≤ M p.2 ∧ M p.2 ≤ (2 : ℝ) ^ m)
    {c : ℝ} (hc : c ≤ ‖∑ p ∈ pairs, a p‖) :
    ∃ j ≤ n, ∃ k ≤ m,
      c ≤ ((n + 1 : ℕ) : ℝ) * (m + 1 : ℕ) * ‖pairBlock pairs a N M j k‖ := by
  let Q := Finset.range (n + 1) ×ˢ Finset.range (m + 1)
  have hQ : Q.Nonempty := ⟨(0, 0), by simp [Q]⟩
  obtain ⟨q, hq, hmax⟩ := Q.exists_max_image
    (fun q => ‖pairBlock pairs a N M q.1 q.2‖) hQ
  have hq' := Finset.mem_product.mp hq
  refine ⟨q.1, by simpa using hq'.1, q.2, by simpa using hq'.2, ?_⟩
  calc
    c ≤ ‖∑ q ∈ Q, pairBlock pairs a N M q.1 q.2‖ := by
      simpa only [Q, sum_pairBlocks pairs a N M n m hN hM] using hc
    _ ≤ ∑ q ∈ Q, ‖pairBlock pairs a N M q.1 q.2‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ Q, ‖pairBlock pairs a N M q.1 q.2‖ :=
      Finset.sum_le_sum (fun q' hq' => hmax q' hq')
    _ = _ := by simp [Q, Finset.card_product, nsmul_eq_mul, mul_assoc]

end Expansion.Dyadic
