import HeckeSkeleton.LowHybrid.Losses
import Mathlib.Algebra.BigOperators.Module

/-!
# Linear counting gives the uniform harmonic small-power bound

The norm is a positive natural number, as for nonzero integral ideals. Only
linear counting of finite norm-bounded sets is used. Summation by parts and
an elementary logarithm inequality provide all harmonic estimates; no zeta
or analytic large-sieve input is added.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators
noncomputable section

/-- Prefix-sum majorization for a nonnegative decreasing weight. -/
theorem sum_mul_le_of_prefix_bound (a w : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hw0 : ∀ n : ℕ, 0 ≤ w n) (hw : Antitone w)
    (ha : ∀ n : ℕ, n ≤ N → (∑ j ∈ Finset.range n, a j) ≤ C * n) :
    (∑ n ∈ Finset.range N, a n * w n) ≤
      C * ∑ n ∈ Finset.range N, w n := by
  have hab := Finset.sum_range_by_parts' a w N
  have hcb := Finset.sum_range_by_parts' (fun _ : ℕ => C) w N
  simp only [smul_eq_mul] at hab hcb
  have hprefix (n : ℕ) : (∑ _j ∈ Finset.range n, C) = C * n := by
    simp [mul_comm]
  simp_rw [hprefix] at hcb
  have hfirst :
      (∑ j ∈ Finset.range N, a j) * w (N - 1) ≤
        (C * N) * w (N - 1) :=
    mul_le_mul_of_nonneg_right (ha N le_rfl) (hw0 (N - 1))
  have hsum :
      (∑ n ∈ Finset.range (N - 1), (C * (n + 1)) * (w (n + 1) - w n)) ≤
        ∑ n ∈ Finset.range (N - 1),
          (∑ j ∈ Finset.range (n + 1), a j) * (w (n + 1) - w n) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnN : n + 1 ≤ N := by
      have := Finset.mem_range.mp hn
      omega
    have hdiff : w (n + 1) - w n ≤ 0 := sub_nonpos.mpr (hw (Nat.le_succ n))
    simpa only [Nat.cast_add, Nat.cast_one] using
      mul_le_mul_of_nonpos_right (ha (n + 1) hnN) hdiff
  calc
    _ = (∑ j ∈ Finset.range N, a j) * w (N - 1) -
        ∑ n ∈ Finset.range (N - 1),
          (∑ j ∈ Finset.range (n + 1), a j) * (w (n + 1) - w n) := hab
    _ ≤ (C * N) * w (N - 1) -
        ∑ n ∈ Finset.range (N - 1), (C * (n + 1)) * (w (n + 1) - w n) :=
      sub_le_sub hfirst hsum
    _ = ∑ n ∈ Finset.range N, C * w n := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcb.symm
    _ = _ := (Finset.mul_sum ..).symm

def harmonicPartial (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)

/-- The elementary logarithmic bound, including the harmless N=0 case. -/
theorem harmonicPartial_le_log (N : ℕ) :
    harmonicPartial N ≤ 1 + Real.log N := by
  induction N with
  | zero => simp [harmonicPartial]
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      simp [harmonicPartial]
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnp : 0 < (n : ℝ) + 1 := by positivity
    have hinc : 1 / ((n : ℝ) + 1) ≤
        Real.log ((n : ℝ) + 1) - Real.log n := by
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hnp hnpos)
      rw [Real.log_div (ne_of_gt hnp) (ne_of_gt hnpos)] at h
      have heq : 1 - (((n : ℝ) + 1) / (n : ℝ))⁻¹ =
          1 / ((n : ℝ) + 1) := by
        rw [inv_div]
        field_simp
        ring
      rw [heq] at h
      exact h
    unfold harmonicPartial at ih ⊢
    rw [Finset.sum_range_succ]
    push_cast
    linarith

/-- A finite linear prefix count controls the weighted counting sum. -/
theorem reciprocal_sum_le_harmonic_of_prefix_count
    {I : Type*} (s : Finset I) (q : I → ℕ) (N : ℕ) (C : ℝ)
    (hq : ∀ i ∈ s, 1 ≤ q i) (hupper : ∀ i ∈ s, q i ≤ N)
    (hcount : ∀ n : ℕ, n ≤ N →
      ((s.filter fun i => q i ≤ n).card : ℝ) ≤ C * n) :
    (∑ i ∈ s, 1 / (q i : ℝ)) ≤ C * harmonicPartial N := by
  classical
  let phi : I → ℕ := fun i => q i - 1
  let a : ℕ → ℝ := fun n => ((s.filter fun i => phi i = n).card : ℝ)
  let w : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hmap : ∀ i ∈ s, phi i ∈ Finset.range N := by
    intro i hi
    have hp := hq i hi
    have hu := hupper i hi
    simp only [phi, Finset.mem_range]
    omega
  have hfilter (n : ℕ) :
      s.filter (fun i => phi i ∈ Finset.range n) = s.filter (fun i => q i ≤ n) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, phi]
    constructor
    · intro ⟨hi, hn⟩
      have hp := hq i hi
      exact ⟨hi, by omega⟩
    · intro ⟨hi, hn⟩
      have hp := hq i hi
      exact ⟨hi, by omega⟩
  have hprefix (n : ℕ) (hn : n ≤ N) :
      (∑ j ∈ Finset.range n, a j) ≤ C * n := by
    have heq : (∑ j ∈ Finset.range n, a j) =
        ((s.filter fun i => phi i ∈ Finset.range n).card : ℝ) := by
      dsimp only [a]
      exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter s (Finset.range n) phi
    rw [heq, hfilter]
    exact hcount n hn
  have hw0 : ∀ n : ℕ, 0 ≤ w n := by intro n; dsimp [w]; positivity
  have hw : Antitone w := by
    intro n m hnm
    dsimp only [w]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have heq : (∑ i ∈ s, 1 / (q i : ℝ)) =
      ∑ n ∈ Finset.range N, a n * w n := by
    calc
      _ = ∑ n ∈ Finset.range N, ∑ i ∈ s with phi i = n, 1 / (q i : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to hmap _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        calc
          _ = ∑ _i ∈ s with phi _i = n, 1 / ((n : ℝ) + 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hp := hq i (Finset.mem_filter.mp hi).1
            have hphi := (Finset.mem_filter.mp hi).2
            have hqi : q i = n + 1 := by dsimp [phi] at hphi; omega
            simp only [hqi, Nat.cast_add, Nat.cast_one]
          _ = a n * w n := by simp [a, w]
  rw [heq]
  exact sum_mul_le_of_prefix_bound a w N C hw0 hw hprefix

/-- Linear counting, stated without choosing global cutoff finsets. -/
def LinearNormCounting {I : Type*} (q : I → ℕ) (C : ℝ) : Prop :=
  ∀ N : ℕ, ∀ s : Finset I, (∀ i ∈ s, q i ≤ N) → (s.card : ℝ) ≤ C * N

/-- A genuine finite-set harmonic estimate deduced from linear norm counting. -/
theorem reciprocal_sum_le_log_of_linear_counting
    {I : Type*} (q : I → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hq : ∀ i : I, 1 ≤ q i) (hcount : LinearNormCounting q C)
    (X : ℝ) (hX : 1 ≤ X) (s : Finset I)
    (hs : ∀ i ∈ s, (q i : ℝ) ≤ X) :
    (∑ i ∈ s, 1 / (q i : ℝ)) ≤ C * (1 + Real.log X) := by
  classical
  let N := Nat.floor X
  have hN : 1 ≤ N := Nat.le_floor (by simpa using hX)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hsN : ∀ i ∈ s, q i ≤ N := fun i hi => Nat.le_floor (hs i hi)
  have hc : ∀ n : ℕ, n ≤ N →
      ((s.filter fun i => q i ≤ n).card : ℝ) ≤ C * n := by
    intro n _hn
    exact hcount n (s.filter fun i => q i ≤ n)
      (fun _ hi => (Finset.mem_filter.mp hi).2)
  calc
    _ ≤ C * harmonicPartial N :=
      reciprocal_sum_le_harmonic_of_prefix_count s q N C (fun i _ => hq i) hsN hc
    _ ≤ C * (1 + Real.log N) :=
      mul_le_mul_of_nonneg_left (harmonicPartial_le_log N) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (Real.log_le_log hNpos
        (Nat.floor_le (le_trans zero_le_one hX)))) hC

/-- Uniform finite harmonic small-power bound, with the constant selected
before X and the actual finite support. -/
theorem reciprocal_sum_subpower_of_linear_counting
    {I : Type*} (q : I → ℕ) (C : ℝ) (hC : 0 < C)
    (hq : ∀ i : I, 1 ≤ q i) (hcount : LinearNormCounting q C)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ X : ℝ, 1 ≤ X → ∀ s : Finset I,
      (∀ i ∈ s, (q i : ℝ) ≤ X) →
        (∑ i ∈ s, 1 / (q i : ℝ)) ≤ CH * X ^ eps := by
  refine ⟨C * (1 + 1 / eps), mul_pos hC (by positivity), ?_⟩
  intro X hX s hs
  calc
    _ ≤ C * (1 + Real.log X) :=
      reciprocal_sum_le_log_of_linear_counting q C (le_of_lt hC) hq hcount X hX s hs
    _ ≤ C * ((1 + 1 / eps) * X ^ eps) :=
      mul_le_mul_of_nonneg_left (one_add_log_le_small_power X eps hX heps) (le_of_lt hC)
    _ = _ := by ring

/-- Cutoff families inherit a single small-power envelope from linear counting. -/
theorem harmonic_cutoff_subpower_of_linear_counting
    {I : Type*} (q : I → ℕ) (C : ℝ) (hC : 0 < C)
    (hq : ∀ i : I, 1 ≤ q i) (hcount : LinearNormCounting q C)
    (cutoff : ℝ → Finset I)
    (hcutoff : ∀ X : ℝ, 1 ≤ X → ∀ i ∈ cutoff X, (q i : ℝ) ≤ X) :
    SubpowerBound (fun X => ∑ i ∈ cutoff X, 1 / (q i : ℝ)) := by
  intro eps heps
  obtain ⟨CH, hCH, hb⟩ := reciprocal_sum_subpower_of_linear_counting
    q C hC hq hcount eps heps
  exact ⟨CH, hCH, fun X hX => hb X hX (cutoff X) (hcutoff X hX)⟩

#print axioms sum_mul_le_of_prefix_bound
#print axioms harmonicPartial_le_log
#print axioms reciprocal_sum_le_harmonic_of_prefix_count
#print axioms reciprocal_sum_le_log_of_linear_counting
#print axioms reciprocal_sum_subpower_of_linear_counting
#print axioms harmonic_cutoff_subpower_of_linear_counting

end
end HeckeSkeleton.LowHybrid
