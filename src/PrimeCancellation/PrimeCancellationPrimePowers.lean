import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A square-root bound for finite prime-power tails

The objects below need not be prime ideals.  The only counting input is that
the number of objects of norm at most Y is at most d * Y, and every norm is
at least two.  The bounds are uniform in the finite exponent truncation.
No Hecke function, prime-sum cancellation, or infinite-sum identity is assumed.
-/

noncomputable section
open scoped Classical BigOperators

namespace PrimeCancellationPrimePowers

theorem root_le_geometric_sqrt {X : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hpow : (2 : ℝ) ^ k ≤ X) :
    X ^ (k : ℝ)⁻¹ ≤ (2 : ℝ) ^ (1 - (k : ℝ) / 2) * Real.sqrt X := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have he : (k : ℝ)⁻¹ - (1 / 2 : ℝ) ≤ 0 := by
    have hrecip : (k : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hk2
    norm_num at hrecip
    linarith
  have hX : 0 < X := (pow_pos (by norm_num : (0 : ℝ) < 2) k).trans_le hpow
  have hmono := Real.rpow_le_rpow_of_nonpos
    (pow_pos (by norm_num : (0 : ℝ) < 2) k) hpow he
  have hexp : ((2 : ℝ) ^ k) ^ ((k : ℝ)⁻¹ - 1 / 2) =
      (2 : ℝ) ^ (1 - (k : ℝ) / 2) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [mul_sub, mul_inv_cancel₀ hkpos.ne']
    ring
  calc
    X ^ (k : ℝ)⁻¹ = X ^ ((k : ℝ)⁻¹ - 1 / 2) * Real.sqrt X := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX]
      congr 1
      ring
    _ ≤ ((2 : ℝ) ^ k) ^ ((k : ℝ)⁻¹ - 1 / 2) * Real.sqrt X :=
      mul_le_mul_of_nonneg_right hmono (Real.sqrt_nonneg X)
    _ = _ := by rw [hexp]

def ratio : ℝ := (Real.sqrt 2)⁻¹

theorem ratio_pos : 0 < ratio := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))

theorem ratio_lt_one : ratio < 1 := by
  unfold ratio
  rw [← one_div]
  apply (div_lt_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
  simpa using Real.one_lt_sqrt_two

theorem ratio_sq : ratio ^ 2 = (1 / 2 : ℝ) := by
  unfold ratio
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem geometric_half_constant : 1 / (2 * (1 - ratio)) = 1 + ratio := by
  apply (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
    (sub_pos.mpr ratio_lt_one).ne')).mpr
  nlinarith [ratio_sq]

theorem geometric_sum_le (N : ℕ) :
    (∑ n ∈ Finset.range N, ratio ^ n) ≤ 1 / (1 - ratio) := by
  apply (le_div_iff₀ (sub_pos.mpr ratio_lt_one)).mpr
  have hgeom := geom_sum_mul_neg ratio N
  nlinarith [pow_nonneg ratio_pos.le N]

theorem root_shift_le {X : ℝ} (n : ℕ) (hpow : (2 : ℝ) ^ (n + 2) ≤ X) :
    X ^ ((n + 2 : ℕ) : ℝ)⁻¹ ≤ ratio ^ n * Real.sqrt X := by
  have h := root_le_geometric_sqrt (k := n + 2) (by omega) hpow
  have hexp : (1 : ℝ) - ((n + 2 : ℕ) : ℝ) / 2 =
      (-(1 / 2 : ℝ)) * (n : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hratio : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = ratio := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
    rfl
  simpa only [hratio] using h

variable {α : Type*}

def powerCutoff (pool : Finset α) (norm : α → ℝ) (X : ℝ) (k : ℕ) : Finset α :=
  pool.filter (fun p => norm p ^ k ≤ X)

theorem powerCutoff_card_le_root (pool : Finset α) (norm : α → ℝ)
    (d X : ℝ) (k : ℕ) (hX : 0 ≤ X) (hk : 0 < k)
    (hnorm : ∀ p ∈ pool, 2 ≤ norm p)
    (hcount : ∀ Y : ℝ, 0 ≤ Y →
      ((pool.filter (fun p => norm p ≤ Y)).card : ℝ) ≤ d * Y) :
    ((powerCutoff pool norm X k).card : ℝ) ≤ d * X ^ (k : ℝ)⁻¹ := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hsubset : powerCutoff pool norm X k ⊆
      pool.filter (fun p => norm p ≤ X ^ (k : ℝ)⁻¹) := by
    intro p hp
    obtain ⟨hpool, hpower⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨hpool, ?_⟩
    apply (Real.le_rpow_inv_iff_of_pos
      (by linarith [hnorm p hpool] : 0 ≤ norm p) hX hkreal).mpr
    simpa only [Real.rpow_natCast] using hpower
  calc
    ((powerCutoff pool norm X k).card : ℝ) ≤
        ((pool.filter (fun p => norm p ≤ X ^ (k : ℝ)⁻¹)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ _ := hcount _ (Real.rpow_nonneg hX _)

theorem powerCutoff_card_le_geometric (pool : Finset α) (norm : α → ℝ)
    (d X : ℝ) (n : ℕ) (hd : 0 ≤ d) (hX : 0 ≤ X)
    (hnorm : ∀ p ∈ pool, 2 ≤ norm p)
    (hcount : ∀ Y : ℝ, 0 ≤ Y →
      ((pool.filter (fun p => norm p ≤ Y)).card : ℝ) ≤ d * Y) :
    ((powerCutoff pool norm X (n + 2)).card : ℝ) ≤
      d * ratio ^ n * Real.sqrt X := by
  by_cases hpow : (2 : ℝ) ^ (n + 2) ≤ X
  · calc
      ((powerCutoff pool norm X (n + 2)).card : ℝ) ≤
          d * X ^ ((n + 2 : ℕ) : ℝ)⁻¹ :=
        powerCutoff_card_le_root pool norm d X (n + 2) hX (by omega) hnorm hcount
      _ ≤ d * (ratio ^ n * Real.sqrt X) :=
        mul_le_mul_of_nonneg_left (root_shift_le n hpow) hd
      _ = _ := by ring
  · have hempty : powerCutoff pool norm X (n + 2) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hpool, hpower⟩ := Finset.mem_filter.mp hp
      exact hpow ((pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (hnorm p hpool) (n + 2)).trans hpower)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hd (pow_nonneg ratio_pos.le n)) (Real.sqrt_nonneg X)

/-- The bound does not grow with the exponent cutoff N. -/
theorem sum_powerCutoff_cards_le (pool : Finset α) (norm : α → ℝ)
    (d X : ℝ) (N : ℕ) (hd : 0 ≤ d) (hX : 0 ≤ X)
    (hnorm : ∀ p ∈ pool, 2 ≤ norm p)
    (hcount : ∀ Y : ℝ, 0 ≤ Y →
      ((pool.filter (fun p => norm p ≤ Y)).card : ℝ) ≤ d * Y) :
    (∑ n ∈ Finset.range N, ((powerCutoff pool norm X (n + 2)).card : ℝ)) ≤
      d * Real.sqrt X / (1 - ratio) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, d * ratio ^ n * Real.sqrt X :=
      Finset.sum_le_sum (fun n _ => powerCutoff_card_le_geometric
        pool norm d X n hd hX hnorm hcount)
    _ = (d * Real.sqrt X) * ∑ n ∈ Finset.range N, ratio ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ (d * Real.sqrt X) * (1 / (1 - ratio)) :=
      mul_le_mul_of_nonneg_left (geometric_sum_le N) (mul_nonneg hd (Real.sqrt_nonneg X))
    _ = _ := by ring

/-- Coefficients bounded by M/k yield the explicit elementary geometric constant
`1 + 1 / sqrt 2`.  The conclusion is uniform in both finite truncations. -/
theorem norm_weighted_primePower_tail_le (pool : Finset α) (norm : α → ℝ)
    (d X M : ℝ) (N : ℕ) (c : ℕ → α → ℂ)
    (hd : 0 ≤ d) (hX : 0 ≤ X) (hM : 0 ≤ M)
    (hnorm : ∀ p ∈ pool, 2 ≤ norm p)
    (hcount : ∀ Y : ℝ, 0 ≤ Y →
      ((pool.filter (fun p => norm p ≤ Y)).card : ℝ) ≤ d * Y)
    (hcoef : ∀ n ∈ Finset.range N, ∀ p ∈ powerCutoff pool norm X (n + 2),
      ‖c n p‖ ≤ M / ((n + 2 : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.range N, ∑ p ∈ powerCutoff pool norm X (n + 2), c n p‖ ≤
      M * d * (1 + ratio) * Real.sqrt X := by
  have hrow (n : ℕ) (hn : n ∈ Finset.range N) :
      ‖∑ p ∈ powerCutoff pool norm X (n + 2), c n p‖ ≤
        ((powerCutoff pool norm X (n + 2)).card : ℝ) * (M / 2) := by
    calc
      _ ≤ ∑ p ∈ powerCutoff pool norm X (n + 2), ‖c n p‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ powerCutoff pool norm X (n + 2), M / 2 := by
        apply Finset.sum_le_sum
        intro p hp
        refine (hcoef n hn p hp).trans ?_
        apply div_le_div_of_nonneg_left hM (by norm_num : (0 : ℝ) < 2)
        exact_mod_cast (show 2 ≤ n + 2 by omega)
      _ = _ := by simp
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        ‖∑ p ∈ powerCutoff pool norm X (n + 2), c n p‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N,
        ((powerCutoff pool norm X (n + 2)).card : ℝ) * (M / 2) :=
      Finset.sum_le_sum hrow
    _ = (M / 2) * ∑ n ∈ Finset.range N,
        ((powerCutoff pool norm X (n + 2)).card : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ (M / 2) * (d * Real.sqrt X / (1 - ratio)) :=
      mul_le_mul_of_nonneg_left
        (sum_powerCutoff_cards_le pool norm d X N hd hX hnorm hcount)
        (div_nonneg hM (by norm_num))
    _ = M * d * Real.sqrt X * (1 / (2 * (1 - ratio))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [geometric_half_constant]; ring

/-- The actual finite-window term after logarithmic cancellation. -/
def primePowerWindowTerm (norm : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ)
    (P : ℝ) (n : ℕ) (p : α) : ℂ :=
  a p ^ (n + 2) * W (norm p ^ (n + 2) / P) / ((n + 2 : ℕ) : ℂ)

theorem norm_primePowerWindowTerm_le (norm : α → ℝ) (a : α → ℂ)
    (W : ℝ → ℂ) (P M : ℝ) (n : ℕ) (p : α)
    (ha : ‖a p‖ ≤ 1) (hW : ‖W (norm p ^ (n + 2) / P)‖ ≤ M) :
    ‖primePowerWindowTerm norm a W P n p‖ ≤ M / ((n + 2 : ℕ) : ℝ) := by
  rw [primePowerWindowTerm, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (n + 2))
  calc
    ‖a p‖ ^ (n + 2) * ‖W (norm p ^ (n + 2) / P)‖ ≤ 1 * M :=
      mul_le_mul (pow_le_one₀ (norm_nonneg (a p)) ha) hW
        (norm_nonneg _) zero_le_one
    _ = M := one_mul M

theorem primePowerWindowTerm_eq_zero_of_not_cutoff (norm : α → ℝ)
    (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ) (n : ℕ) (p : α)
    (hP : 0 < P) (hsupport : Function.support W ⊆ Set.Icc (1 : ℝ) 2)
    (hnot : ¬norm p ^ (n + 2) ≤ 2 * P) :
    primePowerWindowTerm norm a W P n p = 0 := by
  have harg : 2 < norm p ^ (n + 2) / P :=
    (lt_div_iff₀ hP).mpr (lt_of_not_ge hnot)
  have hW : W (norm p ^ (n + 2) / P) = 0 := by
    by_contra hne
    exact (not_le_of_gt harg) (hsupport hne).2
  simp only [primePowerWindowTerm, hW, mul_zero, zero_div]

/-- The window's upper support makes deletion outside the finite power
cutoff an equality, not an additional estimate. -/
theorem sum_primePowerWindowTerm_eq_cutoff (pool : Finset α) (norm : α → ℝ)
    (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ) (n : ℕ)
    (hP : 0 < P) (hsupport : Function.support W ⊆ Set.Icc (1 : ℝ) 2) :
    (∑ p ∈ pool, primePowerWindowTerm norm a W P n p) =
      ∑ p ∈ powerCutoff pool norm (2 * P) (n + 2),
        primePowerWindowTerm norm a W P n p := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  apply primePowerWindowTerm_eq_zero_of_not_cutoff norm a W P n p hP hsupport
  intro hpower
  exact hnot (Finset.mem_filter.mpr ⟨hp, hpower⟩)

/-- A genuine double finite sum with character-like coefficients and a
smooth-window support condition.  The bound is independent of both the
prime-object pool and the exponent cutoff, provided their counting
constant d is uniform. Smoothness itself is not needed for this estimate. -/
theorem norm_primePowerWindow_tail_le (pool : Finset α) (norm : α → ℝ)
    (d P M : ℝ) (N : ℕ) (a : α → ℂ) (W : ℝ → ℂ)
    (hd : 0 ≤ d) (hP : 0 < P) (hM : 0 ≤ M)
    (hnorm : ∀ p ∈ pool, 2 ≤ norm p)
    (hcount : ∀ Y : ℝ, 0 ≤ Y →
      ((pool.filter (fun p => norm p ≤ Y)).card : ℝ) ≤ d * Y)
    (ha : ∀ p ∈ pool, ‖a p‖ ≤ 1)
    (hsupport : Function.support W ⊆ Set.Icc (1 : ℝ) 2)
    (hW : ∀ x : ℝ, ‖W x‖ ≤ M) :
    ‖∑ n ∈ Finset.range N, ∑ p ∈ pool,
        primePowerWindowTerm norm a W P n p‖ ≤
      M * d * (1 + ratio) * Real.sqrt (2 * P) := by
  have heq :
      (∑ n ∈ Finset.range N, ∑ p ∈ pool, primePowerWindowTerm norm a W P n p) =
        ∑ n ∈ Finset.range N, ∑ p ∈ powerCutoff pool norm (2 * P) (n + 2),
          primePowerWindowTerm norm a W P n p := by
    apply Finset.sum_congr rfl
    intro n _
    exact sum_primePowerWindowTerm_eq_cutoff pool norm a W P n hP hsupport
  rw [heq]
  apply norm_weighted_primePower_tail_le pool norm d (2 * P) M N
    (fun n p => primePowerWindowTerm norm a W P n p)
    hd (mul_nonneg (by norm_num) hP.le) hM hnorm hcount
  intro n _ p hp
  exact norm_primePowerWindowTerm_le norm a W P M n p
    (ha p (Finset.mem_filter.mp hp).1) (hW _)

theorem one_add_ratio_mul_sqrt_two :
    (1 + ratio) * Real.sqrt 2 = 1 + Real.sqrt 2 := by
  have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  unfold ratio
  rw [add_mul, one_mul, inv_mul_cancel₀ hne]
  ring

/-- With X=2P the explicit constant is d*(1+sqrt 2), times the window bound. -/
theorem norm_primePowerWindow_tail_le_sqrt (pool : Finset α) (norm : α → ℝ)
    (d P M : ℝ) (N : ℕ) (a : α → ℂ) (W : ℝ → ℂ)
    (hd : 0 ≤ d) (hP : 0 < P) (hM : 0 ≤ M)
    (hnorm : ∀ p ∈ pool, 2 ≤ norm p)
    (hcount : ∀ Y : ℝ, 0 ≤ Y →
      ((pool.filter (fun p => norm p ≤ Y)).card : ℝ) ≤ d * Y)
    (ha : ∀ p ∈ pool, ‖a p‖ ≤ 1)
    (hsupport : Function.support W ⊆ Set.Icc (1 : ℝ) 2)
    (hW : ∀ x : ℝ, ‖W x‖ ≤ M) :
    ‖∑ n ∈ Finset.range N, ∑ p ∈ pool,
        primePowerWindowTerm norm a W P n p‖ ≤
      M * d * (1 + Real.sqrt 2) * Real.sqrt P := by
  calc
    _ ≤ M * d * (1 + ratio) * Real.sqrt (2 * P) :=
      norm_primePowerWindow_tail_le pool norm d P M N a W hd hP hM hnorm hcount
        ha hsupport hW
    _ = M * d * (1 + Real.sqrt 2) * Real.sqrt P := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        M * d * (1 + ratio) * (Real.sqrt 2 * Real.sqrt P) =
            M * d * ((1 + ratio) * Real.sqrt 2) * Real.sqrt P := by ring
        _ = _ := by rw [one_add_ratio_mul_sqrt_two]

#print axioms root_le_geometric_sqrt
#print axioms ratio_pos
#print axioms ratio_lt_one
#print axioms ratio_sq
#print axioms geometric_half_constant
#print axioms geometric_sum_le
#print axioms root_shift_le
#print axioms powerCutoff_card_le_root
#print axioms powerCutoff_card_le_geometric
#print axioms sum_powerCutoff_cards_le
#print axioms norm_weighted_primePower_tail_le
#print axioms norm_primePowerWindowTerm_le
#print axioms primePowerWindowTerm_eq_zero_of_not_cutoff
#print axioms sum_primePowerWindowTerm_eq_cutoff
#print axioms norm_primePowerWindow_tail_le
#print axioms one_add_ratio_mul_sqrt_two
#print axioms norm_primePowerWindow_tail_le_sqrt

end PrimeCancellationPrimePowers
