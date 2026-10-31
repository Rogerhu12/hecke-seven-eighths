import HeckePort.Moments.Descent.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Lean.Elab.Tactic.Omega

/-!
# Finite geometry of the canonical inverse induction

The arithmetic of a single pair of Poisson transforms is recorded in
`HeckePort.Moments.Descent.Basic`.  This file proves the remaining finite
argument: a simultaneous choice of losses, preservation of both margins,
and a uniform bound on the length of every branch.  No energy estimate is
an assumption of this file.
-/

set_option autoImplicit false

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open HeckePort.Moments

/-- One choice of numerical parameters works for every node and every
surviving subcollection of marks.  The depth and losses precede all nodes. -/
structure DescentBudget (Mmax c ε : ℝ) where
  depth : ℕ
  step : ℝ
  eta : ℝ
  tau : ℝ
  pi : ℝ
  step_pos : 0 < step
  eta_pos : 0 < eta
  tau_pos : 0 < tau
  pi_pos : 0 < pi
  step_small : step ≤ c / 200
  depth_bound : Mmax < (depth : ℝ) * step
  eta_step : eta ≤ step / 16
  margin_budget : (depth : ℝ) * eta ≤ c / 14
  eta_terminal : eta ≤ c / 1000
  tau_terminal : tau ≤ c / 1000
  pi_terminal : pi ≤ c / 1000
  loss_budget : (depth : ℝ) * (40 * eta + tau + pi) < ε / 2

/-- Existence of all small parameters is simultaneous.  In particular the
number of recursive steps is fixed before choosing any localization loss. -/
theorem exists_descentBudget (Mmax c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    Nonempty (DescentBudget Mmax c ε) := by
  let d : ℝ := c / 200
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨D, hD⟩ := exists_nat_gt (2 + Mmax / d)
  let L : ℝ := (D : ℝ) + 1
  have hDn : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hL : 0 < L := by dsimp [L]; linarith
  let s : ℝ := min (d / 16) (min (c / (2000 * L)) (ε / (1000 * L)))
  have hs : 0 < s := by dsimp [s]; positivity
  have hsd : s ≤ d / 16 := min_le_left _ _
  have hsc : s ≤ c / (2000 * L) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hse : s ≤ ε / (1000 * L) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsc' : s * (2000 * L) ≤ c := (le_div_iff₀ (by positivity)).mp hsc
  have hse' : s * (1000 * L) ≤ ε := (le_div_iff₀ (by positivity)).mp hse
  have hdepth : Mmax < (D : ℝ) * d := by
    have hdiv : Mmax / d < D := by linarith
    exact (div_lt_iff₀ hd).mp hdiv
  have hsmall : s ≤ c / 1000 := by
    dsimp [L] at hsc'
    nlinarith [mul_nonneg hs.le hDn]
  refine ⟨⟨D, d, s, s, s, hd, hs, hs, hs, le_rfl, hdepth, hsd, ?_,
    hsmall, hsmall, hsmall, ?_⟩⟩
  · dsimp [L] at hsc'
    nlinarith [mul_nonneg hs.le hDn]
  · dsimp [L] at hse'
    nlinarith [mul_nonneg hs.le hDn]

/-- Accumulated row-length decrease along an arbitrary branch. -/
theorem chain_row_bound (row : ℕ → ℝ) (d : ℝ) (n : ℕ)
    (hdrop : ∀ k < n, row (k + 1) + d ≤ row k) :
    row n + (n : ℝ) * d ≤ row 0 := by
  revert hdrop
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hdrop
      have hp := ih (fun k hk => hdrop k (Nat.lt_succ_of_lt hk))
      have hn := hdrop n (Nat.lt_succ_self _)
      push_cast
      linarith

/-- The total column-and-label length stays in one fixed bounded range
despite the small enlargement caused by clipping at each step. -/
theorem chain_total_length_bound (length : ℕ → ℝ) (η : ℝ) (n : ℕ)
    (hgrowth : ∀ k < n, length (k + 1) ≤ length k + 11 * η) :
    length n ≤ length 0 + 11 * (n : ℝ) * η := by
  revert hgrowth
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hgrowth
      have hp := ih (fun k hk => hgrowth k (Nat.lt_succ_of_lt hk))
      have hn := hgrowth n (Nat.lt_succ_self _)
      push_cast
      linarith

/-- A common upper length range is fixed before the recursive nodes. -/
theorem budget_total_length_bound {Mmax c ε Fmax : ℝ}
    (b : DescentBudget Mmax c ε) (length : ℕ → ℝ) {n : ℕ}
    (hn : n ≤ b.depth) (hroot : length 0 ≤ Fmax)
    (hgrowth : ∀ k < n, length (k + 1) ≤ length k + 11 * b.eta) :
    length n ≤ Fmax + 11 * (b.depth : ℝ) * b.eta := by
  have hb := chain_total_length_bound length b.eta n hgrowth
  have hcast : (n : ℝ) ≤ b.depth := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hcast b.eta_pos.le
  linarith

/-- Nonnegative row lengths exclude every branch of the chosen depth. -/
theorem branch_length_lt_depth (row : ℕ → ℝ) {d Mmax : ℝ} {D n : ℕ}
    (hd : 0 < d) (hdepth : Mmax < (D : ℝ) * d)
    (hroot : row 0 ≤ Mmax) (hnonneg : 0 ≤ row n)
    (hdrop : ∀ k < n, row (k + 1) + d ≤ row k) : n < D := by
  have hb := chain_row_bound row d n hdrop
  by_contra hn
  have hDn : D ≤ n := Nat.le_of_not_gt hn
  have hcast : (D : ℝ) ≤ n := by exact_mod_cast hDn
  have hmul := mul_le_mul_of_nonneg_right hcast hd.le
  linarith

/-- Both canonical margins remain positive at every reachable depth. -/
theorem budget_margin {Mmax c ε : ℝ} (b : DescentBudget Mmax c ε)
    {h : ℕ} (hh : h ≤ b.depth) :
    c / 2 ≤ c - 7 * (h : ℝ) * b.eta := by
  exact depth_margin b.eta_pos.le (by exact_mod_cast hh) b.margin_budget

/-- The budget provides the paper's strict row decrease from the full
annular one-step inequality. -/
theorem budget_row_decrease {Mmax c ε M M' V ell : ℝ}
    (b : DescentBudget Mmax c ε)
    (hlarge : b.step ≤ V + ell)
    (hchild : 2 * (V + ell) - 8 * b.eta ≤ M - M') :
    b.step ≤ M - M' := by
  have hη := b.eta_step
  linarith

/-- Uniform strict gain for all three reflected terminal branches. -/
theorem terminal_ledger_saving {F M cnode c d η τ π : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M) (hnode : c / 2 ≤ cnode)
    (hd : d ≤ c / 200) (hη : η ≤ c / 1000)
    (hτ : τ ≤ c / 1000) (hπ : π ≤ c / 1000) :
    F - cnode + 5 * η / 3 + π ≤ F - c / 4 ∧
    F - 2 * cnode + 5 * d + 17 * η / 3 + τ + π ≤ F - c / 4 ∧
    F - M / 4 - 3 * cnode / 4 + 5 * d / 2 + 19 * η / 6 + τ / 2 + π ≤
      F - c / 4 := by
  constructor
  · linarith
  constructor <;> linarith

/-- The same terminal gain applies at every depth, including to any
subcollection of the original marks. -/
theorem budget_terminal_saving {Mmax c ε F M cnode : ℝ}
    (b : DescentBudget Mmax c ε) (hc : 0 < c) (hM : 0 ≤ M)
    {h : ℕ} (hh : h ≤ b.depth)
    (hnode : c - 7 * (h : ℝ) * b.eta ≤ cnode) :
    F - cnode + 5 * b.eta / 3 + b.pi ≤ F - c / 4 ∧
    F - 2 * cnode + 5 * b.step + 17 * b.eta / 3 + b.tau + b.pi ≤ F - c / 4 ∧
    F - M / 4 - 3 * cnode / 4 + 5 * b.step / 2 + 19 * b.eta / 6 +
      b.tau / 2 + b.pi ≤ F - c / 4 :=
  terminal_ledger_saving hc hM ((budget_margin b hh).trans hnode)
    b.step_small b.eta_terminal b.tau_terminal b.pi_terminal

/-- Every partial branch spends less than the fixed global loss allowance. -/
theorem budget_partial_loss {Mmax c ε : ℝ} (b : DescentBudget Mmax c ε)
    {h : ℕ} (hh : h ≤ b.depth) :
    (h : ℝ) * (40 * b.eta + b.tau + b.pi) < ε / 2 := by
  have hcast : (h : ℝ) ≤ b.depth := by exact_mod_cast hh
  have hnonneg : 0 ≤ 40 * b.eta + b.tau + b.pi := by
    have hη := b.eta_pos
    have hτ := b.tau_pos
    have hπ := b.pi_pos
    positivity
  exact (mul_le_mul_of_nonneg_right hcast hnonneg).trans_lt b.loss_budget

/-- A nonnegative initial row range forces at least one allocated step. -/
theorem budget_depth_pos {Mmax c ε : ℝ} (b : DescentBudget Mmax c ε)
    (hMmax : 0 ≤ Mmax) : 1 ≤ b.depth := by
  have hne : b.depth ≠ 0 := by
    intro hzero
    have hd := b.depth_bound
    rw [hzero] at hd
    norm_num at hd
    linarith
  exact Nat.one_le_iff_ne_zero.mpr hne

/-- The initial one-transform reduction fits in the other half of the
same total epsilon budget; its clipping loss is charged only once. -/
theorem budget_initial_loss {Mmax c ε : ℝ} (b : DescentBudget Mmax c ε)
    (hMmax : 0 ≤ Mmax) : 11 * b.eta + b.pi < ε / 2 := by
  have hD : (1 : ℝ) ≤ b.depth := by exact_mod_cast budget_depth_pos b hMmax
  have hη := b.eta_pos
  have hτ := b.tau_pos
  have hπ := b.pi_pos
  have hL : 0 ≤ 40 * b.eta + b.tau + b.pi := by positivity
  have hm := mul_le_mul_of_nonneg_right hD hL
  have hb := b.loss_budget
  nlinarith

/-- Initial and recursive losses together are strictly below ε. -/
theorem budget_combined_loss {Mmax c ε : ℝ} (b : DescentBudget Mmax c ε)
    (hMmax : 0 ≤ Mmax) :
    11 * b.eta + b.pi + (b.depth : ℝ) * (40 * b.eta + b.tau + b.pi) < ε := by
  have hi := budget_initial_loss b hMmax
  have hr := b.loss_budget
  linarith

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
