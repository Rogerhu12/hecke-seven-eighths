import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# The finite order of the paired fourth-moment induction

The order in revised §4.8 is (zero/positive slots, width band,
first/second proof stage).  In particular, comparison is an earlier-stage
call, not a strict-width call.  Removing every slot may return to any of
the already completed zero-slot bands.

This file only supplies the order.  It assumes no analytic estimate.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

/-- `slots = 0` means zero slots; `stage = 0` is the first proof stage.
There are `bands + 1` width bands in each slot regime. -/
structure State (bands : ℕ) where
  slots : Fin 2
  band : Fin (bands + 1)
  stage : Fin 2

namespace State

variable {bands : ℕ}

def rank (s : State bands) : ℕ :=
  (if s.slots.val = 0 then 0 else 2 * (bands + 1)) +
    2 * s.band.val + s.stage.val

/-- The three strictly earlier kinds of call permitted by §4.8. -/
def Earlier (child parent : State bands) : Prop :=
  child.slots.val < parent.slots.val ∨
    (child.slots = parent.slots ∧
      (child.band.val < parent.band.val ∨
        (child.band = parent.band ∧ child.stage.val < parent.stage.val)))

theorem rank_lt_bound (s : State bands) : s.rank < 4 * (bands + 1) := by
  have hb := s.band.isLt
  have hs := s.stage.isLt
  unfold rank
  split_ifs <;> omega

theorem earlier_rank_lt {child parent : State bands}
    (h : child.Earlier parent) : child.rank < parent.rank := by
  have hc := child.band.isLt
  have hp := parent.band.isLt
  have hcs := child.stage.isLt
  have hps := parent.stage.isLt
  have hcm := child.slots.isLt
  have hpm := parent.slots.isLt
  rcases h with hm | ⟨hm, hb | ⟨hb, hs⟩⟩
  · have hcz : child.slots.val = 0 := by omega
    have hpz : parent.slots.val ≠ 0 := by omega
    simp only [rank, hcz, hpz, ite_true, ite_false]
    omega
  · unfold rank
    rw [hm]
    split_ifs <;> omega
  · unfold rank
    rw [hm, hb]
    split_ifs <;> omega

theorem earlier_wellFounded : WellFounded (Earlier (bands := bands)) :=
  (measure rank).wf.mono (fun _ _ h => earlier_rank_lt h)

/-- Strong induction on the actual ordered state, including comparison
and the switch from positive to zero slots. -/
theorem induction {P : State bands → Prop}
    (step : ∀ s, (∀ child, child.Earlier s → P child) → P s) : ∀ s, P s := by
  intro s
  exact earlier_wellFounded.induction s step

theorem zero_before_positive {child parent : State bands}
    (hc : child.slots.val = 0) (hp : parent.slots.val = 1) :
    child.Earlier parent := by
  left
  omega

theorem smaller_band {child parent : State bands}
    (hm : child.slots = parent.slots) (hb : child.band.val < parent.band.val) :
    child.Earlier parent := Or.inr ⟨hm, Or.inl hb⟩

theorem comparison {child parent : State bands}
    (hm : child.slots = parent.slots) (hb : child.band = parent.band)
    (hc : child.stage.val = 0) (hp : parent.stage.val = 1) :
    child.Earlier parent := by
  exact Or.inr ⟨hm, Or.inr ⟨hb, by omega⟩⟩

end State

/-- Bands of length `σ / 4`, as in the paper. -/
def widthBand (σ M : ℝ) : ℕ := ⌊4 * M / σ⌋₊

theorem widthBand_mono {σ M₁ M₂ : ℝ} (hσ : 0 < σ) (hM : M₁ ≤ M₂) :
    widthBand σ M₁ ≤ widthBand σ M₂ := by
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_right (by linarith) hσ.le

/-- The actual post-clipping decrease `σ / 2` crosses a whole width band.
No assertion that merely `M' < M` changes the band is used. -/
theorem widthBand_strict {σ child parent : ℝ} (hσ : 0 < σ)
    (hc : 0 ≤ child) (hdrop : child + σ / 2 ≤ parent) :
    widthBand σ child < widthBand σ parent := by
  have hcq : 0 ≤ 4 * child / σ := div_nonneg (by linarith) hσ.le
  have hgap : 4 * child / σ + 2 ≤ 4 * parent / σ := by
    apply (le_div_iff₀ hσ).2
    have he : (4 * child / σ + 2) * σ = 4 * child + 2 * σ := by
      rw [add_mul, div_mul_cancel₀ _ hσ.ne']
    rw [he]
    linarith
  have hup := Nat.lt_floor_add_one (4 * parent / σ)
  apply (Nat.floor_lt hcq).2
  dsimp only [widthBand] at *
  linarith

/-- Turn bounded real widths into the finite band component. -/
def boundedBand (σ M W : ℝ) (hσ : 0 < σ) (hM : M ≤ W) :
    Fin (widthBand σ W + 1) :=
  ⟨widthBand σ M, Nat.lt_succ_of_le (widthBand_mono hσ hM)⟩

/-- A strict child with the same slot regime is earlier, regardless of
which of the two stages it needs. -/
theorem strict_child_earlier {bands : ℕ} {σ Mc Mp : ℝ}
    {child parent : State bands} (hσ : 0 < σ) (hMc : 0 ≤ Mc)
    (hdrop : Mc + σ / 2 ≤ Mp) (hmode : child.slots = parent.slots)
    (hc : child.band.val = widthBand σ Mc)
    (hp : parent.band.val = widthBand σ Mp) : child.Earlier parent := by
  apply State.smaller_band hmode
  rw [hc, hp]
  exact widthBand_strict hσ hMc hdrop

end HeckeSkeleton.Moments.EngineInduction
