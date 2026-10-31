import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# The terminal ledger of the paired fourth-moment induction

These are the numerical deductions in the latter half of §4.8.  The hypotheses
are the displayed local ledgers, with every aggregate boundary error retained.
In particular, a numerical exceptional-row saving is not used as a substitute
for the analytic estimate for the whole centered coefficient.

The width lemmas apply to actual widths after clipping.  The final two choice
lemmas implement the prescribed order: choose the coarse floor and step first,
then the boundary precision, mesh, and local loss after the finite depth is
known.
-/

namespace HeckeSkeleton.Moments.EngineInduction

/-- The two-transform width formula, before clipping or boundary errors. -/
theorem child_width_drop
    {M M' J g g₂ t₂ σ : ℝ}
    (hwidth : M' = M + J - g - g₂ + t₂)
    (henlarge : max J 0 + σ ≤ g) (hcommon : t₂ ≤ g₂) :
    M' ≤ M - σ := by
  linarith [le_max_left J 0]

/-- The strict width decrease survives the complete aggregate boundary error. -/
theorem actual_child_width_drop
    {M M' Mact J g g₂ t₂ σ boundary : ℝ}
    (hwidth : M' = M + J - g - g₂ + t₂)
    (henlarge : max J 0 + σ ≤ g) (hcommon : t₂ ≤ g₂)
    (hactual : Mact ≤ M' + boundary) (hboundary : boundary ≤ σ / 2) :
    Mact ≤ M - σ / 2 := by
  have hnominal := child_width_drop hwidth henlarge hcommon
  linarith

/-- One greedy prefix pays for the complete actual child defect.  Its
single overshoot contributes at most one mesh width, uniformly up to κ=1. -/
theorem slot_removal_budget
    {defect w pool allowance κ η boundary : ℝ}
    (hdefect : defect ≤ 6 * (w + pool) + boundary)
    (hallowance : w + pool ≤ allowance) (hκ : κ ≤ 1) (hη : 0 ≤ η) :
    defect / 6 + κ * η ≤ allowance + boundary / 6 + η := by
  have hmesh := mul_le_mul_of_nonneg_right hκ hη
  nlinarith

/-- Positive slots cost at most one sixth of a small terminal width. -/
theorem small_width_slot_cost
    {n₁ n₂ z κ M ρ : ℝ} (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂)
    (hcapacity : n₁ + n₂ + 6 * κ * z ≤ M) (hwidth : M ≤ ρ) :
    κ * z ≤ ρ / 6 := by
  linarith

/-- The equal-product residue cancellation pays for the final divisor
extraction.  All four lengths stay formal, including subunit rectangles. -/
theorem centered_divisor_saving
    {tMinus r₁ r₂ r omega₂ : ℝ} (hratio : tMinus - r₂ ≤ omega₂) :
    tMinus - r₁ - r₂ - max (r - r₁) 0 ≤ omega₂ - r := by
  linarith [le_max_left (r - r₁) 0]

/-- The exceptional penalty is minimized at `v = M/4`.  This stronger form
is valid even when `A < M`, before replacing the result by its positive part. -/
theorem centered_exceptional_excess_le_sub (A M v : ℝ) :
    A - 5 * M / 6 - 2 * v / 3 - max (M / 4 - v) 0 ≤ A - M := by
  linarith [le_max_left (M / 4 - v) 0, le_max_right (M / 4 - v) 0]

theorem centered_exceptional_excess_le (A M v : ℝ) :
    A - 5 * M / 6 - 2 * v / 3 - max (M / 4 - v) 0 ≤ max (A - M) 0 :=
  (centered_exceptional_excess_le_sub A M v).trans (le_max_left _ _)

/-- The exceptional local ledger closes the uncentered range. -/
theorem uncentered_exceptional_excess_le
    {A M F₁ F₂ c w b₂ σ boundary : ℝ}
    (hcore : A ≤ 5 * M / 6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb₂ : 0 ≤ b₂)
    (hF₁ : 2 * (c + w) / 3 - 3 * σ - boundary ≤ F₁)
    (hF₂ : 2 * b₂ / 3 ≤ F₂) :
    A - 5 * M / 6 - F₁ - F₂ ≤ 3 * σ + boundary := by
  linarith

/-- The smaller second extraction fits inside its mean length. -/
theorem smaller_extraction_le_mean (c₂ d₂ : ℝ) :
    min c₂ d₂ ≤ (c₂ + d₂) / 2 := by
  linarith [min_le_left c₂ d₂, min_le_right c₂ d₂]

/-- Combine the two local losses with the cancellation on the side having
the smaller extraction.  The aggregate boundary error is charged once. -/
theorem centered_exceptional_terminal
    {A M F₁ F₂ c w c₂ d₂ σ boundary : ℝ}
    (hF₁ : 2 * (c + w) / 3 - 3 * σ - boundary ≤ F₁)
    (hF₂ : 2 * ((c₂ + d₂) / 2) / 3 ≤ F₂) :
    A - 5 * M / 6 - F₁ - F₂ - max (M / 4 - (c + w + min c₂ d₂)) 0 ≤
      max (A - M) 0 + 3 * σ + boundary := by
  have hsmall := smaller_extraction_le_mean c₂ d₂
  have hcenter := centered_exceptional_excess_le A M (c + w + min c₂ d₂)
  linarith

/-- Positive-slot capacity makes the terminal excess nonpositive before
the local error.  This uses the full endpoint `κ = 1` as well. -/
theorem positive_capacity_total_length
    {n₁ n₂ z κ M : ℝ} (hz : 0 ≤ z) (hκ : 3 / 4 ≤ κ)
    (hcapacity : n₁ + n₂ + 6 * κ * z ≤ M) :
    n₁ + n₂ + z ≤ M := by
  have hzκ : (3 / 4 : ℝ) * z ≤ κ * z := mul_le_mul_of_nonneg_right hκ hz
  nlinarith

theorem centered_positive_terminal
    {A M F₁ F₂ c w c₂ d₂ σ boundary : ℝ}
    (hcapacity : A ≤ M)
    (hF₁ : 2 * (c + w) / 3 - 3 * σ - boundary ≤ F₁)
    (hF₂ : 2 * ((c₂ + d₂) / 2) / 3 ≤ F₂) :
    A - 5 * M / 6 - F₁ - F₂ - max (M / 4 - (c + w + min c₂ d₂)) 0 ≤
      3 * σ + boundary := by
  have h := centered_exceptional_terminal (A := A) (M := M) hF₁ hF₂
  rwa [max_eq_right (sub_nonpos.mpr hcapacity), zero_add] at h

/-- The unrestricted zero-slot branch is reflected into the padded core.
Only its padding is added to the terminal excess. -/
theorem centered_zero_slot_terminal
    {A M F₁ F₂ c w c₂ d₂ σ boundary padding : ℝ}
    (hpadding : 0 ≤ padding) (hcore : A ≤ M + padding)
    (hF₁ : 2 * (c + w) / 3 - 3 * σ - boundary ≤ F₁)
    (hF₂ : 2 * ((c₂ + d₂) / 2) / 3 ≤ F₂) :
    A - 5 * M / 6 - F₁ - F₂ - max (M / 4 - (c + w + min c₂ d₂)) 0 ≤
      padding + 3 * σ + boundary := by
  have h := centered_exceptional_terminal (A := A) (M := M) hF₁ hF₂
  have hmax : max (A - M) 0 ≤ padding := max_le (by linarith) hpadding
  linarith

/-- The same-band comparison has a margin of `M/6` for zero slots. -/
theorem zero_slot_comparison_margin
    {A M Acomp boundary : ℝ} (hcentered : 5 * M / 6 < A)
    (hcomparison : Acomp ≤ 3 * M / 2 - A + boundary) :
    Acomp < 5 * M / 6 - (M / 6 - boundary) := by
  linarith

/-- In a centered positive-slot state, capacity forces `z < M/20`.
This bound is uniform for all `κ` in the required interval. -/
theorem centered_positive_slot_length
    {A M z κ : ℝ} (hz : 0 ≤ z) (hκ : 3 / 4 ≤ κ)
    (hcentered : 5 * M / 6 < A)
    (hcapacity : A + (6 * κ - 1) * z ≤ M) :
    z < M / 20 := by
  have hzκ : (3 / 4 : ℝ) * z ≤ κ * z := mul_le_mul_of_nonneg_right hκ hz
  nlinarith

/-- The reflected comparison returns to the earlier uncentered stage.
The `M/15` margin accounts for both live-slot contributions. -/
theorem positive_slot_comparison_margin
    {A M z Acomp boundary : ℝ} (hz : z < M / 20)
    (hcentered : 5 * M / 6 < A)
    (hcomparison : Acomp ≤ 3 * M / 2 - A + 2 * z + boundary) :
    Acomp < 5 * M / 6 - (M / 15 - boundary) := by
  linarith

/-- Telescoping only the strict two-transform calls.  Same-band comparison
is accounted for by the stage coordinate of the dependency order. -/
theorem width_chain_drop (width : ℕ → ℝ) (σ : ℝ) (n : ℕ) :
    (∀ j < n, width (j + 1) ≤ width j - σ / 2) →
      width n + (n : ℝ) * σ / 2 ≤ width 0 := by
  induction n with
  | zero =>
      intro _
      simp
  | succ n ih =>
      intro hstep
      have hprev := ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self n)))
      have hlast := hstep n (Nat.lt_succ_self n)
      simp only [Nat.cast_succ] at *
      linarith

/-- The paper's finite depth bound for strict calls, including its two
spare boundary stages. -/
theorem finite_strict_call_count
    (width : ℕ → ℝ) {σ Mmax : ℝ} (hσ : 0 < σ) (n : ℕ)
    (hstep : ∀ j < n, width (j + 1) ≤ width j - σ / 2)
    (hstart : width 0 ≤ Mmax) (hend : 0 ≤ width n) :
    n ≤ 2 + ⌈2 * Mmax / σ⌉₊ := by
  have hdrop := width_chain_drop width σ n hstep
  have hn : (n : ℝ) ≤ 2 * Mmax / σ := (le_div_iff₀ hσ).mpr (by linarith)
  have hceil : n ≤ ⌈2 * Mmax / σ⌉₊ := by
    exact_mod_cast hn.trans (Nat.le_ceil (2 * Mmax / σ))
  omega

/-- Coarse parameters are fixed before the depth and the slot mesh.
The explicit choice leaves more than half of the requested coarse budget. -/
theorem exists_coarse_loss_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ padding σ : ℝ, 0 < ρ ∧ 0 < padding ∧ 0 < σ ∧
      ρ + padding + ρ / 6 + 3 * σ + 5 * σ / 3 < ε / 4 := by
  refine ⟨ε / 64, ε / 64, ε / 64, by positivity, by positivity, by positivity, ?_⟩
  linarith

/-- A choice with the additional floor/step/padding hierarchy required by
the comparison construction.  The fine analytic parameters still come later. -/
theorem exists_ordered_coarse_loss_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ padding σ : ℝ, 0 < ρ ∧ 0 < padding ∧ 0 < σ ∧
      16 * σ ≤ ρ ∧ 16 * padding ≤ σ ∧
      ρ + padding + ρ / 6 + 3 * σ + 5 * σ / 3 < ε / 4 := by
  refine ⟨ε / 16, ε / 4096, ε / 256,
    by positivity, by positivity, by positivity, ?_, ?_, ?_⟩ <;> linarith

/-- The fine precision and the mesh are chosen after the finite depth.
`localLoss` is the aggregate per-stage small-power loss. -/
theorem exists_fine_loss_parameters {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (D : ℕ) :
    ∃ ξ η localLoss : ℝ, 0 < ξ ∧ 0 < η ∧ 0 < localLoss ∧
      ξ ≤ σ / 2 ∧ η < σ / 6 ∧
      (D : ℝ) * (ξ + η + localLoss) < ε / 2 := by
  let δ : ℝ := min (σ / 12) (ε / (12 * ((D : ℝ) + 1)))
  have hD : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hden : 0 < 12 * ((D : ℝ) + 1) := by positivity
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hε hden)
  have hσδ : δ ≤ σ / 12 := min_le_left _ _
  have hεδ : δ * (12 * ((D : ℝ) + 1)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  refine ⟨δ, δ, δ, hδ, hδ, hδ, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · nlinarith

/-- Choose the coarse geometry before evaluating its finite recursion depth,
then choose the precision, mesh and local loss.  The single unmultiplied
terminal boundary error is included in the final budget as well.  Taking
`depth σ = 4 * (widthBand σ W + 1)` instantiates the ordered engine. -/
theorem exists_ordered_induction_loss_parameters {ε : ℝ} (hε : 0 < ε)
    (depth : ℝ → ℕ) :
    ∃ ρ padding σ ξ η localLoss : ℝ,
      0 < ρ ∧ 0 < padding ∧ 0 < σ ∧
      16 * σ ≤ ρ ∧ 16 * padding ≤ σ ∧
      0 < ξ ∧ 0 < η ∧ 0 < localLoss ∧
      ξ ≤ σ / 2 ∧ η < σ / 6 ∧
      ρ + padding + ρ / 6 + 3 * σ + 5 * σ / 3 + ξ +
        (depth σ : ℝ) * (ξ + η + localLoss) < ε := by
  obtain ⟨ρ, padding, σ, hρ, hp, hσ, hstep, hpadding, hcoarse⟩ :=
    exists_ordered_coarse_loss_parameters hε
  let D : ℕ := depth σ
  let δ : ℝ := min (σ / 12) (ε / (12 * ((D : ℝ) + 1)))
  have hD : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hden : 0 < 12 * ((D : ℝ) + 1) := by positivity
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hε hden)
  have hσδ : δ ≤ σ / 12 := min_le_left _ _
  have hεδ : δ * (12 * ((D : ℝ) + 1)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hacc : δ + (D : ℝ) * (δ + δ + δ) < ε / 2 := by
    nlinarith
  refine ⟨ρ, padding, σ, δ, δ, δ, hρ, hp, hσ, hstep, hpadding,
    hδ, hδ, hδ, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · change ρ + padding + ρ / 6 + 3 * σ + 5 * σ / 3 + δ +
      (D : ℝ) * (δ + δ + δ) < ε
    linarith

end HeckeSkeleton.Moments.EngineInduction
