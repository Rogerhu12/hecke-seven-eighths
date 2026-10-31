import HeckeSkeleton.Moments.MOM_INV_INDUCTION.InductionGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# One base threshold for the finite induction

All fixed support constants, the fine dyadic width, and the finite
annular partition scales can be absorbed after choosing the descent
budget. The threshold is fixed before the arithmetic source and its
radial test vary. This file also records the exact stage capacities
used by backward induction on the actual node class.
-/

set_option autoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

/-- Any fixed positive power eventually absorbs a prescribed fixed
support or scalar constant, with an explicit common threshold. -/
theorem exists_uniform_power_threshold (delta C : ℝ)
    (hdelta : 0 < delta) (hC : 1 ≤ C) :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → C ≤ Z ^ delta := by
  let Z₀ := max 2 (C ^ delta⁻¹)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  refine ⟨Z₀, le_max_left _ _, ?_⟩
  intro Z hZ
  have hbase : C ^ delta⁻¹ ≤ Z := (le_max_right _ _).trans hZ
  have hb := Real.rpow_le_rpow (Real.rpow_nonneg hC0 _) hbase hdelta.le
  rw [← Real.rpow_mul hC0, inv_mul_cancel₀ hdelta.ne', Real.rpow_one] at hb
  exact hb

/-- The same threshold bounds every logarithmic scale shift in a
fixed compact multiplicative interval. -/
theorem abs_logb_le_of_power_bound {Z delta C s : ℝ}
    (hZ : 1 < Z) (hC : 1 ≤ C) (hCpower : C ≤ Z ^ delta)
    (hslow : C⁻¹ ≤ s) (hshigh : s ≤ C) : |Real.logb Z s| ≤ delta := by
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hsp : 0 < s := (inv_pos.mpr hCp).trans_le hslow
  have hu := Real.logb_le_logb_of_le hZ hsp (hshigh.trans hCpower)
  rw [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hu
  have hinv : s⁻¹ ≤ C := by
    simpa only [inv_inv] using (inv_le_inv₀ hsp (inv_pos.mpr hCp)).mpr hslow
  have hl := Real.logb_le_logb_of_le hZ (inv_pos.mpr hsp) (hinv.trans hCpower)
  rw [Real.logb_inv, Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- The fine mesh is strictly positive and leaves room inside the
provider's prescribed eta/32 width for the fixed smooth partition. -/
def fineMesh {Mmax c eps : ℝ} (b : DescentBudget Mmax c eps) : ℝ :=
  min 1 (b.eta / 128)

theorem fineMesh_spec {Mmax c eps : ℝ} (b : DescentBudget Mmax c eps) :
    0 < fineMesh b ∧ fineMesh b ≤ 1 ∧ fineMesh b ≤ b.eta / 128 := by
  exact ⟨lt_min zero_lt_one (div_pos b.eta_pos (by norm_num)),
    min_le_left _ _, min_le_right _ _⟩

theorem fineMesh_provider {Mmax c eps : ℝ} (b : DescentBudget Mmax c eps) :
    fineMesh b ∈ Set.Icc (0 : ℝ) 1 ∧ fineMesh b ≤ (b.eta / 2) / 32 := by
  obtain ⟨hp, h1, hsmall⟩ := fineMesh_spec b
  exact ⟨⟨hp.le, h1⟩, by linarith [b.eta_pos]⟩

/-- One threshold supplies both the fine dyadic width and all fixed
smooth-partition scale shifts. -/
theorem exists_fine_scale_threshold {Mmax c eps : ℝ}
    (b : DescentBudget Mmax c eps) (supportConstant : ℝ)
    (hC : 1 ≤ supportConstant) :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      2 ≤ Z ^ fineMesh b ∧ supportConstant ≤ Z ^ (b.eta / 8) ∧
      ∀ s : ℝ, supportConstant⁻¹ ≤ s → s ≤ supportConstant →
        |Real.logb Z s| ≤ b.eta / 8 := by
  obtain ⟨Z₁, hZ₁, hwidth⟩ := exists_uniform_power_threshold (fineMesh b) 2
    (fineMesh_spec b).1 (by norm_num)
  obtain ⟨Z₂, hZ₂, hsupport⟩ := exists_uniform_power_threshold (b.eta / 8)
    supportConstant (div_pos b.eta_pos (by norm_num)) hC
  refine ⟨max Z₁ Z₂, hZ₁.trans (le_max_left _ _), ?_⟩
  intro Z hZ
  have hz1 := (le_max_left Z₁ Z₂).trans hZ
  have hz2 := (le_max_right Z₁ Z₂).trans hZ
  have hz : 1 < Z := by linarith
  exact ⟨hwidth Z hz1, hsupport Z hz2,
    fun s hslo hshi => abs_logb_le_of_power_bound hz hC (hsupport Z hz2) hslo hshi⟩

def stageCapacity (Fmax eta : ℝ) (h : ℕ) : ℝ := Fmax + 11 * (h : ℝ) * eta
def stageMargin (c eta : ℝ) (h : ℕ) : ℝ := c - 7 * (h : ℝ) * eta
def stageRowBound (Mmax d : ℝ) (h : ℕ) : ℝ := Mmax - (h : ℝ) * d

theorem stageCapacity_succ (Fmax eta : ℝ) (h : ℕ) :
    stageCapacity Fmax eta (h + 1) = stageCapacity Fmax eta h + 11 * eta := by
  simp only [stageCapacity, Nat.cast_add, Nat.cast_one]
  ring

theorem stageMargin_succ (c eta : ℝ) (h : ℕ) :
    stageMargin c eta (h + 1) = stageMargin c eta h - 7 * eta := by
  simp only [stageMargin, Nat.cast_add, Nat.cast_one]
  ring

theorem stageRowBound_succ (Mmax d : ℝ) (h : ℕ) :
    stageRowBound Mmax d (h + 1) = stageRowBound Mmax d h - d := by
  simp only [stageRowBound, Nat.cast_add, Nat.cast_one]
  ring

/-- The one-step uniform constants use a single capacity for every
remaining depth, before any node or base is chosen. -/
theorem stageCapacity_le_common {Fmax eta : ℝ} {h D : ℕ}
    (heta : 0 ≤ eta) (hh : h ≤ D) :
    stageCapacity Fmax eta h ≤ max 1 (stageCapacity Fmax eta D) := by
  have hcast : (h : ℝ) ≤ (D : ℝ) := by exact_mod_cast hh
  apply le_trans _ (le_max_right _ _)
  dsimp only [stageCapacity]
  nlinarith [mul_le_mul_of_nonneg_right hcast heta]

theorem stageMargin_lower {Mmax c eps : ℝ}
    (b : DescentBudget Mmax c eps) {h : ℕ} (hh : h ≤ b.depth) :
    c / 2 ≤ stageMargin c b.eta h := budget_margin b hh

theorem stageRowBound_rank_iff (M Mmax d : ℝ) (h : ℕ) :
    M ≤ stageRowBound Mmax d h ↔ M + (h : ℝ) * d ≤ Mmax := by
  dsimp only [stageRowBound]
  constructor <;> intro hm <;> linarith

/-- A budget selected with a smaller numerical margin is a valid budget
for the original class.  The chosen depth and every loss stay identical. -/
def DescentBudget.enlargeMargin {Mmax c c' eps : ℝ}
    (b : DescentBudget Mmax c' eps) (hc : c' ≤ c) : DescentBudget Mmax c eps where
  depth := b.depth
  step := b.step
  eta := b.eta
  tau := b.tau
  pi := b.pi
  step_pos := b.step_pos
  eta_pos := b.eta_pos
  tau_pos := b.tau_pos
  pi_pos := b.pi_pos
  step_small := b.step_small.trans (div_le_div_of_nonneg_right hc (by norm_num))
  depth_bound := b.depth_bound
  eta_step := b.eta_step
  margin_budget := b.margin_budget.trans (div_le_div_of_nonneg_right hc (by norm_num))
  eta_terminal := b.eta_terminal.trans (div_le_div_of_nonneg_right hc (by norm_num))
  tau_terminal := b.tau_terminal.trans (div_le_div_of_nonneg_right hc (by norm_num))
  pi_terminal := b.pi_terminal.trans (div_le_div_of_nonneg_right hc (by norm_num))
  loss_budget := b.loss_budget

/-- The descent can be made as fine as any positive fixed allowance.
This choice still precedes all nodes and their radial tests. -/
theorem exists_descentBudget_small_step (Mmax c eps delta : ℝ)
    (hc : 0 < c) (heps : 0 < eps) (hdelta : 0 < delta) :
    ∃ b : DescentBudget Mmax c eps, b.step ≤ delta := by
  let c' := min c (200 * delta)
  have hc' : 0 < c' := lt_min hc (mul_pos (by norm_num) hdelta)
  obtain ⟨b⟩ := exists_descentBudget Mmax c' eps hc' heps
  refine ⟨b.enlargeMargin (min_le_left _ _), ?_⟩
  change b.step ≤ delta
  have hs := b.step_small
  have hsmall : c' ≤ 200 * delta := min_le_right _ _
  linarith

/-- The short reflected source uses the common surviving margin c/2.
Its stronger step allowance is included in the simultaneous choice. -/
theorem exists_terminal_descentBudget (Mmax c eps : ℝ)
    (hc : 0 < c) (heps : 0 < eps) :
    ∃ b : DescentBudget Mmax c eps, b.step ≤ (c / 2) / 1000 :=
  exists_descentBudget_small_step Mmax c eps ((c / 2) / 1000) hc heps (by positivity)

/-- Every stage can absorb the fixed annular shift c -> c-eta/2. -/
theorem stageMargin_half_eta_nonneg {Mmax c eps : ℝ}
    (b : DescentBudget Mmax c eps) (hc : 0 < c) {j : ℕ} (hj : j ≤ b.depth) :
    0 ≤ stageMargin c b.eta j - b.eta / 2 := by
  have hm := stageMargin_lower b hj
  have he := b.eta_terminal
  linarith

end HeckeSkeleton.Moments.MOM_INV_INDUCTION

end
