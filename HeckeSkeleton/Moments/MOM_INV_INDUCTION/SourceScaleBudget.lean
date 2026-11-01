import Expansion.DyadicSupport
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.UniformThreshold
import HeckeSkeleton.Moments.MOM_INV_STEP.SchwartzTestPartition

/-!
# Uniform scales and finite counts for the strict source seed

The original column cutoff has scale at most `H^(1-gap)`. Its exact
dyadic cap covers `2 H^(1-gap)` and is at most twice that number. Every
one of the fixed twenty-four smooth pieces consequently has scale at
most `32 H^(1-gap)`. A threshold chosen before the source absorbs this
fixed factor and leaves a gap of `gap/2` in its logarithmic length.

The squared number of dyadic pieces also costs an arbitrarily small
power, with the constant and threshold chosen before `H` and `gap`.
Scales below one remain available for the direct complete-row estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleBudget

open HeckeSkeleton.Moments.MOM_INV_STEP

def cap (H gap : ℝ) : ℕ := Expansion.Dyadic.dyadicCap (2 * H ^ (1 - gap))

def annularScale (i : SchwartzTestPartition.Index) : ℝ :=
  SchwartzTestPartition.scale (SchwartzTestPartition.exponent i)

def columnScale (i : SchwartzTestPartition.Index) (j : ℕ) : ℝ :=
  annularScale i * (2 : ℝ) ^ j

theorem annularScale_pos (i : SchwartzTestPartition.Index) : 0 < annularScale i :=
  SchwartzTestPartition.scale_pos _

theorem annularScale_le_eight (i : SchwartzTestPartition.Index) : annularScale i ≤ 8 := by
  have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2)
    (SchwartzTestPartition.exponent_bounds i).2
  exact h.trans (by norm_num)

theorem columnScale_pos (i : SchwartzTestPartition.Index) (j : ℕ) :
    0 < columnScale i j := mul_pos (annularScale_pos i) (by positivity)

/-- The ceiling cap increases a positive scale at least one by at most
one dyadic factor. -/
theorem two_pow_dyadicCap_le {R : ℝ} (hR : 1 ≤ R) :
    (2 : ℝ) ^ Expansion.Dyadic.dyadicCap R ≤ 2 * R := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquot : 0 ≤ Real.log R / Real.log 2 :=
    div_nonneg (Real.log_nonneg hR) hlog2.le
  have hceil := (Nat.ceil_lt_add_one hquot).le
  have hmul := mul_le_mul_of_nonneg_right hceil hlog2.le
  have hcancel : (Real.log R / Real.log 2 + 1) * Real.log 2 =
      Real.log R + Real.log 2 := by field_simp [hlog2.ne']
  rw [hcancel] at hmul
  have hlog : Real.log R + Real.log 2 = Real.log (2 * R) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hRp.ne']
    ring
  rw [hlog] at hmul
  exact (Real.pow_le_iff_le_log (by norm_num : (0 : ℝ) < 2)
    (mul_pos (by norm_num) hRp)).mpr hmul

theorem cap_bounds {H gap : ℝ} (hH : 1 ≤ H) (hgap : gap ≤ 1) :
    2 * H ^ (1 - gap) ≤ (2 : ℝ) ^ cap H gap ∧
      (2 : ℝ) ^ cap H gap ≤ 4 * H ^ (1 - gap) := by
  have hp : 1 ≤ H ^ (1 - gap) := Real.one_le_rpow hH (by linarith)
  constructor
  · exact Expansion.Dyadic.le_two_pow_dyadicCap (by positivity)
  · exact (two_pow_dyadicCap_le (by linarith : 1 ≤ 2 * H ^ (1 - gap))).trans_eq
      (by ring)

/-- This form applies to any fixed partition scale bounded by eight. -/
theorem scaled_dyadic_upper {H gap s : ℝ} {j : ℕ}
    (hH : 1 ≤ H) (hgap : gap ≤ 1) (hs0 : 0 ≤ s) (hs : s ≤ 8)
    (hj : j ≤ cap H gap) : s * (2 : ℝ) ^ j ≤ 32 * H ^ (1 - gap) := by
  have hpow := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj).trans
    (cap_bounds hH hgap).2
  calc
    _ ≤ s * (4 * H ^ (1 - gap)) := mul_le_mul_of_nonneg_left hpow hs0
    _ ≤ 8 * (4 * H ^ (1 - gap)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by ring

theorem columnScale_upper {H gap : ℝ} (hH : 1 ≤ H) (hgap : gap ≤ 1)
    (i : SchwartzTestPartition.Index) {j : ℕ} (hj : j ≤ cap H gap) :
    columnScale i j ≤ 32 * H ^ (1 - gap) :=
  scaled_dyadic_upper hH hgap (annularScale_pos i).le (annularScale_le_eight i) hj

/-- The logarithmic length is the actual dilated scale. The fixed
factor thirty-two is paid before taking the logarithm. -/
theorem scaled_dyadic_length {H gap s : ℝ} {j : ℕ}
    (hH : 1 < H) (hgap : gap ≤ 1) (hs0 : 0 ≤ s) (hs : s ≤ 8)
    (hj : j ≤ cap H gap) (hlarge : 1 ≤ s * (2 : ℝ) ^ j)
    (hfixed : 32 ≤ H ^ (gap / 2)) :
    0 ≤ Real.logb H (s * (2 : ℝ) ^ j) ∧
      Real.logb H (s * (2 : ℝ) ^ j) ≤ 1 - gap / 2 := by
  have hHp := zero_lt_one.trans hH
  have hu : s * (2 : ℝ) ^ j ≤ H ^ (1 - gap / 2) := by
    calc
      _ ≤ 32 * H ^ (1 - gap) := scaled_dyadic_upper hH.le hgap hs0 hs hj
      _ ≤ H ^ (gap / 2) * H ^ (1 - gap) :=
        mul_le_mul_of_nonneg_right hfixed (Real.rpow_nonneg hHp.le _)
      _ = _ := by rw [← Real.rpow_add hHp]; congr 1; ring
  refine ⟨Real.logb_nonneg hH hlarge, ?_⟩
  have hl := Real.logb_le_logb_of_le hH (zero_lt_one.trans_le hlarge) hu
  simpa only [Real.logb_rpow hHp (ne_of_gt hH)] using hl

theorem columnScale_length {H gap : ℝ} (hH : 1 < H) (hgap : gap ≤ 1)
    (i : SchwartzTestPartition.Index) {j : ℕ} (hj : j ≤ cap H gap)
    (hlarge : 1 ≤ columnScale i j) (hfixed : 32 ≤ H ^ (gap / 2)) :
    0 ≤ Real.logb H (columnScale i j) ∧
      Real.logb H (columnScale i j) ≤ 1 - gap / 2 :=
  scaled_dyadic_length hH hgap (annularScale_pos i).le (annularScale_le_eight i)
    hj hlarge hfixed

theorem columnScale_eq_rpow {H : ℝ} (hH : 1 < H)
    (i : SchwartzTestPartition.Index) (j : ℕ) :
    H ^ Real.logb H (columnScale i j) = columnScale i j :=
  Real.rpow_logb (zero_lt_one.trans hH) (ne_of_gt hH) (columnScale_pos i j)

/-- The number includes every endpoint `0 ≤ j ≤ cap`. Its logarithmic
bound is uniform for the whole allowed interval of gaps. -/
theorem count_le_log {H gap : ℝ} (hH : 1 ≤ H) (hgap0 : 0 ≤ gap) (hgap1 : gap ≤ 1) :
    (cap H gap : ℝ) + 1 ≤ Real.log H / Real.log 2 + 3 := by
  have hHp := zero_lt_one.trans_le hH
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 1 ≤ H ^ (1 - gap) := Real.one_le_rpow hH (by linarith)
  have hquot : 0 ≤ Real.log (2 * H ^ (1 - gap)) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) hlog2.le
  have hceil := (Nat.ceil_lt_add_one hquot).le
  have hlogH : 0 ≤ Real.log H / Real.log 2 := div_nonneg (Real.log_nonneg hH) hlog2.le
  calc
    (cap H gap : ℝ) + 1 ≤ Real.log (2 * H ^ (1 - gap)) / Real.log 2 + 2 := by
      change (⌈Real.log (2 * H ^ (1 - gap)) / Real.log 2⌉₊ : ℝ) + 1 ≤ _
      linarith
    _ = (1 - gap) * (Real.log H / Real.log 2) + 3 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (Real.rpow_pos_of_pos hHp _).ne', Real.log_rpow hHp]
      field_simp [hlog2.ne']
      ring
    _ ≤ Real.log H / Real.log 2 + 3 := by nlinarith

/-- The count constant is independent of both the source scale and
the gap. In particular the gap may later be fixed by the strict seed. -/
theorem exists_count_square_bound (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H gap : ℝ, 1 ≤ H → 0 ≤ gap → gap ≤ 1 →
      ((cap H gap : ℝ) + 1) ^ 2 ≤ C * H ^ eps := by
  let delta := eps / 2
  have hdelta : 0 < delta := div_pos heps (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C₀ := 3 + (delta * Real.log 2)⁻¹
  have hC₀ : 1 ≤ C₀ := by
    have hn := inv_nonneg.mpr (mul_pos hdelta hlog2).le
    dsimp only [C₀]
    linarith
  refine ⟨C₀ ^ 2, one_le_pow₀ hC₀, ?_⟩
  intro H gap hH hgap0 hgap1
  have hHp := zero_lt_one.trans_le hH
  have hp : 1 ≤ H ^ delta := Real.one_le_rpow hH hdelta.le
  have hlog := Real.log_le_rpow_div hHp.le hdelta
  have hc : (cap H gap : ℝ) + 1 ≤ C₀ * H ^ delta := by
    calc
      _ ≤ Real.log H / Real.log 2 + 3 := count_le_log hH hgap0 hgap1
      _ ≤ (H ^ delta / delta) / Real.log 2 + 3 * H ^ delta :=
        add_le_add (div_le_div_of_nonneg_right hlog hlog2.le)
          (by nlinarith)
      _ = _ := by dsimp only [C₀]; field_simp [hdelta.ne', hlog2.ne']; ring
  calc
    _ ≤ (C₀ * H ^ delta) ^ 2 := pow_le_pow_left₀ (by positivity) hc 2
    _ = C₀ ^ 2 * H ^ eps := by
      rw [mul_pow, ← Real.rpow_mul_natCast hHp.le]
      congr 1
      congr 1
      dsimp only [delta]
      ring

/-- A single threshold removes the count constant. It is uniform over
all gaps in `[0,1]`, not selected after a dyadic column is chosen. -/
theorem exists_count_square_threshold (eps : ℝ) (heps : 0 < eps) :
    ∃ H₀ : ℝ, 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ gap : ℝ,
      0 ≤ gap → gap ≤ 1 → ((cap H gap : ℝ) + 1) ^ 2 ≤ H ^ (eps / 2) := by
  obtain ⟨C, hC, hcount⟩ := exists_count_square_bound (eps / 4) (by positivity)
  obtain ⟨H₀, hH₀, hconstant⟩ := exists_uniform_power_threshold (eps / 4) C
    (by positivity) hC
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH gap hgap0 hgap1
  have hH1 : 1 ≤ H := by linarith
  calc
    _ ≤ C * H ^ (eps / 4) := hcount H gap hH1 hgap0 hgap1
    _ ≤ H ^ (eps / 4) * H ^ (eps / 4) :=
      mul_le_mul_of_nonneg_right (hconstant H hH) (by positivity)
    _ = H ^ (eps / 2) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hH1)]
      congr 1
      ring

/-- All scale and finite-count requirements of the strict source seed
hold at one threshold, before the original row or column is chosen. -/
theorem exists_uniform_scale_budget (gap eps : ℝ)
    (hgap0 : 0 < gap) (hgap1 : gap < 1) (heps : 0 < eps) :
    ∃ H₀ : ℝ, 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      (2 * H ^ (1 - gap) ≤ (2 : ℝ) ^ cap H gap ∧
        (2 : ℝ) ^ cap H gap ≤ 4 * H ^ (1 - gap)) ∧
      ((cap H gap : ℝ) + 1) ^ 2 ≤ H ^ (eps / 2) ∧
      ∀ (j : ℕ), j ≤ cap H gap → ∀ i : SchwartzTestPartition.Index,
        1 ≤ columnScale i j →
        0 ≤ Real.logb H (columnScale i j) ∧
          Real.logb H (columnScale i j) ≤ 1 - gap / 2 := by
  obtain ⟨H₁, hH₁, hfixed⟩ := exists_uniform_power_threshold (gap / 2) 32
    (by positivity) (by norm_num)
  obtain ⟨H₂, hH₂, hcount⟩ := exists_count_square_threshold eps heps
  refine ⟨max H₁ H₂, hH₁.trans (le_max_left _ _), ?_⟩
  intro H hH
  have hh1 := (le_max_left H₁ H₂).trans hH
  have hh2 := (le_max_right H₁ H₂).trans hH
  have hHgt : 1 < H := by linarith
  refine ⟨cap_bounds hHgt.le hgap1.le, hcount H hh2 gap hgap0.le hgap1.le, ?_⟩
  intro j hj i hlarge
  exact columnScale_length hHgt hgap1.le i hj hlarge (hfixed H hh1)

/-- The actual long-column lengths fit the initial source margins at
row length one, zero puncture length, and zero prime-mark length. -/
theorem initial_margins {gap n : ℝ} (hgap0 : 0 ≤ gap) (hgap1 : gap ≤ 1)
    (hn : n ≤ 1 - gap / 2) :
    n + 0 + 0 ≤ 1 - gap / 4 ∧ 2 * n + 6 * 0 ≤ 3 * 1 - gap / 4 := by
  constructor <;> linarith

theorem initial_pool_cap {H n : ℝ} (hH : 4 ≤ H) (hn : n ≤ 1) :
    4 * H ^ n ≤ H ^ (2 : ℝ) := by
  have hH1 : 1 ≤ H := by linarith
  calc
    _ ≤ H * H ^ (1 : ℝ) := by
      apply mul_le_mul hH (Real.rpow_le_rpow_of_exponent_le hH1 hn)
        (Real.rpow_nonneg (by linarith) _) (by linarith)
    _ = H ^ (2 : ℝ) := by simp only [Real.rpow_one, Real.rpow_two, pow_two]

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleBudget
