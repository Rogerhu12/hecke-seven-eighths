import ExpansionInterfaces.DyadicCount
import Mathlib.Tactic.FieldSimp

/-!
# Actual dyadic shell assignment with strict lower endpoints

The index is `ceil(log(r / base) / log 2) - 1`.  The ceiling is essential:
if r is an exact dyadic endpoint, it belongs to the preceding shell.
The resulting index lies in the concrete finite schedule counted by
`DyadicCount.lean`, and the shell lower endpoint is exactly `Z ^ d`.
-/

noncomputable section
namespace ExpansionInterfaces

/-- The interval `(j,j+1]` containing a positive real number. -/
def upperClosedIndex (x : ℝ) : ℕ := Nat.ceil x - 1

theorem upperClosedIndex_spec {x : ℝ} (hx : 0 < x) :
    (upperClosedIndex x : ℝ) < x ∧ x ≤ (upperClosedIndex x : ℝ) + 1 := by
  have hc : 1 ≤ Nat.ceil x := Nat.one_le_ceil_iff.mpr hx
  have heq : upperClosedIndex x + 1 = Nat.ceil x := by
    unfold upperClosedIndex
    omega
  have heqr : (upperClosedIndex x : ℝ) + 1 = Nat.ceil x := by
    exact_mod_cast heq
  have hlo := Nat.ceil_lt_add_one hx.le
  have hhi := Nat.le_ceil x
  constructor <;> linarith

/-- Index for `(2^j,2^(j+1)]`. -/
def dyadicIndex (ratio : ℝ) : ℕ :=
  upperClosedIndex (Real.log ratio / Real.log 2)

theorem dyadicIndex_spec {ratio : ℝ} (hratio : 1 < ratio) :
    (2 : ℝ) ^ dyadicIndex ratio < ratio ∧
      ratio ≤ (2 : ℝ) ^ (dyadicIndex ratio + 1) := by
  have hratio0 : 0 < ratio := by linarith
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < Real.log ratio / Real.log 2 := div_pos (Real.log_pos hratio) h2
  have hs := upperClosedIndex_spec hq
  change (dyadicIndex ratio : ℝ) < Real.log ratio / Real.log 2 ∧
    Real.log ratio / Real.log 2 ≤ (dyadicIndex ratio : ℝ) + 1 at hs
  constructor
  · apply (Real.pow_lt_iff_lt_log (by norm_num : (0 : ℝ) < 2) hratio0).mpr
    exact (lt_div_iff₀ h2).mp hs.1
  · apply (Real.le_pow_iff_log_le hratio0 (by norm_num : (0 : ℝ) < 2)).mpr
    have hh := (div_le_iff₀ h2).mp hs.2
    simpa only [Nat.cast_add, Nat.cast_one] using hh

theorem dyadicShell_bounds {base r : ℝ} (hbase : 0 < base) (hr : base < r) :
    base * (2 : ℝ) ^ dyadicIndex (r / base) < r ∧
      r ≤ base * (2 : ℝ) ^ (dyadicIndex (r / base) + 1) := by
  have hratio : 1 < r / base := (one_lt_div hbase).mpr hr
  have hh := dyadicIndex_spec hratio
  have heq : base * (r / base) = r := by field_simp [hbase.ne']
  constructor
  · exact (mul_lt_mul_of_pos_left hh.1 hbase).trans_eq heq
  · exact heq.symm.trans_le (mul_le_mul_of_nonneg_left hh.2 hbase.le)

/-- Exponent of the actual lower endpoint relative to Z. -/
def shellExponent (Z lower : ℝ) (j : ℕ) : ℝ :=
  lower + (j : ℝ) * Real.log 2 / Real.log Z

theorem shellExponent_identity {Z lower : ℝ} (hZ : 1 < Z) (j : ℕ) :
    Z ^ shellExponent Z lower j = Z ^ lower * (2 : ℝ) ^ j := by
  have hZ0 : 0 < Z := by linarith
  have hlog : Real.log Z ≠ 0 := (Real.log_pos hZ).ne'
  unfold shellExponent
  rw [Real.rpow_add hZ0]
  congr 1
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos hZ0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  field_simp [hlog]

theorem shellExponent_range {Z lower upper r : ℝ}
    (hZ : 1 < Z) (hr : Z ^ lower < r) (hu : r ≤ Z ^ upper) :
    lower ≤ shellExponent Z lower (dyadicIndex (r / Z ^ lower)) ∧
      shellExponent Z lower (dyadicIndex (r / Z ^ lower)) < upper := by
  have hZ0 : 0 < Z := by linarith
  have hbase : 0 < Z ^ lower := Real.rpow_pos_of_pos hZ0 _
  have hh := dyadicShell_bounds hbase hr
  constructor
  · unfold shellExponent
    have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hquot : 0 ≤ (dyadicIndex (r / Z ^ lower) : ℝ) * Real.log 2 / Real.log Z :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog2) (Real.log_pos hZ).le
    linarith
  · apply (Real.rpow_lt_rpow_left_iff hZ).mp
    rw [shellExponent_identity hZ]
    exact hh.1.trans_le hu

/-- No analytic estimate is used to bound the actual shell index. -/
theorem dyadicIndex_lt_count {Z lower upper r : ℝ}
    (hZ : 1 < Z) (hr : Z ^ lower < r) (hu : r ≤ Z ^ upper) :
    dyadicIndex (r / Z ^ lower) < dyadicCount ((upper - lower) / Real.log 2) Z := by
  have hs := (shellExponent_range hZ hr hu).2
  have hlogZ : 0 < Real.log Z := Real.log_pos hZ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfrac : (dyadicIndex (r / Z ^ lower) : ℝ) * Real.log 2 / Real.log Z <
      upper - lower := by
    unfold shellExponent at hs
    linarith
  have hmul := (div_lt_iff₀ hlogZ).mp hfrac
  have hj : (dyadicIndex (r / Z ^ lower) : ℝ) <
      ((upper - lower) / Real.log 2) * Real.log Z := by
    calc
      _ < ((upper - lower) * Real.log Z) / Real.log 2 := (lt_div_iff₀ hlog2).mpr hmul
      _ = _ := by ring
  have hfl : dyadicIndex (r / Z ^ lower) ≤
      Nat.floor (((upper - lower) / Real.log 2) * Real.log Z) := Nat.le_floor hj.le
  unfold dyadicCount
  omega

/-- The literal finite index used by the row assignment. -/
def boundedShellIndex (Z lower upper r : ℝ) (hZ : 1 < Z)
    (hr : Z ^ lower < r) (hu : r ≤ Z ^ upper) :
    Fin (dyadicCount ((upper - lower) / Real.log 2) Z) :=
  ⟨dyadicIndex (r / Z ^ lower), dyadicIndex_lt_count hZ hr hu⟩

theorem boundedShellIndex_spec (Z lower upper r : ℝ) (hZ : 1 < Z)
    (hr : Z ^ lower < r) (hu : r ≤ Z ^ upper) :
    let j := boundedShellIndex Z lower upper r hZ hr hu
    let d := shellExponent Z lower j.val
    lower ≤ d ∧ d < upper ∧ Z ^ d < r ∧ r ≤ 2 * Z ^ d := by
  dsimp only [boundedShellIndex]
  have hs := shellExponent_range hZ hr hu
  have hh := dyadicShell_bounds (Real.rpow_pos_of_pos (by linarith : 0 < Z) lower) hr
  refine ⟨hs.1, hs.2, ?_, ?_⟩
  · rw [shellExponent_identity hZ]
    exact hh.1
  · rw [shellExponent_identity hZ]
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh.2

/-- A dyadic endpoint has a unique upper-closed shell. -/
theorem dyadicShell_unique {base r : ℝ} (hbase : 0 < base) {i j : ℕ}
    (hi : base * (2 : ℝ) ^ i < r ∧ r ≤ base * (2 : ℝ) ^ (i + 1))
    (hj : base * (2 : ℝ) ^ j < r ∧ r ≤ base * (2 : ℝ) ^ (j + 1)) : i = j := by
  apply le_antisymm
  · by_contra h
    have hji : j + 1 ≤ i := by omega
    have hp : (2 : ℝ) ^ (j + 1) ≤ 2 ^ i :=
      pow_le_pow_right₀ (by norm_num) hji
    have hbound := hj.2.trans (mul_le_mul_of_nonneg_left hp hbase.le)
    exact (not_lt_of_ge hbound) hi.1
  · by_contra h
    have hij : i + 1 ≤ j := by omega
    have hp : (2 : ℝ) ^ (i + 1) ≤ 2 ^ j :=
      pow_le_pow_right₀ (by norm_num) hij
    have hbound := hi.2.trans (mul_le_mul_of_nonneg_left hp hbase.le)
    exact (not_lt_of_ge hbound) hj.1

/-- The actual retained prefix; every index has a legal shell exponent.
`dyadicCount` is only a convenient larger count bound, not the block type. -/
def shellCount (Z lower upper : ℝ) : ℕ :=
  Nat.ceil (((upper - lower) / Real.log 2) * Real.log Z)

theorem shellCount_le_dyadicCount (Z lower upper : ℝ) :
    shellCount Z lower upper ≤ dyadicCount ((upper - lower) / Real.log 2) Z := by
  have hh := Nat.lt_floor_add_one (((upper - lower) / Real.log 2) * Real.log Z)
  have hn : Nat.ceil (((upper - lower) / Real.log 2) * Real.log Z) ≤
      Nat.floor (((upper - lower) / Real.log 2) * Real.log Z) + 1 := by
    apply Nat.ceil_le.mpr
    simpa only [Nat.cast_add, Nat.cast_one] using hh.le
  unfold shellCount dyadicCount
  omega

/-- Every actual shell index satisfies the required range, including empty shells. -/
theorem actualShell_range {Z lower upper : ℝ} (hZ : 1 < Z)
    (j : Fin (shellCount Z lower upper)) :
    lower ≤ shellExponent Z lower j.val ∧ shellExponent Z lower j.val < upper := by
  have hlogZ : 0 < Real.log Z := Real.log_pos hZ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj : (j.val : ℝ) < ((upper - lower) / Real.log 2) * Real.log Z :=
    Nat.lt_ceil.mp j.isLt
  have hmul : (j.val : ℝ) * Real.log 2 < (upper - lower) * Real.log Z := by
    have hh := mul_lt_mul_of_pos_right hj hlog2
    have heq : (((upper - lower) / Real.log 2) * Real.log Z) * Real.log 2 =
        (upper - lower) * Real.log Z := by field_simp [hlog2.ne']
    exact hh.trans_eq heq
  have hfrac := (div_lt_iff₀ hlogZ).mpr hmul
  have hnonneg : 0 ≤ (j.val : ℝ) * Real.log 2 / Real.log Z :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog2.le) hlogZ.le
  unfold shellExponent
  constructor <;> linarith

theorem dyadicIndex_lt_shellCount {Z lower upper r : ℝ}
    (hZ : 1 < Z) (hr : Z ^ lower < r) (hu : r ≤ Z ^ upper) :
    dyadicIndex (r / Z ^ lower) < shellCount Z lower upper := by
  have hs := (shellExponent_range hZ hr hu).2
  have hlogZ : 0 < Real.log Z := Real.log_pos hZ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfrac : (dyadicIndex (r / Z ^ lower) : ℝ) * Real.log 2 / Real.log Z <
      upper - lower := by
    unfold shellExponent at hs
    linarith
  have hmul := (div_lt_iff₀ hlogZ).mp hfrac
  apply Nat.lt_ceil.mpr
  calc
    (dyadicIndex (r / Z ^ lower) : ℝ) <
        ((upper - lower) * Real.log Z) / Real.log 2 := (lt_div_iff₀ hlog2).mpr hmul
    _ = _ := by ring

/-- Canonical row assignment into the actual retained shell prefix. -/
def actualShellIndex (Z lower upper r : ℝ) (hZ : 1 < Z)
    (hr : Z ^ lower < r) (hu : r ≤ Z ^ upper) : Fin (shellCount Z lower upper) :=
  ⟨dyadicIndex (r / Z ^ lower), dyadicIndex_lt_shellCount hZ hr hu⟩

theorem actualShellIndex_spec (Z lower upper r : ℝ) (hZ : 1 < Z)
    (hr : Z ^ lower < r) (hu : r ≤ Z ^ upper) :
    let j := actualShellIndex Z lower upper r hZ hr hu
    let d := shellExponent Z lower j.val
    lower ≤ d ∧ d < upper ∧ Z ^ d < r ∧ r ≤ 2 * Z ^ d := by
  exact boundedShellIndex_spec Z lower upper r hZ hr hu

theorem shellCount_subpower {Z lower upper η : ℝ}
    (hZ : 1 ≤ Z) (hlu : lower ≤ upper) (hη : 0 < η) :
    (shellCount Z lower upper : ℝ) ≤
      (2 + ((upper - lower) / Real.log 2) / η) * Z ^ η := by
  have hc : 0 ≤ (upper - lower) / Real.log 2 :=
    div_nonneg (sub_nonneg.mpr hlu) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hcount : (shellCount Z lower upper : ℝ) ≤
      dyadicCount ((upper - lower) / Real.log 2) Z := by
    exact_mod_cast shellCount_le_dyadicCount Z lower upper
  exact hcount.trans (dyadicCount_le hc hZ hη)

/-- A shell and a choice from a fixed finite buffered-bin schedule.
The finite `Choice` is fixed before Z and T.  It can encode height and
buffer-center indices; amplitude labels and witness subdivisions are separate. -/
abbrev RetainedBlockSchedule (Choice : Type*) (Z lower upper : ℝ) :=
  Fin (shellCount Z lower upper) × Choice

theorem card_retainedBlockSchedule (Choice : Type*) [Fintype Choice]
    (Z lower upper : ℝ) :
    Fintype.card (RetainedBlockSchedule Choice Z lower upper) =
      shellCount Z lower upper * Fintype.card Choice := by
  simp [RetainedBlockSchedule]

/-- The actual block count has no height loss.  This is the exact shape
required by EX-BLOCK-COUNT, once blocks use this finite schedule. -/
theorem retainedBlockSchedule_subpower (Choice : Type*) [Fintype Choice]
    {Z lower upper η : ℝ} (hZ : 1 ≤ Z) (hlu : lower ≤ upper) (hη : 0 < η) :
    (Fintype.card (RetainedBlockSchedule Choice Z lower upper) : ℝ) ≤
      ((Fintype.card Choice : ℝ) * (2 + ((upper - lower) / Real.log 2) / η)) *
        Z ^ η := by
  rw [card_retainedBlockSchedule]
  push_cast
  have hh := mul_le_mul_of_nonneg_right (shellCount_subpower hZ hlu hη)
    (Nat.cast_nonneg (Fintype.card Choice) : (0 : ℝ) ≤ Fintype.card Choice)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh

end ExpansionInterfaces
