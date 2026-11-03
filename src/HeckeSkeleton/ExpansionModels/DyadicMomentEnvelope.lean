import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Repair of the dyadic source row cutoff

The physical shell is U < N(u) <= 2U.  A `MomentData.rows U` enumeration
has N(u) <= U by its defining `rows_spec`; these are incompatible for every
row in the physical shell.  The repair keeps all witness and prime scales
unchanged and increases only the moment's row exponent m to

    m(U) = 1 + log(2)/log(U),  so U^m(U) = 2U.

For U >= 2 this exponent belongs to the fixed compact interval [1,2].
All inverse/paired capacity inequalities with right side 1 remain valid,
and the moment cost U^(m(U)+eps) is exactly 2*U^(1+eps).
-/

set_option autoImplicit false
noncomputable section

namespace ExpansionRecipe

open scoped BigOperators

/-- Abstract form of the project's exact `MomentData.rows_spec`. -/
theorem no_row_both_above_and_below_cutoff {Row : Type*}
    (rowNorm : Row → ℝ) (rows : ℝ → Finset Row) (allowed : Row → Prop)
    (rows_spec : ∀ X u, u ∈ rows X ↔ allowed u ∧ rowNorm u ≤ X)
    {U : ℝ} {u : Row} (hU : U < rowNorm u) : u ∉ rows U := by
  intro hu
  exact (not_lt_of_ge (rows_spec U u |>.mp hu).2) hU

/-- A source asserting both incompatible memberships forces every purported
dyadic witness set to be empty.  No nonemptiness is assumed in this lemma. -/
theorem dyadic_witness_empty_of_wrong_cutoff {Row : Type*}
    (rowNorm : Row → ℝ) (rows : ℝ → Finset Row) (allowed : Row → Prop)
    (rows_spec : ∀ X u, u ∈ rows X ↔ allowed u ∧ rowNorm u ≤ X)
    (witness : Finset Row) (U : ℝ)
    (hdyadic : ∀ u ∈ witness, U < rowNorm u)
    (heligible : witness ⊆ rows U) : witness = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact no_row_both_above_and_below_cutoff rowNorm rows allowed rows_spec
    (hdyadic u hu) (heligible hu)

def dyadicMassExponent (U : ℝ) : ℝ := 1 + Real.log 2 / Real.log U

theorem dyadicMassExponent_gt_one {U : ℝ} (hU : 1 < U) :
    1 < dyadicMassExponent U := by
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  dsimp [dyadicMassExponent]
  exact lt_add_of_pos_right 1 (div_pos hlog2 hlogU)

theorem dyadicMassExponent_le_two {U : ℝ} (hU : 2 ≤ U) :
    dyadicMassExponent U ≤ 2 := by
  have hU1 : 1 < U := lt_of_lt_of_le (by norm_num) hU
  have hlogU : 0 < Real.log U := Real.log_pos hU1
  have hlog : Real.log 2 ≤ Real.log U := Real.log_le_log (by norm_num) hU
  have hdiv : Real.log 2 / Real.log U ≤ 1 :=
    (div_le_one hlogU).mpr hlog
  dsimp [dyadicMassExponent]
  linarith

/-- Exact envelope: the changed mass exponent changes no witness length. -/
theorem rpow_dyadicMassExponent {U : ℝ} (hU : 1 < U) :
    U ^ dyadicMassExponent U = 2 * U := by
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hlogU : Real.log U ≠ 0 := (Real.log_pos hU).ne'
  rw [dyadicMassExponent, Real.rpow_add hU0, Real.rpow_one]
  have hpow : U ^ (Real.log 2 / Real.log U) = 2 := by
    rw [Real.rpow_def_of_pos hU0]
    have hm : Real.log U * (Real.log 2 / Real.log U) = Real.log 2 := by
      field_simp
    rw [hm, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hpow, mul_comm]

/-- The row-enumeration overhead is the constant 2, not a scale loss. -/
theorem rpow_dyadicMassExponent_add {U : ℝ} (hU : 1 < U) (ε : ℝ) :
    U ^ (dyadicMassExponent U + ε) = 2 * U ^ (1 + ε) := by
  have hU0 : 0 < U := zero_lt_one.trans hU
  rw [Real.rpow_add hU0, rpow_dyadicMassExponent hU,
    Real.rpow_add hU0, Real.rpow_one]
  ring

/-- A literal dyadic shell now lies in the exhaustive moment enumeration. -/
theorem dyadic_row_mem_repaired_cutoff {Row : Type*}
    (rowNorm : Row → ℝ) (rows : ℝ → Finset Row) (allowed : Row → Prop)
    (rows_spec : ∀ X u, u ∈ rows X ↔ allowed u ∧ rowNorm u ≤ X)
    {U : ℝ} (hU : 1 < U) {u : Row} (ha : allowed u)
    (hupper : rowNorm u ≤ 2 * U) :
    u ∈ rows (U ^ dyadicMassExponent U) := by
  rw [rpow_dyadicMassExponent hU, rows_spec]
  exact ⟨ha, hupper⟩

/-- Existing strict inverse capacity margins are preserved, with room to
spare.  The right side gets larger when the shell envelope is repaired. -/
theorem inverse_capacity_preserved {U r z loss : ℝ}
    (hU : 1 < U) (hloss : 0 < loss)
    (h₁ : r + 2 * z ≤ 1 - 2 * loss)
    (h₂ : 2 * r + 8 * z ≤ 3 - 2 * loss) :
    r + 2 * z < dyadicMassExponent U ∧
      2 * r + 8 * z < 3 * dyadicMassExponent U := by
  have hm := dyadicMassExponent_gt_one hU
  constructor <;> linarith

theorem paired_capacity_preserved {U n₁ n₂ κ z : ℝ}
    (hU : 1 < U) (h : n₁ + n₂ + 6 * κ * z ≤ 1) :
    n₁ + n₂ + 6 * κ * z ≤ dyadicMassExponent U :=
  h.trans (dyadicMassExponent_gt_one hU).le

/-- Inverse moments at the repaired exponent retain the desired U^(1+eps)
bound after doubling the uniform constant. -/
theorem repaired_moment_bound {U E C ε H : ℝ}
    (hU : 1 < U)
    (h : E ≤ C * U ^ (dyadicMassExponent U + ε) * H) :
    E ≤ (2 * C) * U ^ (1 + ε) * H := by
  calc
    E ≤ C * U ^ (dyadicMassExponent U + ε) * H := h
    _ = (2 * C) * U ^ (1 + ε) * H := by
      rw [rpow_dyadicMassExponent_add hU ε]
      ring

end ExpansionRecipe

#print axioms ExpansionRecipe.no_row_both_above_and_below_cutoff
#print axioms ExpansionRecipe.dyadic_witness_empty_of_wrong_cutoff
#print axioms ExpansionRecipe.rpow_dyadicMassExponent
#print axioms ExpansionRecipe.dyadicMassExponent_le_two
#print axioms ExpansionRecipe.inverse_capacity_preserved
#print axioms ExpansionRecipe.repaired_moment_bound
