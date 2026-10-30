import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import HeckeGeneral.Analysis.RowEulerRational

/-!
# Independent algebra and region audit for TASK_HB_EULER

This file imports a byte-for-byte copy of the supplied project's
`HeckeGeneral/Analysis/RowEulerRational.lean` and checks its actual rational
factor. It also checks the real inequalities printed in `TInputRanges.lean`.
The complete project and its arithmetic input data are not imported here.
In particular, this is not a proof of `TRowEulerInput` or
`HighExceptionalEulerControl`.

The local source formula is equation `unramified-P` in the supplied project's
paper.  All rational identities below are proved with their denominators
explicitly assumed nonzero.  The real-region predicate is a literal copy of
the six real inequalities in the task, with a distinct namespace and name.
-/

namespace HBEulerRegionAudit

noncomputable section

open HeckeGeneral.ThetaSkeleton.Physical

/-- The local source factor displayed in the paper. -/
def localSource (q v V W D E : ℂ) : ℂ :=
  1 / (1 - V) + W / (1 - W) +
    E / (1 - E) * ((1 - v) / (1 - V) + W) -
    D / (1 - E) * (1 + (q - 1) * W * V / (1 - V))

/-- The normalization prescribed by the three displayed Hecke factors. -/
def localCorrection (q v V W D E : ℂ) : ℂ :=
  localSource q v V W D E * (1 - V) * (1 - W) / (1 - D)

/-- The complete numerator of the correction minus one. -/
def errorNumerator (q v V W D E : ℂ) : ℂ :=
  -V * W + E * (1 - v + v * W - W ^ 2 + W ^ 2 * V) +
    D * (V + W - q * V * W + (q - 1) * W ^ 2 * V) - D * E

theorem localCorrection_sub_one (q v V W D E : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0)
    (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    localCorrection q v V W D E - 1 =
      errorNumerator q v V W D E / ((1 - D) * (1 - E)) := by
  unfold localCorrection localSource errorNumerator
  field_simp [hV, hW, hD, hE]
  ring

/-- The mixed `V W` term remains when both source-tail parameters vanish. -/
theorem localCorrection_zeroDE (q v V W : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) :
    localCorrection q v V W 0 0 = 1 - V * W := by
  unfold localCorrection localSource
  field_simp [hV, hW]
  ring

/-- A second mixed term remains on the `W = E = 0` slice. -/
theorem localCorrection_zeroWE (q v V D : ℂ)
    (hV : 1 - V ≠ 0) (hD : 1 - D ≠ 0) :
    localCorrection q v V 0 D 0 = 1 + D * V / (1 - D) := by
  unfold localCorrection localSource
  field_simp [hV, hD]
  ring

/-- The audit literal is exactly the rational factor in the supplied source. -/
theorem literal_eq_project_rational (q v V W D E : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0)
    (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    localCorrection q v V W D E = rowEulerRationalValue q v V W D E := by
  simpa only [localCorrection, localSource, one_div] using
    rowEulerLiteral_eq_rational q v V W D E hV hW hE hD

/-- The source's cancelled formula requires only its two genuine denominators. -/
theorem project_rational_sub_one (q v V W D E : ℂ)
    (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    rowEulerRationalValue q v V W D E - 1 =
      errorNumerator q v V W D E / ((1 - D) * (1 - E)) := by
  unfold rowEulerRationalValue errorNumerator
  field_simp [hD, hE]
  ring

theorem project_rational_zeroDE (q v V W : ℂ) :
    rowEulerRationalValue q v V W 0 0 = 1 - V * W := by
  unfold rowEulerRationalValue
  ring

theorem project_rational_zeroWE (q v V D : ℂ) (hD : 1 - D ≠ 0) :
    rowEulerRationalValue q v V 0 D 0 = 1 + D * V / (1 - D) := by
  unfold rowEulerRationalValue
  field_simp [hD]
  ring

/-- Exact remainder after removing the positive `D V` model term. -/
theorem project_rational_sub_dvModel (q v V W D E : ℂ)
    (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    rowEulerRationalValue q v V W D E - (1 + D * V / (1 - D)) =
      (-V * W + E * (1 - v + v * W - W ^ 2 + W ^ 2 * V - D + D * V) +
        D * W * (1 - q * V + (q - 1) * W * V)) /
          ((1 - D) * (1 - E)) := by
  unfold rowEulerRationalValue
  field_simp [hD, hE]
  ring

/-- The six inequalities copied from the task's `rowEulerRegion`. -/
def taskRealRegion (σ ω ζ : ℝ) : Prop :=
  1 / 2 < σ ∧ 0 < ω ∧ 0 < ζ ∧ 1 < σ + ω ∧
    5 / 6 < σ + ζ ∧ 2 < σ + ω + 6 * ζ

/-- The corresponding complex region; distinct from the unavailable project definition. -/
def taskComplexRegion (s w z : ℂ) : Prop :=
  taskRealRegion s.re w.re z.re

theorem positive_w_slice (ω : ℝ) :
    taskRealRegion 10 ω (1 / 10) ↔ 0 < ω := by
  constructor
  · exact fun h => h.2.1
  · intro hω
    refine ⟨by norm_num, hω, by norm_num, ?_, by norm_num, ?_⟩ <;> linarith

theorem positive_complex_w_slice (w : ℂ) :
    taskComplexRegion 10 w (1 / 10) ↔ 0 < w.re := by
  simpa [taskComplexRegion] using positive_w_slice w.re

/-- The task region does not force the summability exponent of `V W` above one. -/
theorem vw_region_counterexample :
    taskRealRegion 10 (1 / 10) (1 / 10) ∧
      (1 / 10 : ℝ) + 6 * (1 / 10) = 7 / 10 ∧
      (1 / 10 : ℝ) + 6 * (1 / 10) < 1 := by
  norm_num [taskRealRegion]

/-- It does not force the summability exponent of `D V` above one either. -/
theorem dv_region_counterexample :
    taskRealRegion (9 / 10) 2 (1 / 100) ∧
      (9 / 10 : ℝ) + 6 * (1 / 100) = 24 / 25 ∧
      (9 / 10 : ℝ) + 6 * (1 / 100) < 1 := by
  norm_num [taskRealRegion]

/-- The same missing `D V` exponent persists with a large positive `w`. -/
theorem dv_large_w_region_counterexample :
    taskRealRegion (9 / 10) 4 (1 / 100) ∧
      (9 / 10 : ℝ) + 6 * (1 / 100) = 24 / 25 ∧
      (9 / 10 : ℝ) + 6 * (1 / 100) < 1 := by
  norm_num [taskRealRegion]

theorem dv_large_w_slice (ω : ℝ) :
    taskRealRegion (9 / 10) ω (1 / 100) ↔ 26 / 25 < ω := by
  unfold taskRealRegion
  constructor
  · rintro ⟨hσ, hω, hζ, hσω, hσζ, hσωζ⟩
    linarith
  · intro hω
    refine ⟨by norm_num, ?_, by norm_num, ?_, by norm_num, ?_⟩ <;> linarith

/-- A candidate corrected convergence region, retaining the task inequalities. -/
def safeRealRegion (σ ω ζ : ℝ) : Prop :=
  taskRealRegion σ ω ζ ∧ 1 < ω + 6 * ζ ∧ 1 < σ + 6 * ζ

/-- Exact membership conditions on the task's dynamic line. -/
theorem dynamic_line_membership (a e : ℝ) :
    taskRealRegion (a + 16 * e) (1 - a - 6 * e) (17 / 50) ↔
      0 < e ∧ 1 / 2 - 16 * e < a ∧ a < 1 - 6 * e := by
  unfold taskRealRegion
  constructor
  · rintro ⟨hσ, hω, hζ, hσω, hσζ, hσωζ⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨he, ha₁, ha₂⟩
    refine ⟨?_, ?_, by norm_num, ?_, ?_, ?_⟩ <;> linarith

/-- The dynamic line automatically satisfies both missing mixed inequalities. -/
theorem dynamic_line_mixed_exponents (a e : ℝ)
    (h : taskRealRegion (a + 16 * e) (1 - a - 6 * e) (17 / 50)) :
    1 < (1 - a - 6 * e) + 6 * (17 / 50 : ℝ) ∧
      1 < (a + 16 * e) + 6 * (17 / 50 : ℝ) := by
  rcases h with ⟨hσ, hω, hζ, hσω, hσζ, hσωζ⟩
  constructor <;> linarith

/-- Restricting to the candidate corrected region does not change the dynamic line. -/
theorem safe_dynamic_line_iff (a e : ℝ) :
    safeRealRegion (a + 16 * e) (1 - a - 6 * e) (17 / 50) ↔
      0 < e ∧ 1 / 2 - 16 * e < a ∧ a < 1 - 6 * e := by
  constructor
  · intro h
    exact (dynamic_line_membership a e).mp h.1
  · intro h
    have hr := (dynamic_line_membership a e).mpr h
    exact ⟨hr, dynamic_line_mixed_exponents a e hr⟩

/-- A frequently used sufficient bin range for the corrected dynamic region. -/
theorem safe_dynamic_line_of_bin_range (a e : ℝ)
    (he : 0 < e) (ha : 1 / 2 ≤ a) (ha' : a < 1 - 6 * e) :
    safeRealRegion (a + 16 * e) (1 - a - 6 * e) (17 / 50) := by
  apply (safe_dynamic_line_iff a e).mpr
  exact ⟨he, by linarith, ha'⟩

end

#print axioms localCorrection_sub_one
#print axioms localCorrection_zeroDE
#print axioms localCorrection_zeroWE
#print axioms literal_eq_project_rational
#print axioms project_rational_sub_one
#print axioms project_rational_zeroDE
#print axioms project_rational_zeroWE
#print axioms project_rational_sub_dvModel
#print axioms positive_w_slice
#print axioms positive_complex_w_slice
#print axioms vw_region_counterexample
#print axioms dv_region_counterexample
#print axioms dv_large_w_region_counterexample
#print axioms dv_large_w_slice
#print axioms dynamic_line_membership
#print axioms dynamic_line_mixed_exponents
#print axioms safe_dynamic_line_iff
#print axioms safe_dynamic_line_of_bin_range

end HBEulerRegionAudit
