import HeckeSkeleton.LowFrozenCube.Valuations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast

/-!
# Local phase stability and full-cube coefficient normalization

The analytic local-table bound is an explicit input.  This file proves the
arithmetic stability of its phase digits, and the exact normalization which
turns a `1/N(x)` bound and an existing `1/N(n')` weight into `1/N(b)`.
-/

namespace HeckeSkeleton.LowFrozenCube

/-- The local phase digit in the ordinary-prime table, reduced modulo six. -/
def localPhaseDigit (j e : ℕ) : ℕ :=
  if e = 0 then (8 - j) % 6 else (4 + 2 * e) % 6

/-- On an allowed positive progression, adding a cube does not change the digit. -/
theorem localPhaseDigit_add_cube (j e x : ℕ) (he : 0 < e) :
    localPhaseDigit j (e + 3 * x) = localPhaseDigit j e := by
  have he0 : e ≠ 0 := by omega
  have hex0 : e + 3 * x ≠ 0 := by omega
  simp only [localPhaseDigit, if_neg he0, if_neg hex0]
  omega

theorem localPhaseDigit_frozen (j e : ℕ) (he : AdmissibleExponent e) :
    localPhaseDigit j e = localPhaseDigit j (frozenMin e) := by
  by_cases h0 : e = 0
  · simp [h0]
  · have hm : 0 < frozenMin e := by
      have hm0 : frozenMin e ≠ 0 := by
        intro h
        exact h0 ((frozenMin_eq_zero_iff e).mp h)
      omega
    calc
      localPhaseDigit j e =
          localPhaseDigit j (frozenMin e + 3 * frozenCubeExp e) := by
            rw [← frozenExponent_decomposition e he]
      _ = localPhaseDigit j (frozenMin e) :=
        localPhaseDigit_add_cube j (frozenMin e) (frozenCubeExp e) hm

/-- The residual coefficient after extracting the frozen majorant `C/N(b)`. -/
noncomputable def normalizedCubeCoefficient (Qx C : ℝ) (Ω : ℂ) : ℂ :=
  ((Qx : ℂ) / (C : ℂ)) * Ω

/-- Local-table decay becomes a unit-bounded coefficient.  This includes the
case of a zero frozen majorant, in which the original coefficient is zero. -/
theorem normalizedCubeCoefficient_norm_le (Qx C : ℝ) (Ω : ℂ)
    (hQx : 0 < Qx) (hC : 0 ≤ C) (hΩ : ‖Ω‖ ≤ C / Qx) :
    ‖normalizedCubeCoefficient Qx C Ω‖ ≤ 1 := by
  by_cases hC0 : C = 0
  · simp [normalizedCubeCoefficient, hC0]
  · have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    simp only [normalizedCubeCoefficient, norm_mul, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hQx, abs_of_pos hCp]
    calc
      Qx / C * ‖Ω‖ ≤ Qx / C * (C / Qx) :=
        mul_le_mul_of_nonneg_left hΩ (div_nonneg hQx.le hC)
      _ = 1 := by field_simp [ne_of_gt hCp, ne_of_gt hQx]

/-- The full-cube weight is exact: the old denominator `N(n')` and the
extracted `N(x)^(-1)` combine into `N(x)N(n')=N(b)`. -/
theorem normalizedCubeCoefficient_reassemble (Qx Qn C : ℝ) (Ω : ℂ)
    (hQx : 0 < Qx) (hQn : 0 < Qn) (hC : 0 ≤ C) (hΩ : ‖Ω‖ ≤ C / Qx) :
    Ω / (Qn : ℂ) = (C : ℂ) * normalizedCubeCoefficient Qx C Ω /
      ((Qx * Qn : ℝ) : ℂ) := by
  by_cases hC0 : C = 0
  · have hΩ0 : Ω = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm
      · simpa [hC0] using hΩ
      · exact norm_nonneg Ω
    simp [normalizedCubeCoefficient, hC0, hΩ0]
  · have hx : (Qx : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hQx
    have hn : (Qn : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hQn
    have hc : (C : ℂ) ≠ 0 := by exact_mod_cast hC0
    simp only [normalizedCubeCoefficient, Complex.ofReal_mul]
    field_simp [hx, hn, hc] <;> ring

#print axioms localPhaseDigit_frozen
#print axioms normalizedCubeCoefficient_norm_le
#print axioms normalizedCubeCoefficient_reassemble

end HeckeSkeleton.LowFrozenCube
