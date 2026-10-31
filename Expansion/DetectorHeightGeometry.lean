import ExpansionInterfaces.BufferedHeights
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A fixed detector budget and the physical buffered heights

The internal losses and positive height ceiling are chosen before the
external exponent tau. The same exponent tau controls the Fourier radius;
only the source zero-height envelope uses 32*tau. This distinction keeps
the actual common frequency inside the next physical height rectangle.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

/-- An explicit numerical choice for all three analytic detector budgets.
The degree A is the fixed actual Hecke height degree. -/
theorem exists_detector_numerical_budget (A η : ℝ) (hA : 0 ≤ A) (hη : 0 < η) :
    ∃ e ε ceiling : ℝ,
      0 < e ∧ e < 1 / 1000 ∧ 0 < ε ∧ 0 < ceiling ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        A * (32 * τ) ≤ 1 ∧
        132 * e + 2 * ε + A * ε * (32 * τ) ≤ η / 4 ∧
        12 * e + 2 * ε + A * (32 * τ) * (1 + ε) ≤ η / 4 := by
  let e : ℝ := min (η / 4096) (1 / 2000)
  let c : ℝ := min (1 / (64 * (A + 1))) (η / (2048 * (A + 1)))
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have heη : e ≤ η / 4096 := min_le_left _ _
  have heSmall : e ≤ 1 / 2000 := min_le_right _ _
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨e, e, c, he, by linarith, he, hc, ?_⟩
  intro τ hτ hτc
  have hτone : τ ≤ 1 / (64 * (A + 1)) := hτc.trans (min_le_left _ _)
  have hτη : τ ≤ η / (2048 * (A + 1)) := hτc.trans (min_le_right _ _)
  have hτone' := (le_div_iff₀ (by positivity : 0 < 64 * (A + 1))).mp hτone
  have hτη' := (le_div_iff₀ (by positivity : 0 < 2048 * (A + 1))).mp hτη
  have hdegree : A * (32 * τ) ≤ 1 / 2 := by nlinarith
  have hloss : A * (32 * τ) ≤ η / 64 := by nlinarith
  have hforward := mul_le_mul_of_nonneg_left hdegree he.le
  have hsmall : 1 + e ≤ 2 := by linarith
  have hreflected := mul_le_mul hloss hsmall (by positivity : 0 ≤ 1 + e)
    (by positivity : 0 ≤ η / 64)
  refine ⟨by linarith, ?_, ?_⟩ <;> nlinarith

/-- A shell in [1/16,1] keeps the Fourier radius below the original
physical cutoff, while 32*tau supplies a square-height source envelope. -/
theorem shell_height_powers (Z d τ : ℝ) (hZ : 1 ≤ Z)
    (hd : 1 / 16 ≤ d) (hd' : d ≤ 1) (hτ : 0 ≤ τ) :
    (Z ^ d) ^ τ ≤ Z ^ τ ∧ (Z ^ τ) ^ (2 : ℕ) ≤ (Z ^ d) ^ (32 * τ) := by
  have hZnonneg : 0 ≤ Z := zero_le_one.trans hZ
  constructor
  · rw [← Real.rpow_mul hZnonneg]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)
  · rw [← Real.rpow_mul_natCast hZnonneg, ← Real.rpow_mul hZnonneg]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num; nlinarith)

/-- Every selected zero fits the source's power-height envelope once the
external physical height exceeds the fixed finite height multiplicity. -/
theorem selected_height_power_envelope (N i : ℕ) (hi : i ≤ N)
    (Z d τ : ℝ) (hZ : 1 ≤ Z) (hd : 1 / 16 ≤ d) (hd' : d ≤ 1) (hτ : 0 ≤ τ)
    (hT : 3 * (N : ℝ) ≤ Z ^ τ) :
    ExpansionInterfaces.selectedHeight i (Z ^ τ) ≤ (Z ^ d) ^ (32 * τ) := by
  have hTnonneg := Real.rpow_nonneg (zero_le_one.trans hZ) τ
  have hi' : (i : ℝ) ≤ N := by exact_mod_cast hi
  have hb := mul_le_mul_of_nonneg_right
    (show 3 * (i : ℝ) ≤ Z ^ τ by linarith) hTnonneg
  exact (show ExpansionInterfaces.selectedHeight i (Z ^ τ) ≤ (Z ^ τ) ^ (2 : ℕ)
    by unfold ExpansionInterfaces.selectedHeight; nlinarith).trans
      (shell_height_powers Z d τ hZ hd hd' hτ).2

/-- The upper rectangle uses a fixed finite constant and the same power
height; its constant precedes all rowwise choices. -/
theorem upper_height_power_envelope (N i : ℕ) (hi : i ≤ N)
    (Z d τ : ℝ) (hZ : 1 ≤ Z) (hd : 1 / 16 ≤ d) (hd' : d ≤ 1) (hτ : 0 ≤ τ) :
    2 + ExpansionInterfaces.upperHeight i (Z ^ τ) ≤
      (3 * ((N : ℝ) + 1) + 2) * (Z ^ d) ^ (32 * τ) := by
  have hT : 1 ≤ Z ^ τ := Real.one_le_rpow hZ hτ
  have hi' : (i : ℝ) ≤ N := by exact_mod_cast hi
  have hiT := mul_le_mul_of_nonneg_right hi' (by positivity : 0 ≤ Z ^ τ)
  have hbase : 2 + ExpansionInterfaces.upperHeight i (Z ^ τ) ≤
      (3 * ((N : ℝ) + 1) + 2) * (Z ^ τ) := by
    unfold ExpansionInterfaces.upperHeight
    push_cast
    nlinarith
  have hp : Z ^ τ ≤ (Z ^ d) ^ (32 * τ) :=
    (show Z ^ τ ≤ (Z ^ τ) ^ (2 : ℕ) by nlinarith).trans
      (shell_height_powers Z d τ hZ hd hd' hτ).2
  exact hbase.trans (mul_le_mul_of_nonneg_left hp (by positivity))

/-- The complete worst-case Fourier shift, contour height and 3/2 margin
fit inside the next physical rectangle. -/
theorem physical_fourier_padding (i : ℕ) (U T τ : ℝ)
    (hU : 0 ≤ U) (hT : 1 ≤ T) (hUT : U ^ τ ≤ T) :
    ExpansionInterfaces.selectedHeight i T +
        2 * Real.pi * (U ^ τ / (8 * Real.pi + 8)) + T + 3 / 2 ≤
      ExpansionInterfaces.upperHeight i T := by
  have hden : 0 < 8 * Real.pi + 8 := by positivity
  have hradius : U ^ τ / (8 * Real.pi + 8) ≤ T / (8 * Real.pi + 8) :=
    div_le_div_of_nonneg_right hUT hden.le
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hfreq := mul_le_mul_of_nonneg_left hradius hpi
  have hquarter : 2 * Real.pi * (T / (8 * Real.pi + 8)) ≤ T / 4 := by
    rw [mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  unfold ExpansionInterfaces.selectedHeight ExpansionInterfaces.upperHeight
  push_cast
  linarith

#print axioms exists_detector_numerical_budget
#print axioms shell_height_powers
#print axioms physical_fourier_padding

end Expansion.Project
