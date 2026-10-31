import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fixed ratio intervals from an `X / log X` asymptotic

This real analysis lemma is independent of the prime ideal theorem. Its
arithmetic instance is provided by `WindowPIT.Counting`.
-/

set_option autoImplicit false

namespace HeckeSkeleton.WindowPIT

open Filter Asymptotics
open scoped Topology

variable (P : ℝ → ℝ)

/-- Normalize a fixed positive dilation of a function asymptotic to `X / log X`
using the original, unscaled `X / log X`. -/
theorem scaled_div_tendsto
    (hP : P ~[atTop] (fun X : ℝ => X / Real.log X)) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun X : ℝ => P (t * X) / (X / Real.log X)) atTop (𝓝 t) := by
  have hnonzero : ∀ᶠ X : ℝ in atTop, X / Real.log X ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact div_ne_zero (ne_of_gt (lt_trans zero_lt_one hX))
      (ne_of_gt (Real.log_pos hX))
  have hprime : Tendsto (fun X : ℝ => P X / (X / Real.log X)) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hnonzero).mp hP
  have hscale : Tendsto (fun X : ℝ => t * X) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ht).mpr tendsto_id
  have hprimeScale :
      Tendsto (fun X : ℝ => P (t * X) / (t * X / Real.log (t * X)))
        atTop (𝓝 1) := hprime.comp hscale
  have hsmall : Tendsto (fun X : ℝ => Real.log t / Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hlogRatio :
      Tendsto (fun X : ℝ => Real.log (t * X) / Real.log X) atTop (𝓝 1) := by
    have hsum : Tendsto (fun X : ℝ => Real.log t / Real.log X + 1)
        atTop (𝓝 1) := by
      simpa only [zero_add] using hsmall.add tendsto_const_nhds
    apply hsum.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    symm
    rw [Real.log_mul (ne_of_gt ht) (ne_of_gt (lt_trans zero_lt_one hX)),
      add_div, div_self (ne_of_gt (Real.log_pos hX))]
  have hnormalizer :
      Tendsto (fun X : ℝ => t / (Real.log (t * X) / Real.log X)) atTop (𝓝 t) := by
    have hnum : Tendsto (fun _ : ℝ => t) atTop (𝓝 t) := tendsto_const_nhds
    have hdiv := hnum.div hlogRatio (by norm_num : (1 : ℝ) ≠ 0)
    have hfun :
        ((fun _ : ℝ => t) / (fun X : ℝ => Real.log (t * X) / Real.log X)) =
          (fun X : ℝ => t / (Real.log (t * X) / Real.log X)) := by
      funext X
      rfl
    rw [hfun, div_one] at hdiv
    exact hdiv
  have hproduct :
      Tendsto
        (fun X : ℝ =>
          (P (t * X) / (t * X / Real.log (t * X))) *
            (t / (Real.log (t * X) / Real.log X)))
        atTop (𝓝 t) := by
    simpa only [one_mul] using hprimeScale.mul hnormalizer
  apply hproduct.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hscale.eventually (eventually_gt_atTop (1 : ℝ))] with X hX htX
  field_simp [ne_of_gt ht, ne_of_gt (lt_trans zero_lt_one hX),
    ne_of_gt (Real.log_pos hX), ne_of_gt (Real.log_pos htX)] <;> ring

/-- Positive lower bounds for differences on fixed ratio intervals follow from
an `X / log X` asymptotic. No monotonicity hypothesis on `P` is needed. -/
theorem interval_lower_of_equivalent
    (hP : P ~[atTop] (fun X : ℝ => X / Real.log X))
    (a b : ℝ) (ha : 1 < a) (hab : a < b) :
    ∃ c X₀ : ℝ, 0 < c ∧ 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      c * X / Real.log X ≤ P (b * X) - P (a * X) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hb0 : 0 < b := lt_trans ha0 hab
  have hdiff :
      Tendsto
        (fun X : ℝ => (P (b * X) - P (a * X)) / (X / Real.log X))
        atTop (𝓝 (b - a)) := by
    simpa only [sub_div] using
      (scaled_div_tendsto P hP b hb0).sub (scaled_div_tendsto P hP a ha0)
  have hhalf : (b - a) / 2 < b - a := by linarith
  have hlower := (tendsto_order.mp hdiff).1 ((b - a) / 2) hhalf
  rcases eventually_atTop.mp hlower with ⟨X₁, hX₁⟩
  refine ⟨(b - a) / 2, max X₁ 2, by linarith, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right X₁ 2)
  · intro X hX
    have hX2 : 2 ≤ X := (le_max_right X₁ 2).trans hX
    have hden : 0 < X / Real.log X :=
      div_pos (by linarith) (Real.log_pos (by linarith))
    have hquot := (hX₁ X ((le_max_left X₁ 2).trans hX)).le
    have hbound := (le_div_iff₀ hden).mp hquot
    simpa only [mul_div_assoc] using hbound

end HeckeSkeleton.WindowPIT
