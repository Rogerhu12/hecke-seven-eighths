import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.IntegralRecursion

/-!
# Finite branches with continuous child parameters

The authoritative paired engine conclusion has finitely many branches,
with two actual children under the same positive kernel in each branch.
Only the two numerical child energies need be integrable. There is no
measurable-space requirement on the type of polynomial models, and no
pushforward of the kernel to that type is needed.

The proof keeps the full parameter integral. Strong induction is applied
pointwise to the actual child models, and then integrated on the original
parameter space. The two half weights charge each common kernel once.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace HeckeSkeleton.Moments.EngineInduction

universe u v

/-- One node's actual local reduction. Keeping it local permits a genuine
base leaf, a reflection branch, and a two-transform branch to be assembled
by cases, without relabelling a base estimate as a transform zero term. -/
structure BranchedIntegralAt {X : Type u} {Ω : Type v} {bands : ℕ}
    [MeasurableSpace Ω] (value : X → ℝ) (schedule : X → State bands) (x : X) where
  branches : ℕ
  kernel : Fin branches → Measure Ω
  finite : ∀ b, IsFiniteMeasure (kernel b)
  left : Fin branches → Ω → X
  right : Fin branches → Ω → X
  remainder : ℝ
  left_integrable : ∀ b, Integrable (fun ξ => value (left b ξ)) (kernel b)
  right_integrable : ∀ b, Integrable (fun ξ => value (right b ξ)) (kernel b)
  left_earlier : ∀ b, ∀ᵐ ξ ∂kernel b,
    (schedule (left b ξ)).Earlier (schedule x)
  right_earlier : ∀ b, ∀ᵐ ξ ∂kernel b,
    (schedule (right b ξ)).Earlier (schedule x)
  estimate : value x ≤ remainder +
    ∑ b, ((∫ ξ, value (left b ξ) ∂kernel b) +
      ∫ ξ, value (right b ξ) ∂kernel b) / 2

/-- A true leaf retains its actual energy as the remainder and has no
children. Its required absolute or reflection estimate is proved separately. -/
def BranchedIntegralAt.terminal
    {X : Type u} {Ω : Type v} {bands : ℕ} [MeasurableSpace Ω]
    (value : X → ℝ) (schedule : X → State bands) (x : X) :
    BranchedIntegralAt (Ω := Ω) value schedule x where
  branches := 0
  kernel b := Fin.elim0 b
  finite b := Fin.elim0 b
  left b := Fin.elim0 b
  right b := Fin.elim0 b
  remainder := value x
  left_integrable b := Fin.elim0 b
  right_integrable b := Fin.elim0 b
  left_earlier b := Fin.elim0 b
  right_earlier b := Fin.elim0 b
  estimate := by simp

/-- The normalized AM--GM form of a finite-branch engine step. -/
structure BranchedIntegralStep {X : Type u} {Ω : Type v} {bands : ℕ}
    [MeasurableSpace Ω] (value : X → ℝ) (schedule : X → State bands) where
  branches : X → ℕ
  kernel : ∀ x, Fin (branches x) → Measure Ω
  finite : ∀ x b, IsFiniteMeasure (kernel x b)
  left : ∀ x, Fin (branches x) → Ω → X
  right : ∀ x, Fin (branches x) → Ω → X
  remainder : X → ℝ
  left_integrable : ∀ x b, Integrable (fun ξ => value (left x b ξ)) (kernel x b)
  right_integrable : ∀ x b, Integrable (fun ξ => value (right x b ξ)) (kernel x b)
  left_earlier : ∀ x b, ∀ᵐ ξ ∂kernel x b,
    (schedule (left x b ξ)).Earlier (schedule x)
  right_earlier : ∀ x b, ∀ᵐ ξ ∂kernel x b,
    (schedule (right x b ξ)).Earlier (schedule x)
  estimate : ∀ x, value x ≤ remainder x +
    ∑ b, ((∫ ξ, value (left x b ξ) ∂kernel x b) +
      ∫ ξ, value (right x b ξ) ∂kernel x b) / 2

namespace BranchedIntegralStep

variable {X : Type u} {Ω : Type v} {bands : ℕ} [MeasurableSpace Ω]
variable {value : X → ℝ} {schedule : X → State bands}

/-- Assemble locally constructed branches while retaining their literal
remainder, kernel, and child maps. -/
def ofLocal (localStep : ∀ x, BranchedIntegralAt (Ω := Ω) value schedule x) :
    BranchedIntegralStep (Ω := Ω) value schedule where
  branches x := (localStep x).branches
  kernel x := (localStep x).kernel
  finite x := (localStep x).finite
  left x := (localStep x).left
  right x := (localStep x).right
  remainder x := (localStep x).remainder
  left_integrable x := (localStep x).left_integrable
  right_integrable x := (localStep x).right_integrable
  left_earlier x := (localStep x).left_earlier
  right_earlier x := (localStep x).right_earlier
  estimate x := (localStep x).estimate

/-- The branch count is unrestricted; only this complete mass is charged. -/
def mass (step : BranchedIntegralStep (Ω := Ω) value schedule) (x : X) : ℝ :=
  ∑ b, (step.kernel x b).real Set.univ

theorem mass_nonneg (step : BranchedIntegralStep (Ω := Ω) value schedule) (x : X) :
    0 ≤ step.mass x :=
  Finset.sum_nonneg fun _ _ => measureReal_nonneg

/-- Pointwise induction and integration on the original parameter space.
No measurable child-model map or measurable structure on `X` is assumed. -/
theorem bound (step : BranchedIntegralStep (Ω := Ω) value schedule)
    (terminal mass : ℝ) (ht : 0 ≤ terminal) (hm : 0 ≤ mass)
    (hterminal : ∀ x, step.remainder x ≤ terminal)
    (hmass : ∀ x, step.mass x ≤ mass) :
    ∀ x, value x ≤ terminal * (1 + mass) ^ ((schedule x).rank + 1) := by
  have hone : 1 ≤ 1 + mass := by linarith
  have hmain : ∀ n : ℕ, ∀ x, (schedule x).rank = n →
      value x ≤ terminal * (1 + mass) ^ (n + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      have hearlier (y : X) (hy : (schedule y).Earlier (schedule x)) :
          value y ≤ terminal * (1 + mass) ^ n := by
        have hylt : (schedule y).rank < n := by
          rw [← hx]
          exact State.earlier_rank_lt hy
        exact (ih _ hylt y rfl).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hone (Nat.succ_le_of_lt hylt)) ht)
      have hbranch (b : Fin (step.branches x)) :
          ((∫ ξ, value (step.left x b ξ) ∂step.kernel x b) +
            ∫ ξ, value (step.right x b ξ) ∂step.kernel x b) / 2 ≤
              (step.kernel x b).real Set.univ * (terminal * (1 + mass) ^ n) := by
        letI : IsFiniteMeasure (step.kernel x b) := step.finite x b
        have hl := integral_mono_ae (step.left_integrable x b)
          (integrable_const (terminal * (1 + mass) ^ n))
          ((step.left_earlier x b).mono fun ξ hξ => hearlier _ hξ)
        have hr := integral_mono_ae (step.right_integrable x b)
          (integrable_const (terminal * (1 + mass) ^ n))
          ((step.right_earlier x b).mono fun ξ hξ => hearlier _ hξ)
        simp only [integral_const, smul_eq_mul] at hl hr
        linarith
      have hpower : 1 ≤ (1 + mass) ^ n := one_le_pow₀ hone
      have hnonneg : 0 ≤ terminal * (1 + mass) ^ n :=
        mul_nonneg ht (pow_nonneg (by linarith) _)
      calc
        value x ≤ step.remainder x +
            ∑ b, ((∫ ξ, value (step.left x b ξ) ∂step.kernel x b) +
              ∫ ξ, value (step.right x b ξ) ∂step.kernel x b) / 2 := step.estimate x
        _ ≤ terminal + ∑ b,
            (step.kernel x b).real Set.univ * (terminal * (1 + mass) ^ n) :=
          add_le_add (hterminal x) (Finset.sum_le_sum fun b _ => hbranch b)
        _ = terminal + step.mass x * (terminal * (1 + mass) ^ n) := by
          rw [← Finset.sum_mul] <;> rfl
        _ ≤ terminal + mass * (terminal * (1 + mass) ^ n) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right (hmass x) hnonneg)
        _ ≤ terminal * (1 + mass) ^ n + mass * (terminal * (1 + mass) ^ n) :=
          add_le_add
            (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower ht) le_rfl
        _ = terminal * (1 + mass) ^ (n + 1) := by rw [pow_succ]; ring
  intro x
  exact hmain _ x rfl

theorem uniform_rank_bound (step : BranchedIntegralStep (Ω := Ω) value schedule)
    (terminal mass : ℝ) (ht : 0 ≤ terminal) (hm : 0 ≤ mass)
    (hterminal : ∀ x, step.remainder x ≤ terminal)
    (hmass : ∀ x, step.mass x ≤ mass) :
    ∀ x, value x ≤ terminal * (1 + mass) ^ (6 * (bands + 1)) := by
  intro x
  exact (step.bound terminal mass ht hm hterminal hmass x).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith) (Nat.succ_le_of_lt (schedule x).rank_lt_bound)) ht)

end BranchedIntegralStep

/-- The same one-time terminal budget and depth-times edge loss as the
finite and pushforward-measure versions. -/
theorem branchedIntegralStep_power_bound
    {X : Type u} {Ω : Type v} {bands : ℕ} [MeasurableSpace Ω]
    {value : X → ℝ} {schedule : X → State bands}
    (step : BranchedIntegralStep (Ω := Ω) value schedule) (C U T H β δ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hT : 0 ≤ T) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hterminal : ∀ x, step.remainder x ≤ C * (1 + T) ^ H * U ^ β)
    (hmass : ∀ x, step.mass x ≤ C * (1 + T) ^ H * U ^ δ) :
    ∀ x, value x ≤
      (C * (1 + C) ^ (6 * (bands + 1))) *
        U ^ (β + (6 * (bands + 1) : ℕ) * δ) *
        (1 + T) ^ (H * ((6 * (bands + 1) : ℕ) + 1)) := by
  intro x
  have hp : 1 ≤ (1 + T) ^ H := Real.one_le_rpow (by linarith) hH
  have h₁ := step.uniform_rank_bound
    (C * (1 + T) ^ H * U ^ β) (C * (1 + T) ^ H * U ^ δ)
    (by positivity) (by positivity) hterminal hmass x
  apply h₁.trans
  convert propagated_majorant C U ((1 + T) ^ H) β δ (6 * (bands + 1))
    hC hU hp hδ using 1
  rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ 1 + T)]
  norm_num

end HeckeSkeleton.Moments.EngineInduction
