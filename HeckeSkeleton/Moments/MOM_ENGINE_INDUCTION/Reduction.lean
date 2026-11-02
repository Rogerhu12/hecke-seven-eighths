import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.IntegralRecursion
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.BranchedIntegralRecursion

/-!
# Finite and continuous parent reductions

A parent may have a finite family of children or a continuously parametrized
family coming from a common transform kernel.  The two constructors retain
these actual reduction structures.  In the integral case the measurable
space and the finite positive child measures are part of the data, together
with integrability and almost-everywhere decrease of the induction state.

The common interface exposes the original terminal remainder and the total
nonnegative child mass.  Its power bound is proved by applying the appropriate
finite or integral induction theorem; no completed bound is a constructor
field.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace HeckeSkeleton.Moments.EngineInduction

universe u

/-- Three genuine forms of the parent reduction. The direct branched form
needs a measurable structure only on its original parameter space. -/
inductive Reduction {X : Type u} {bands : ℕ}
    (value : X → ℝ) (schedule : X → State bands) where
  | finite (step : LocalStep value schedule)
  | integral (measurableSpace : MeasurableSpace X)
      (step : @IntegralStep X bands measurableSpace value schedule)
  | branched (Ω : Type u) (measurableSpace : MeasurableSpace Ω)
      (step : @BranchedIntegralStep X Ω bands measurableSpace value schedule)

namespace Reduction

variable {X : Type u} {bands : ℕ}
variable {value : X → ℝ} {schedule : X → State bands}

/-- The original terminal contribution, before its ledger is closed. -/
def remainder : Reduction value schedule → X → ℝ
  | .finite step => step.remainder
  | .integral measurableSpace step =>
      letI : MeasurableSpace X := measurableSpace
      step.remainder
  | .branched Ω measurableSpace step =>
      letI : MeasurableSpace Ω := measurableSpace
      step.remainder

/-- Finite weight mass or the total mass of the positive kernel measure. -/
def mass : Reduction value schedule → X → ℝ
  | .finite step => fun x => ∑ y ∈ step.children x, step.weight x y
  | .integral measurableSpace step =>
      letI : MeasurableSpace X := measurableSpace
      step.mass
  | .branched Ω measurableSpace step =>
      letI : MeasurableSpace Ω := measurableSpace
      step.mass

theorem mass_nonneg (reduction : Reduction value schedule) (x : X) :
    0 ≤ reduction.mass x := by
  cases reduction with
  | finite step =>
      change 0 ≤ ∑ y ∈ step.children x, step.weight x y
      exact Finset.sum_nonneg fun y hy => step.weight_nonneg x y hy
  | integral measurableSpace step =>
      letI : MeasurableSpace X := measurableSpace
      change 0 ≤ step.mass x
      exact step.mass_nonneg x
  | branched Ω measurableSpace step =>
      letI : MeasurableSpace Ω := measurableSpace
      change 0 ≤ step.mass x
      exact step.mass_nonneg x

/-- One quantitative conclusion for all three genuine reduction structures.
Only the local mass loss is multiplied by the finite state depth. -/
theorem power_bound (reduction : Reduction value schedule)
    (C U T H β δ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hT : 0 ≤ T) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hterminal : ∀ x, reduction.remainder x ≤ C * (1 + T) ^ H * U ^ β)
    (hmass : ∀ x, reduction.mass x ≤ C * (1 + T) ^ H * U ^ δ) :
    ∀ x, value x ≤
      (C * (1 + C) ^ (6 * (bands + 1))) *
        U ^ (β + (6 * (bands + 1) : ℕ) * δ) *
        (1 + T) ^ (H * ((6 * (bands + 1) : ℕ) + 1)) := by
  cases reduction with
  | finite step =>
      exact localStep_power_bound step C U T H β δ hC hU hT hH hδ hterminal hmass
  | integral measurableSpace step =>
      letI : MeasurableSpace X := measurableSpace
      exact integralStep_power_bound step C U T H β δ hC hU hT hH hδ hterminal hmass
  | branched Ω measurableSpace step =>
      letI : MeasurableSpace Ω := measurableSpace
      exact branchedIntegralStep_power_bound step C U T H β δ hC hU hT hH hδ hterminal hmass

end Reduction

end HeckeSkeleton.Moments.EngineInduction
