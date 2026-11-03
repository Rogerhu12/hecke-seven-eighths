import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CallData
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StrictProfileOrder

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original profile inputs and uniform scalar witnesses

A uniform estimate chooses a finite set of original seminorms and a
polynomial scalar envelope before the moving parent is selected. The
uniform preparation task then supplies the actual original Schwartz
representatives and pays this envelope. No eligibility predicate is
chosen by a certificate: the rank annulus, scale threshold and finite
seminorm inclusion are the explicit conditions below.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source EngineStep
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

namespace Call

variable {c : TargetContext K} (call : Call c)

def rank : ℕ :=
  parameterCoreRank (recipeInductionSigma c) 2 (recipeInductionSigma c / 16)
    call.node.parameters

def rankBound (_call : Call c) : ℕ := 6 * (widthBand (recipeInductionSigma c) 2 + 1)

def childOrder : ℕ :=
  backwardProfileOrder 1 call.schedule.engine call.frame.reflection (call.rank - 1)

def fixedRange : StrictProfileRange :=
  StrictProfileRange.ofSchedule call.frame.lower call.frame.upper
    call.frame.lower_pos call.frame.interval.le call.rankBound

/-- These are the actual recursive child orders, including the full
prime-cancellation orders already required by the merged constructor. -/
def childOrders : Finset (ℕ × ℕ) :=
  call.fixedRange.childOrders (K := K) (ω := c.family.omega)
    (ψ := targetCharacter K c) ∅ call.childOrder call.frame.decay

/-- All fields constrain original inputs only. In particular there is
no source expansion, child, terminal estimate or kernel in this record. -/
structure Regular : Prop where
  cap : call.prepared.cap = c.geometry.slots
  weight : call.prepared.weight = call.frame.decay
  lower : call.prepared.lower = clippedAnnulusLower call.frame.lower call.frame.upper
    call.rankBound call.rank
  upper : call.prepared.upper =
    rankedAnnulusUpper call.frame.upper call.rankBound call.rank
  heightDegree_nonneg : 0 ≤ call.Hp
  minimumCp : strictChildProfileMinimum
    (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
    1 call.schedule.engine call.frame.reflection (recipeInductionSigma c)
    2 (recipeInductionSigma c / 16) call.frame.decay call.frame.lower call.frame.upper
    call.frame.lower_pos
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) call.frame.upper_large) ≤ call.Cp

def window : Set ℝ :=
  Set.Icc (call.prepared.lower / 2) (2 * call.prepared.upper)

theorem window_positive : call.window ⊆ Set.Ioi 0 := by
  intro x hx
  exact (div_pos call.prepared.lower_pos (by norm_num : (0 : ℝ) < 2)).trans_le hx.1

end Call

/-- Genuine representatives of the original Mellin model. These are
constructed by the merged Mellin-to-Schwartz bridge, before either
Poisson transformation. -/
structure ProfileInput {c : TargetContext K} (call : Call c) where
  regular : call.Regular
  orders : Finset (ℕ × ℕ)
  amplitude : ℝ
  amplitude_one_le : 1 ≤ amplitude
  raw : RawProfileWindow Set.univ Set.univ call.window orders call.node.data amplitude

namespace ProfileInput

variable {c : TargetContext K} {call : Call c} (input : ProfileInput call)

/-- Restricting the allowed rows preserves every original representative.
It does not manufacture any transformed profile. -/
def localized : RawProfileWindow Set.univ Set.univ call.window input.orders
    call.localizedData input.amplitude :=
  localizedRawProfileWindow input.raw call.node.parameters call.base

end ProfileInput

/-- Numerical output of one uniform estimate. Its proof must establish
the estimate for these particular witnesses, for every moving input. -/
structure UniformCost where
  orders : Finset (ℕ × ℕ)
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  profileDegree : ℕ
  heightDegree : ℝ
  heightDegree_nonneg : 0 ≤ heightDegree
  threshold : ℝ
  threshold_one_le : 1 ≤ threshold

namespace UniformCost

def value (cost : UniformCost) (amplitude height : ℝ) : ℝ :=
  cost.coefficient * amplitude ^ cost.profileDegree *
    (1 + height) ^ cost.heightDegree

theorem value_nonneg (cost : UniformCost) {amplitude height : ℝ}
    (hamplitude : 0 ≤ amplitude) (hheight : 0 ≤ height) :
    0 ≤ cost.value amplitude height :=
  mul_nonneg (mul_nonneg cost.coefficient_nonneg (pow_nonneg hamplitude _))
    (Real.rpow_nonneg (by linarith) _)

/-- The three concrete input checks used by a uniform estimate. The
window and original-input calibration are fixed by `ProfileInput`. -/
structure Ready {c : TargetContext K} (cost : UniformCost)
    (call : Call c) (input : ProfileInput call) : Prop where
  orders : cost.orders ⊆ input.orders
  large : cost.threshold ≤ call.base

end UniformCost
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
