module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailContracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Add the two estimates of the same original trace

The two independently proved estimates retain the literal normalized
tail terms. Their fixed orders, polynomial coefficients and thresholds
are combined before any moving call. No source or tail is replaced.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open NumberField HeckeGeneral.ThetaSkeleton.Global EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

structure FirstTailCertificate (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c) where
  cost : UniformCost
  bound : ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
    cost.Ready call input → ∀ F : FirstPresentation call p, F.Realizes →
      F.normalizedTail ≤ cost.value input.amplitude call.request.height *
        call.base ^ recipeInductionTerminalLoss c

structure SecondTailCertificate (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c) where
  cost : UniformCost
  bound : ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
    cost.Ready call input → ∀ trace : SourceTrace call p, trace.Realizes →
      trace.second.normalizedTail ≤ cost.value input.amplitude call.request.height *
        call.base ^ recipeInductionTerminalLoss c

def sumCost (left right : UniformCost) : UniformCost where
  orders := left.orders ∪ right.orders
  coefficient := left.coefficient + right.coefficient
  coefficient_nonneg := add_nonneg left.coefficient_nonneg right.coefficient_nonneg
  profileDegree := left.profileDegree + right.profileDegree
  heightDegree := left.heightDegree + right.heightDegree
  heightDegree_nonneg := add_nonneg left.heightDegree_nonneg right.heightDegree_nonneg
  threshold := max left.threshold right.threshold
  threshold_one_le := left.threshold_one_le.trans (le_max_left _ _)

theorem sumCost_ready_left {c : TargetContext K} {call : Call c}
    {input : ProfileInput call} {left right : UniformCost}
    (ready : (sumCost left right).Ready call input) : left.Ready call input where
  orders := fun _ h => ready.orders (Finset.mem_union_left _ h)
  large := (le_max_left _ _).trans ready.large

theorem sumCost_ready_right {c : TargetContext K} {call : Call c}
    {input : ProfileInput call} {left right : UniformCost}
    (ready : (sumCost left right).Ready call input) : right.Ready call input where
  orders := fun _ h => ready.orders (Finset.mem_union_right _ h)
  large := (le_max_right _ _).trans ready.large

theorem sumCost_value (left right : UniformCost) {amplitude height : ℝ}
    (hamplitude : 1 ≤ amplitude) (hheight : 0 ≤ height) :
    left.value amplitude height + right.value amplitude height ≤
      (sumCost left right).value amplitude height := by
  have ha : 0 ≤ amplitude := zero_le_one.trans hamplitude
  have hh : 1 ≤ 1 + height := by linarith
  have hlp := mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hamplitude
      (show left.profileDegree ≤ left.profileDegree + right.profileDegree by omega))
    left.coefficient_nonneg
  have hrp := mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hamplitude
      (show right.profileDegree ≤ left.profileDegree + right.profileDegree by omega))
    right.coefficient_nonneg
  have hlh : (1 + height) ^ left.heightDegree ≤
      (1 + height) ^ (left.heightDegree + right.heightDegree) :=
    Real.rpow_le_rpow_of_exponent_le hh
      (le_add_of_nonneg_right right.heightDegree_nonneg)
  have hrh : (1 + height) ^ right.heightDegree ≤
      (1 + height) ^ (left.heightDegree + right.heightDegree) :=
    Real.rpow_le_rpow_of_exponent_le hh
      (le_add_of_nonneg_left left.heightDegree_nonneg)
  have hl := mul_le_mul hlp hlh (Real.rpow_nonneg (zero_le_one.trans hh) _)
    (mul_nonneg left.coefficient_nonneg (pow_nonneg ha _))
  have hr := mul_le_mul hrp hrh (Real.rpow_nonneg (zero_le_one.trans hh) _)
    (mul_nonneg right.coefficient_nonneg (pow_nonneg ha _))
  calc
    _ ≤ left.coefficient * amplitude ^ (left.profileDegree + right.profileDegree) *
          (1 + height) ^ (left.heightDegree + right.heightDegree) +
        right.coefficient * amplitude ^ (left.profileDegree + right.profileDegree) *
          (1 + height) ^ (left.heightDegree + right.heightDegree) := add_le_add hl hr
    _ = _ := by simp only [UniformCost.value, sumCost]; ring

def tailCertificate_of_parts {c : TargetContext K} {frame : SourceFrame}
    {p : SourceParameters c} (first : FirstTailCertificate c frame p)
    (second : SecondTailCertificate c frame p) : TailCertificate c frame p where
  cost := sumCost first.cost second.cost
  bound := by
    intro call input hframe ready trace htrace
    have hf := first.bound call input hframe (sumCost_ready_left ready)
      trace.first htrace.first
    have hs := second.bound call input hframe (sumCost_ready_right ready) trace htrace
    calc
      _ ≤ first.cost.value input.amplitude call.request.height *
            call.base ^ recipeInductionTerminalLoss c +
          second.cost.value input.amplitude call.request.height *
            call.base ^ recipeInductionTerminalLoss c := add_le_add hf hs
      _ = (first.cost.value input.amplitude call.request.height +
          second.cost.value input.amplitude call.request.height) *
            call.base ^ recipeInductionTerminalLoss c := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (sumCost_value first.cost second.cost input.amplitude_one_le
          call.request.height_nonneg) (Real.rpow_nonneg call.base_pos.le _)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.tailCertificate_of_parts
