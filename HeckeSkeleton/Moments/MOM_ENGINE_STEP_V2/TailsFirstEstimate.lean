import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsEstimateAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsOriginalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsAnalytic
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsFixedCutoff

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The first actual truncation error has a uniform terminal bound

The prescribed positive first cutoff pays the full polynomial degree
of the original active-column tail mass. The decay and the fixed
row-ball seminorm coefficient are chosen before the call. Division by
the unchanged parent normalizer can only decrease this nonnegative
tail, since an actual original row forces that normalizer to be at
least one.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open NumberField HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction.Source

attribute [local instance] sourcePrincipal sourceNormOneSpace sourceNormOneBorel

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem parentNormalizer_one_le (call : Call c) (hactive : call.Active) :
    1 ≤ call.parentNormalizer :=
  Real.one_le_rpow call.domain.scale.le
    ((supportLength_nonneg call).trans (supportLength_le_width call hactive))

theorem normalizedScalar_le (call : Call c) (hactive : call.Active)
    {value : ℝ} (hvalue : 0 ≤ value) : call.normalizedScalar value ≤ value := by
  apply (div_le_iff₀ call.parentNormalizer_pos).mpr
  exact le_mul_of_one_le_right hvalue (parentNormalizer_one_le call hactive)

theorem first_tail_nonneg (F : FirstPresentation call p) : 0 ≤ F.tail :=
  mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- This estimate uses the fixed original point-evaluation order only;
the high-order seminorms belong to the unchanged row-ball kernel and
are included in the fixed coefficient. -/
theorem exists_firstTailCertificate (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c) : Nonempty (FirstTailCertificate c frame p) := by
  let decay := tailDecayForWidth (firstMassDegree c)
    (-recipeInductionTerminalLoss c) p.firstCutoffExponent
  have hdecay : 1 < decay :=
    tailDecayForWidth_gt_one _ _ _ p.firstCutoff_pos
  obtain ⟨estimate⟩ := exists_divisorUniformEstimate c decay hdecay
  let cost : UniformCost := {
    orders := originalOrders
    coefficient := estimate.coefficient * firstMassCoefficient c estimate.orders
    coefficient_nonneg := mul_nonneg estimate.coefficient_nonneg
      (firstMassCoefficient_nonneg c estimate.orders)
    profileDegree := 2 * (c.geometry.slots + 2)
    heightDegree := 0
    heightDegree_nonneg := le_rfl
    threshold := originalThreshold c frame
    threshold_one_le := originalThreshold_one_le c frame }
  refine ⟨{ cost := cost, bound := ?_ }⟩
  intro call input hframe ready F hF
  have horders : originalOrders ⊆ input.orders := ready.orders
  have hlarge : originalThreshold c call.frame ≤ call.base := by
    rw [hframe]
    exact ready.large
  have hmass := first_tailCost_bound F hF input horders hlarge estimate.orders
  have htail := first_masked_tail_le estimate F
  rw [hF.fiber, Nat.cast_one, one_mul] at htail
  have hcutoff := fixed_cutoff_mass_bound call.base
    (firstMassDegree c) (firstMassDegree c) (-recipeInductionTerminalLoss c)
    p.firstCutoffExponent p.firstCutoffExponent
    (F.source.tailCost estimate.orders) (firstMassCoefficient c estimate.orders)
    (input.amplitude ^ (2 * (c.geometry.slots + 2))) estimate.coefficient
    call.domain.scale.le p.firstCutoff_pos le_rfl le_rfl
    (firstMassCoefficient_nonneg c estimate.orders)
    (pow_nonneg (zero_le_one.trans input.amplitude_one_le) _)
    estimate.coefficient_nonneg hmass
  calc
    F.normalizedTail ≤ F.tail :=
      normalizedScalar_le call hF.active (first_tail_nonneg F)
    _ ≤ estimate.coefficient * (p.firstCutoff call) ^ (1 - decay) *
        F.source.tailCost estimate.orders := htail
    _ ≤ (estimate.coefficient * firstMassCoefficient c estimate.orders) *
        input.amplitude ^ (2 * (c.geometry.slots + 2)) *
          call.base ^ recipeInductionTerminalLoss c := by
      simpa only [SourceParameters.firstCutoff, decay, neg_neg] using hcutoff
    _ = _ := by simp only [cost, UniformCost.value, Real.rpow_zero, mul_one]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.exists_firstTailCertificate
