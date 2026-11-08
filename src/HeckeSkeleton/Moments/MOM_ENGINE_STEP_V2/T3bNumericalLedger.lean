module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bKernels
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bIndexWeights
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bIndexAssembly
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bPairedRows

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual exceptional divisor saving and terminal numerical reserve

The centered positive part is retained through the two original divisor
extractions. The final scalar composition integrates the actual fixed
kernels and divides by the original parent normalizer. At the exact
inner-divisor length its weight is literally the N8a index weight.

The analytic and normalizer inequalities used by the scalar composition
are internal proof inputs, proved on the same raw leaf by the source
factories. They are not new hypotheses of the public T3b contract.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

open EngineStep EngineInduction
open EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem positive_part_after_nonnegative_extraction (L r : ℝ) (hr : 0 ≤ r) :
    max (L - r) 0 = max (max L 0 - r) 0 := by
  rcases le_total 0 L with hL | hL
  · rw [max_eq_left hL]
  · have hLr : L - r ≤ 0 := by linarith
    have h0r : 0 - r ≤ 0 := by linarith
    simp only [max_eq_right hL, max_eq_right hLr, max_eq_right h0r]

/-- The original saving is `max (L-v) 0`, even when the remaining
plain length after a divisor extraction is nonpositive. -/
theorem centered_divisor_exponent
    (A M c w b₂ v F₁ F₂ step δ r₁ r₂ divisorLower slotError : ℝ)
    (hr₁ : 0 ≤ r₁) (hdivisor : divisorLower - r₂ ≤ slotError)
    (hF₁ : 2 * (c + w) / 3 - 3 * step - 5 * δ / 6 ≤ F₁)
    (hF₂ : 2 * b₂ / 3 ≤ F₂) (hv : v ≤ c + w + b₂) :
    A - 5 * M / 6 - F₁ - F₂ - r₁ - r₂ - max (M / 4 - v - r₁) 0 ≤
      max (A - M) 0 + 3 * step + 5 * δ / 6 + slotError - divisorLower := by
  have hcenter := exceptional_paired_exponent A M c w b₂ v F₁ F₂ step δ
    hF₁ hF₂ hv
  have hdiv := centered_divisor_saving divisorLower r₁ r₂
    (max (M / 4 - v) 0) slotError hdivisor
  rw [← positive_part_after_nonnegative_extraction (M / 4 - v) r₁ hr₁] at hdiv
  linarith

theorem centered_right_divisor_exponent
    (A M c w b₂ v F₁ F₂ step δ r₁ r₂ divisorLower slotError : ℝ)
    (hr₂ : 0 ≤ r₂) (hdivisor : divisorLower - r₁ ≤ slotError)
    (hF₁ : 2 * (c + w) / 3 - 3 * step - 5 * δ / 6 ≤ F₁)
    (hF₂ : 2 * b₂ / 3 ≤ F₂) (hv : v ≤ c + w + b₂) :
    A - 5 * M / 6 - F₁ - F₂ - r₁ - r₂ - max (M / 4 - v - r₂) 0 ≤
      max (A - M) 0 + 3 * step + 5 * δ / 6 + slotError - divisorLower := by
  have h := centered_divisor_exponent A M c w b₂ v F₁ F₂ step δ
    r₂ r₁ divisorLower slotError hr₂ hdivisor hF₁ hF₂ hv
  linarith

/-- The uncentered alternative uses the actual ordinary core and the
absolute source bound; it does not invoke a centered cancellation. -/
theorem absolute_divisor_exponent
    (A M c w b₂ F₁ F₂ step δ r₁ r₂ divisorLower slotError : ℝ)
    (hA : A ≤ 5 * M / 6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb₂ : 0 ≤ b₂)
    (hr₁ : 0 ≤ r₁) (hdivisor : divisorLower - r₂ ≤ slotError)
    (hF₁ : 2 * (c + w) / 3 - 3 * step - 5 * δ / 6 ≤ F₁)
    (hF₂ : 2 * b₂ / 3 ≤ F₂) :
    A - 5 * M / 6 - F₁ - F₂ - r₁ - r₂ ≤
      3 * step + 5 * δ / 6 + slotError - divisorLower := by
  have h := uncentered_exceptional_bound A M c w b₂ F₁ F₂ step δ
    hA hc hw hb₂ hF₁ hF₂
  linarith

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem original_core_excess_le (call : Call c) :
    max (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z -
      (call.node.parameters.m + call.node.parameters.q)) 0 ≤ recipeInductionSigma c / 16 := by
  have hpadding := call.domain.padded_core
  have hstep := (recipeInduction_budget (c := c)).1
  apply max_le
  · linarith
  · positivity

/-- The same source loss may be used for the supported-volume error
and the later N8a index. All actual small errors stay within the
preselected reserve; the original terminal budget pays both losses. -/
theorem exceptional_exponent_with_index_reserve
    (call : Call c) (p : SourceParameters c) (error : ℝ)
    (herror : error ≤ 4096 * ((c.geometry.slots : ℝ) + 1) * p.loss) :
    max (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z -
      (call.node.parameters.m + call.node.parameters.q)) 0 +
        3 * recipeInductionSigma c + error ≤
      recipeInductionTerminalLoss c - p.loss - p.loss := by
  have hcore := original_core_excess_le call
  have hsmall := p.loss_small
  have hreserve := p.loss_reserve
  have hstep := (recipeInduction_budget (c := c)).1
  change _ ≤ terminalBudget (16 * recipeInductionSigma c) (recipeInductionSigma c / 16)
    (recipeInductionSigma c) (sourceReserve c.family.lamA) - p.loss - p.loss
  unfold terminalBudget
  linarith

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable {geometry : GeometryFamily second}

/-- Convert the proved paired-row estimate using the actual outer
weight and parent normalizer. The two fixed kernel moments are paid
once, and the original second-divisor saving is retained explicitly. -/
theorem normalized_leaf_le_actual_dyad
    (raw : RawFamily geometry) (j : Fin raw.count)
    (hpacket : (raw.packet j).Realizes)
    (nominalNorm scalar coefficient exponent divisorLower normalizerLoss normalizerCoefficient : ℝ)
    (J₁ J₂ : ℕ) (hcoefficient : 0 ≤ coefficient)
    (hpoint : ∀ z : ℝ × ℝ,
      call.base ^ (-nominalNorm) * (raw.packet j).leaf.exceptionalIntegrand z ≤
        scalar * coefficient * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂) *
          call.base ^ (exponent - divisorLower))
    (hnormalizer : (raw.packet j).leaf.weight * scalar * call.base ^ nominalNorm /
        call.parentNormalizer ≤
      normalizerCoefficient * expansion.indexPrefactor (raw.sourceIndex j) * raw.commonIndexFactor j *
        call.base ^ normalizerLoss) :
    call.normalizedScalar (raw.packet j).leaf.exceptionalCost ≤
      (normalizerCoefficient * coefficient * kernelMoment c p J₁ J₂) * raw.exceptionalDyadWeight divisorLower j *
        call.base ^ (exponent + normalizerLoss) := by
  have hcancel : call.base ^ nominalNorm * call.base ^ (-nominalNorm) = 1 := by
    rw [← Real.rpow_add call.base_pos, add_neg_cancel, Real.rpow_zero]
  have hpoint' (z : ℝ × ℝ) :
      (raw.packet j).leaf.exceptionalIntegrand z ≤
        (call.base ^ nominalNorm * (scalar * coefficient * call.base ^ (exponent - divisorLower))) *
          ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂) := by
    calc
      _ = call.base ^ nominalNorm *
          (call.base ^ (-nominalNorm) * (raw.packet j).leaf.exceptionalIntegrand z) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ call.base ^ nominalNorm *
          (scalar * coefficient * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂) *
            call.base ^ (exponent - divisorLower)) :=
        mul_le_mul_of_nonneg_left (hpoint z) (Real.rpow_nonneg call.base_pos.le _)
      _ = _ := by ring
  have hcost := exceptionalCost_le_kernelMoment (raw.packet j) hpacket
    (call.base ^ nominalNorm * (scalar * coefficient * call.base ^ (exponent - divisorLower)))
    J₁ J₂ hpoint'
  have hfactor : 0 ≤ coefficient * kernelMoment c p J₁ J₂ *
      call.base ^ (exponent - divisorLower) :=
    mul_nonneg (mul_nonneg hcoefficient (kernelMoment_nonneg c p J₁ J₂))
      (Real.rpow_nonneg call.base_pos.le _)
  calc
    call.normalizedScalar (raw.packet j).leaf.exceptionalCost ≤
        ((raw.packet j).leaf.weight *
          (call.base ^ nominalNorm * (scalar * coefficient * call.base ^ (exponent - divisorLower))) *
          kernelMoment c p J₁ J₂) / call.parentNormalizer :=
      div_le_div_of_nonneg_right hcost call.parentNormalizer_pos.le
    _ = ((raw.packet j).leaf.weight * scalar * call.base ^ nominalNorm / call.parentNormalizer) *
        (coefficient * kernelMoment c p J₁ J₂ * call.base ^ (exponent - divisorLower)) := by ring
    _ ≤ (normalizerCoefficient * expansion.indexPrefactor (raw.sourceIndex j) * raw.commonIndexFactor j *
        call.base ^ normalizerLoss) *
        (coefficient * kernelMoment c p J₁ J₂ * call.base ^ (exponent - divisorLower)) :=
      mul_le_mul_of_nonneg_right hnormalizer hfactor
    _ = _ := by
      simp only [RawFamily.exceptionalDyadWeight, Real.rpow_add call.base_pos,
        Real.rpow_sub call.base_pos, Real.rpow_neg call.base_pos.le]
      ring

/-- At the actual original divisor norm, the previous exact dyad bound
is the per-leaf bound consumed by the existing N8a summation lemma. -/
theorem normalized_leaf_le_index
    (raw : RawFamily geometry) (j : Fin raw.count)
    (hpacket : (raw.packet j).Realizes)
    (nominalNorm scalar coefficient exponent normalizerLoss loss normalizerCoefficient : ℝ)
    (J₁ J₂ : ℕ) (hcoefficient : 0 ≤ coefficient) (hnormalizerCoefficient : 0 ≤ normalizerCoefficient)
    (hpoint : ∀ z : ℝ × ℝ,
      call.base ^ (-nominalNorm) * (raw.packet j).leaf.exceptionalIntegrand z ≤
        scalar * coefficient * ((1 + ‖z.1‖) ^ J₁ * (1 + ‖z.2‖) ^ J₂) *
          call.base ^ (exponent - idealLogLength call.base (raw.innerDivisor j)))
    (hnormalizer : (raw.packet j).leaf.weight * scalar * call.base ^ nominalNorm /
        call.parentNormalizer ≤
      normalizerCoefficient * expansion.indexPrefactor (raw.sourceIndex j) * raw.commonIndexFactor j *
        call.base ^ normalizerLoss)
    (hexponent : exponent + normalizerLoss ≤ recipeInductionTerminalLoss c - loss - p.loss) :
    call.normalizedScalar (raw.packet j).leaf.exceptionalCost ≤
      (normalizerCoefficient * coefficient * kernelMoment c p J₁ J₂) * raw.indexWeight j *
        call.base ^ (recipeInductionTerminalLoss c - loss - p.loss) := by
  have h := normalized_leaf_le_actual_dyad raw j hpacket
    nominalNorm scalar coefficient exponent
    (idealLogLength call.base (raw.innerDivisor j)) normalizerLoss normalizerCoefficient
    J₁ J₂ hcoefficient hpoint hnormalizer
  rw [raw.t3b_exceptionalDyadWeight_actual_length] at h
  apply h.trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hexponent)
    (mul_nonneg (mul_nonneg (mul_nonneg hnormalizerCoefficient hcoefficient) (kernelMoment_nonneg c p J₁ J₂))
      (raw.t3b_indexWeight_nonneg j))

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.centered_divisor_exponent
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.exceptional_exponent_with_index_reserve
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.normalized_leaf_le_index
