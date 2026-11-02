import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsSecondMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsOriginalRows

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Coarse original geometry for the second truncation

The logarithm of the retained scale cancels against the same logarithm
inside the prescribed enlargement. The three pool errors satisfy their
literal moving-length inequality, so the bound is uniform in their prime.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem originalNominal_moving_le_removed (tag : OriginalNominalTag K) :
    tag.movingLength call.base ≤ tag.removedLength call.base := by
  cases tag with
  | direct => exact le_rfl
  | main => exact le_rfl
  | error e q =>
    exact amplifier_error_moving_le e (idealLogLength call.base q.asIdeal)
      (idealLogLength_nonneg call.base call.domain.scale _ q.ne_bot)

theorem originalNominal_padding_le (tag : OriginalNominalTag K) :
    tag.padding (recipeInductionSigma c) ≤ 2 * recipeInductionSigma c := by
  have hs := (recipeInduction_budget (c := c)).1
  cases tag <;> simp only [OriginalNominalTag.padding] <;> linarith

def secondColumnExponent (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  2 + recipeInductionSigma c / 16 + 4 * p.loss

theorem secondColumnExponent_nonneg : 0 ≤ secondColumnExponent c p := by
  have hs := (recipeInduction_budget (c := c)).1
  dsimp [secondColumnExponent]
  linarith [p.loss_pos]

theorem working_total_z_le :
    call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z ≤
      2 + recipeInductionSigma c / 16 := by
  change call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z ≤ _
  rw [call.domain.total_length]
  exact working_total_le call

theorem physical_active_ideal_le (source : PhysicalSource call p)
    (hwindow : source.Windows) (i : source.Column)
    (hi : i ∈ physicalActiveColumns source) :
    (Arithmetic.data c).exteriorNorm (source.source.ideal i) ≤
      call.base ^ secondColumnExponent c p := by
  have hm := Finset.mem_filter.mp hi
  apply (hwindow.column_upper i hm.1 hm.2).trans
  apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
  have hs := idealLogLength_nonneg call.base call.domain.scale source.first.selected.val
    source.first.selected.property
  have hw := source.first.tag.removedLength_nonneg call.base call.domain.scale
  have ht := working_total_z_le (call := call)
  dsimp only [secondColumnExponent]
  linarith

def secondRadiusExponent (c : TargetContext K) (retainedDegree lengthBound : ℝ) : ℝ :=
  max (2 * (2 + recipeInductionSigma c / 16) + 2 * lengthBound) retainedDegree +
    2 * recipeInductionSigma c

/-- The estimate uses the literal scale and enlargement, before any
second common label or row classifier is introduced. -/
theorem second_inverseRadius_le (source : SecondSource call p) (hs : source.Realizes)
    (hactive : call.Active) (retainedDegree lengthBound : ℝ)
    (hretained : source.physical.first.retainedScale ≤ call.base ^ retainedDegree)
    (hactiveLength : idealLogLength call.base
      (firstActiveRadical source.physical.first.selected.val
        source.physical.first.opposite.val) ≤ lengthBound)
    (hmaskLength : idealLogLength call.base source.physical.first.complementary.val ≤
      lengthBound) :
    source.stage.radius.val⁻¹ ≤ call.base ^ secondRadiusExponent c retainedDegree lengthBound := by
  let R := Real.log source.physical.first.retainedScale / Real.log call.base
  have hR : call.base ^ R = source.physical.first.retainedScale := by
    simpa only [R, Real.logb] using Real.rpow_logb call.base_pos call.domain.scale.ne'
      source.physical.first.retainedScale_pos
  have hRle : R ≤ retainedDegree :=
    (Real.rpow_le_rpow_left_iff call.domain.scale).mp (by rw [hR]; exact hretained)
  have ht := working_total_z_le (call := call)
  have hm := working_m_nonneg call hactive
  have hselected := idealLogLength_nonneg call.base call.domain.scale
    source.physical.first.selected.val source.physical.first.selected.property
  have hremoved := source.physical.first.tag.removedLength_nonneg
    call.base call.domain.scale
  have hmoving := originalNominal_moving_le_removed (call := call) source.physical.first.tag
  have hpadding := originalNominal_padding_le (c := c) source.physical.first.tag
  have hexponent : R + source.physical.enlargement ≤
      secondRadiusExponent c retainedDegree lengthBound := by
    let J := idealLogLength call.base source.physical.first.opposite.val -
      idealLogLength call.base source.physical.first.selected.val +
      source.physical.firstFrequency - R -
      2 * source.physical.first.tag.removedLength call.base +
      source.physical.first.tag.movingLength call.base
    have hbound : R + J ≤ 2 * (2 + recipeInductionSigma c / 16) + 2 * lengthBound := by
      dsimp only [J, PhysicalSource.firstFrequency]
      linarith
    change R + (max J 0 + source.physical.first.tag.padding (recipeInductionSigma c)) ≤ _
    unfold secondRadiusExponent
    by_cases hJ : 0 ≤ J
    · rw [max_eq_left hJ]
      have hh := le_max_left
        (2 * (2 + recipeInductionSigma c / 16) + 2 * lengthBound) retainedDegree
      linarith
    · rw [max_eq_right (le_of_not_ge hJ)]
      have hh := le_max_right
        (2 * (2 + recipeInductionSigma c / 16) + 2 * lengthBound) retainedDegree
      linarith
  rw [hs.radius, inv_inv]
  calc
    _ = call.base ^ (R + source.physical.enlargement) := by
      rw [Real.rpow_add call.base_pos, hR]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hexponent

/-- Exact orbit fibres cannot exceed the original finite row carrier. -/
theorem orbitMultiplicity_le_rows (source : PhysicalSource call p) :
    source.orbitMultiplicity ≤ source.source.rows.card := by
  apply Finset.sup_le
  intro q hq
  exact Finset.card_filter_le _ _

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.second_inverseRadius_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.physical_active_ideal_le
