import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T1: geometry and budgets of the actual original input

The annulus depends only on the fixed frame and target. The complete
old support is controlled by the original joint row/mask budget after
choosing one actual paired row. No transformed estimate is an input.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineStep HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

/-- One upper endpoint is fixed before choosing the actual call. -/
def uniformAnnulus (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  2 * (frame.upper * (2 : ℝ) ^ (6 * (widthBand (recipeInductionSigma c) 2 + 1)))

theorem uniformAnnulus_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ uniformAnnulus c frame := by
  apply one_le_mul_of_one_le_of_one_le (by norm_num)
  exact one_le_mul_of_one_le_of_one_le
    ((by norm_num : (1 : ℝ) ≤ 2).trans frame.upper_large)
    (one_le_pow₀ (by norm_num))

variable {c : TargetContext K}

/-- The rank-dependent original window stays in this fixed annulus. -/
theorem window_subset_uniformAnnulus (frame : SourceFrame) (call : Call c)
    (input : ProfileInput call) (hframe : call.frame = frame) :
    call.window ⊆ Set.Iic (uniformAnnulus c frame) := by
  have hp : (2 : ℝ) ^ (call.rankBound - call.rank) ≤ 2 ^ call.rankBound :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hu : 0 ≤ call.frame.upper :=
    (by norm_num : (0 : ℝ) ≤ 2).trans call.frame.upper_large
  intro x hx
  have hx' : x ≤ 2 * call.prepared.upper := hx.2
  rw [input.regular.upper, rankedAnnulusUpper] at hx'
  have hupper := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hp hu) (by norm_num : (0 : ℝ) ≤ 2)
  have hbound := hx'.trans hupper
  simpa only [Call.rankBound, hframe, uniformAnnulus, Set.mem_Iic] using hbound

variable (call : Call c)

theorem supportLength_nonneg : 0 ≤ call.supportLength := by
  change 0 ≤ idealLogLength call.base call.oldSupport.val
  exact idealLogLength_nonneg call.base call.domain.scale
    call.oldSupport.val call.oldSupport.property.1

/-- The complete old mask has its literal logarithmic norm length. -/
theorem oldSupport_norm_eq_rpow :
    (Arithmetic.data c).exteriorNorm call.oldSupport = call.base ^ call.supportLength := by
  change (Ideal.absNorm call.oldSupport.val : ℝ) =
    call.base ^ idealLogLength call.base call.oldSupport.val
  exact (rpow_idealLogLength call.base call.domain.scale
    call.oldSupport.val call.oldSupport.property.1).symm

/-- A real original row removes its norm factor from the full joint
budget. The displayed-support budget alone is not used for this step. -/
theorem oldSupport_norm_le (hactive : call.Active) :
    (Arithmetic.data c).exteriorNorm call.oldSupport ≤
      call.base ^ (call.node.parameters.m + call.node.parameters.q) := by
  obtain ⟨u, hu⟩ := hactive
  have hbudget : idealNorm K u * idealNorm K
      (call.source.source.recipe.moving.fullMaskSupport
        call.source.source.recipe.remaining) ≤
      call.base ^ (call.node.parameters.m + call.node.parameters.q) :=
    call.source.pairedJointBudget u hu
  have heffective : (Arithmetic.data c).exteriorNorm call.oldSupport ≤
      idealNorm K (call.source.source.recipe.moving.fullMaskSupport
        call.source.source.recipe.remaining) :=
    call.localizedSource.source.recipe.moving.effectiveFullSupport_norm_le
      call.localizedSource.source.recipe.remaining
  have hrow : idealNorm K (call.source.source.recipe.moving.fullMaskSupport
      call.source.source.recipe.remaining) ≤ idealNorm K u * idealNorm K
      (call.source.source.recipe.moving.fullMaskSupport
        call.source.source.recipe.remaining) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_idealNorm K u) (idealNorm_pos K
        (call.source.source.recipe.moving.fullMaskSupport
          call.source.source.recipe.remaining)).le
  exact heffective.trans (hrow.trans hbudget)

theorem supportLength_le_width (hactive : call.Active) :
    call.supportLength ≤ call.node.parameters.m + call.node.parameters.q := by
  have hlog := Real.log_le_log ((Arithmetic.data c).exteriorNorm_pos call.oldSupport)
    (oldSupport_norm_le call hactive)
  rw [Real.log_rpow call.base_pos] at hlog
  exact (div_le_iff₀ (Real.log_pos call.domain.scale)).mpr hlog

theorem working_width :
    call.workingParameters.m + call.workingParameters.q =
      call.node.parameters.m + call.node.parameters.q := by
  change (call.node.parameters.m + call.node.parameters.q - call.supportLength) +
    call.supportLength = call.node.parameters.m + call.node.parameters.q
  ring

theorem working_width_nonneg :
    0 ≤ call.workingParameters.m + call.workingParameters.q := by
  rw [working_width]
  exact call.domain.width_nonneg

theorem working_width_le_two :
    call.workingParameters.m + call.workingParameters.q ≤ 2 := by
  rw [working_width]
  exact call.width_le

theorem working_m_nonneg (hactive : call.Active) : 0 ≤ call.workingParameters.m :=
  sub_nonneg.mpr (supportLength_le_width call hactive)

theorem working_q_nonneg : 0 ≤ call.workingParameters.q := supportLength_nonneg call

theorem working_m_le_two : call.workingParameters.m ≤ 2 := by
  have hq := working_q_nonneg call
  have hw := working_width_le_two call
  linarith

theorem working_q_le_two (hactive : call.Active) : call.workingParameters.q ≤ 2 := by
  have hm := working_m_nonneg call hactive
  have hw := working_width_le_two call
  linarith

theorem original_total_nonneg :
    0 ≤ call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z := by
  have hz : 0 ≤ call.node.parameters.z := by
    rw [call.domain.total_length]
    exact slotGeometry_totalLength_nonneg call.node.data.geometry
  exact add_nonneg (add_nonneg call.domain.plain_left_nonneg
    call.domain.plain_right_nonneg) hz

/-- A bound independent of the call for the literal three column lengths. -/
theorem original_total_le :
    call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z ≤
      2 + recipeInductionSigma c / 16 := by
  linarith [call.domain.padded_core, call.width_le]

theorem working_total_eq :
    call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z =
      call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z := rfl

theorem working_total_nonneg :
    0 ≤ call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z :=
  original_total_nonneg call

theorem working_total_le :
    call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z ≤
      2 + recipeInductionSigma c / 16 := original_total_le call

theorem working_total_length :
    call.workingParameters.z = call.localizedData.geometry.totalLength :=
  call.domain.total_length

/-- The ordinary branch uses its original plain lengths; the centered
branch retains the node's literal comparison sum. -/
theorem working_comparison_sum :
    call.workingComparison₁ + call.workingComparison₂ =
      call.workingParameters.n₁ + call.workingParameters.n₂ := by
  cases hcentered : call.node.centered with
  | false =>
      simp only [Call.workingComparison₁, Call.workingComparison₂, hcentered,
        Bool.false_eq_true, if_false, Call.workingParameters]
  | true =>
      simpa only [Call.workingComparison₁, Call.workingComparison₂, hcentered,
        if_true, Call.workingParameters] using call.node.comparison_sum

theorem working_comparison_product :
    call.base ^ call.workingComparison₁ * call.base ^ call.workingComparison₂ =
      call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂) := by
  rw [← Real.rpow_add call.base_pos, working_comparison_sum]

theorem working_comparison₁_scale_pos : 0 < call.base ^ call.workingComparison₁ :=
  Real.rpow_pos_of_pos call.base_pos _

theorem working_comparison₂_scale_pos : 0 < call.base ^ call.workingComparison₂ :=
  Real.rpow_pos_of_pos call.base_pos _

theorem working_comparison₁_scale_nonneg : 0 ≤ call.base ^ call.workingComparison₁ :=
  (working_comparison₁_scale_pos call).le

theorem working_comparison₂_scale_nonneg : 0 ≤ call.base ^ call.workingComparison₂ :=
  (working_comparison₂_scale_pos call).le

theorem working_comparison₁_scale_one_le : 1 ≤ call.base ^ call.workingComparison₁ := by
  cases hcentered : call.node.centered with
  | false =>
      simpa only [Call.workingComparison₁, hcentered, Bool.false_eq_true, if_false] using
        Real.one_le_rpow call.domain.scale.le call.domain.plain_left_nonneg
  | true =>
      simp only [Call.workingComparison₁, hcentered, if_true]
      rw [call.domain.comparison_left hcentered]
      exact Real.one_le_rpow call.domain.scale.le
        (div_nonneg call.domain.width_nonneg (by norm_num))

theorem working_comparison₂_scale_one_le : 1 ≤ call.base ^ call.workingComparison₂ := by
  cases hcentered : call.node.centered with
  | false =>
      simpa only [Call.workingComparison₂, hcentered, Bool.false_eq_true, if_false] using
        Real.one_le_rpow call.domain.scale.le call.domain.plain_right_nonneg
  | true =>
      simp only [Call.workingComparison₂, hcentered, if_true]
      rw [call.domain.comparison_right hcentered]
      apply Real.one_le_rpow call.domain.scale.le
      have hl := call.domain.centered_left hcentered
      have hr := call.domain.centered_right hcentered
      have hw := call.domain.width_nonneg
      linarith

variable {call} {p : SourceParameters c}

/-- The inverse physical radius is the actual working inverse length. -/
theorem first_radius_inv (F : FirstPresentation call p) (hF : F.Realizes) :
    F.source.radius.val⁻¹ = call.base ^ call.workingParameters.m := by
  rw [hF.radius, Real.rpow_neg call.base_pos.le, inv_inv]

theorem first_radius_inv_one_le (F : FirstPresentation call p) (hF : F.Realizes) :
    1 ≤ F.source.radius.val⁻¹ := by
  rw [first_radius_inv F hF]
  exact Real.one_le_rpow call.domain.scale.le (working_m_nonneg call hF.active)

theorem sigma_le_terminalLoss : recipeInductionSigma c ≤ recipeInductionTerminalLoss c := by
  have hs := (recipeInduction_budget (c := c)).1
  have hr := (moment_mesh_engine_bounds c.family.lamA_pos).2.1
  unfold recipeInductionTerminalLoss terminalBudget
  linarith

theorem source_loss_le_sigma_div (p : SourceParameters c) :
    p.loss ≤ recipeInductionSigma c / 64 := by
  linarith [p.loss_small]

theorem source_loss_paid_by_terminal (p : SourceParameters c) :
    64 * p.loss ≤ recipeInductionTerminalLoss c :=
  p.loss_small.trans sigma_le_terminalLoss

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof
