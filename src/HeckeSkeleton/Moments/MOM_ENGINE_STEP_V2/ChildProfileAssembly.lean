import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildInvariantData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Positive unit windows give the exact scheduled profile primitive

The base finite-rank Schwartz-to-Euler coefficient was paid by the
original uniform preparation. Strict width decrease and literal
zero-slot preservation imply earlier rank before any recursive label
or engine conclusion is constructed. This avoids a circular appeal to
the final output's admissibility.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}
variable {rowDomain : Set (NonzeroIdeal K)} {window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)}

theorem childRank_lt (N : NormalizedData call)
    (geometry : N.family.OutputGeometry N.labels call.node.data call.node.parameters
      (recipeInductionSigma c) rowDomain window orders)
    (side : Bool) (b : N.Active) (ξ : EngineParameter) :
    parameterCoreRank (recipeInductionSigma c) 2 (recipeInductionSigma c / 16)
      (N.childParameters side b) < call.rank := by
  apply parameterCoreRank_strict_width (recipeInduction_budget (c := c)).1
  · cases side with
    | false => exact geometry.left_width_nonneg b
    | true => exact geometry.right_width_nonneg b
  · cases side with
    | false =>
      change (N.family.leftParameters N.labels b).m +
        (N.family.leftParameters N.labels b).q + recipeInductionSigma c / 2 ≤ _
      linarith [geometry.left_width b]
    | true =>
      change (N.family.rightParameters N.labels b).m +
        (N.family.rightParameters N.labels b).q + recipeInductionSigma c / 2 ≤ _
      linarith [geometry.right_width b]
  · intro hzero
    have hcount : call.node.data.geometry.slotCount = 0 :=
      (slotGeometry_totalLength_eq_zero_iff call.node.data.geometry).mp
        (call.domain.total_length.symm.trans hzero)
    have hslots : (N.childData side b ξ).geometry.slotCount ≤
        call.node.data.geometry.slotCount := by
      cases side with
      | false => exact geometry.left_slots b ξ
      | true => exact geometry.right_slots b ξ
    have hlength : (N.childParameters side b).z =
        (N.childData side b ξ).geometry.totalLength := by
      cases side with
      | false => exact geometry.left_length b ξ
      | true => exact geometry.right_length b ξ
    rw [hlength]
    exact (slotGeometry_totalLength_eq_zero_iff _).mpr
      (Nat.eq_zero_of_le_zero (hslots.trans_eq hcount))

theorem profileInvariant_of_windows (N : NormalizedData call)
    (regular : call.Regular)
    (geometry : N.family.OutputGeometry N.labels call.node.data call.node.parameters
      (recipeInductionSigma c) rowDomain window orders)
    (windows : N.UnitWindows) : N.ProfileInvariant := by
  have hupper : 0 < call.frame.upper :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) call.frame.upper_large
  have controls :=
    (exists_rankedAnnulusSchwartz_profileBudget
      (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
      1 call.schedule.engine call.frame.reflection (recipeInductionSigma c)
      2 (recipeInductionSigma c / 16) call.frame.decay
      call.frame.lower call.frame.upper call.frame.lower_pos hupper).choose_spec.2
  have hparent : call.rank ≤ call.rankBound :=
    (parameterCoreRank_lt_bound
      (σ := recipeInductionSigma c) (W := 2) (padding := recipeInductionSigma c / 16)
      call.node.parameters (recipeInduction_budget (c := c)).1 call.width_le).le
  intro side b ξ
  apply controls call.Cp call.Hp call.request.height regular.minimumCp
    regular.heightDegree_nonneg call.request.height_nonneg
    call.node.parameters (N.childParameters side b) (N.childData side b ξ)
    hparent (childRank_lt N geometry side b ξ) call.childOrders
  · exact call.fixedRange.childOrders_euler
      (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
      ∅ call.childOrder call.frame.decay
  · have hwindow := windows side b ξ
    simpa only [Call.childWindow, regular.lower, regular.upper, Call.rankBound, Call.rank]
      using hwindow

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.childRank_lt
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.profileInvariant_of_windows
