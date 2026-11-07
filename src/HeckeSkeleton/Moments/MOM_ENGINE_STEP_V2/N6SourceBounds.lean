module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SideGeometryData
public import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourceReflection

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N6: the original geometry supplies one fixed analytic norm box

The sixth root remains in the complete support. Its actual pattern
slack and the original scale windows prove the same strict width drop
before any normalized child is selected. Every original retained slot
is still bounded by the parent's fixed mesh.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.N6

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}
variable {H Row ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
variable {R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι}
variable {side : Bool}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter Row k}
variable {D : OriginalCalibration call s}

/-- The original complete-deletion width is bounded without assuming
that any source row or normalized child is nonzero. -/
theorem width_le_two (G : SideGeometryData R side s D) :
    D.calibration.parameters.m + D.calibration.parameters.q ≤ 2 := by
  have hslack := G.nominal.sixthDeletion_slack_of_pattern s.base_gt_one
    R.primes R.primes_injective (selectedMultiplicity R side)
    (oppositeMultiplicity R side) G.selected_pos G.opposite_pos G.pattern
    G.second_eq G.opposite_eq G.unit_eq
  dsimp only at hslack
  have hstep := (recipeInduction_budget (c := c)).1
  have hdrop := G.lengths.scales.sixthDeletion_width_drop s.base_gt_one hstep.le
    (idealLogLength s.base
      (secondSixthRootIdeal R.primes (selectedMultiplicity R side)
        (oppositeMultiplicity R side)).val) hslack.2.1
  have hworking : call.workingParameters.m + call.workingParameters.q =
      call.node.parameters.m + call.node.parameters.q := by
    dsimp only [Call.workingParameters]
    ring
  rw [hworking] at hdrop
  linarith [call.width_le]

/-- The actual full mask, including the remaining deletion and sixth
root, is retained when its exponent is enlarged to the fixed box two. -/
theorem fullJointBudget_two (G : SideGeometryData R side s D)
    (joint : D.recipe.FullJointBudget s.base
      (D.calibration.parameters.m + D.calibration.parameters.q)) :
    D.recipe.FullJointBudget s.base 2 := by
  intro ξ u hu
  exact (joint ξ u hu).trans
    (Real.rpow_le_rpow_of_exponent_le s.base_gt_one.le (width_le_two G))

/-- This is the original slot length, before capacity deletion. -/
theorem childLength_le_mesh (D : OriginalCalibration call s)
    (i : Fin s.allocation.keep.card) :
    s.childLength i ≤ (momentMesh K c.family).val :=
  D.originalSlots.fitsMesh call.fitsMesh (SlotRestriction.index s.allocation.keep i)

/-- The complete pre-removal profile power can use the fixed parent
cap. No smaller number of deleted slots is substituted for this count. -/
theorem keep_card_le_cap (D : OriginalCalibration call s) :
    s.allocation.keep.card ≤ c.geometry.slots := by
  have hkeep : s.allocation.keep.card ≤ k := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ s.allocation.keep
  have horiginal : k ≤ call.node.data.geometry.slotCount := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective D.originalSlots.index D.originalSlots.index.injective
  exact hkeep.trans (horiginal.trans call.slots_le)

theorem calibration_theta (D : OriginalCalibration call s) (ξ : EngineParameter) :
    (D.calibration.data ξ).theta =
      Expansion.Project.canonicalDetectorTheta K (targetCharacter K c) :=
  (D.theta_eq ξ).trans call.source.source.theta_eq

theorem calibration_slot (D : OriginalCalibration call s) (ξ : EngineParameter)
    (i : Fin (D.calibration.data ξ).geometry.slotCount) :
    (D.calibration.data ξ).slotCoefficient i ∈
      Expansion.Project.canonicalDetectorTheta K (targetCharacter K c) := by
  simpa only [call.source.source.theta_eq] using D.slot_characters ξ i

theorem calibration_inverse_slot (D : OriginalCalibration call s) (ξ : EngineParameter)
    (i : Fin (D.calibration.data ξ).geometry.slotCount) :
    ((D.calibration.data ξ).slotCoefficient i)⁻¹ ∈
      Expansion.Project.canonicalDetectorTheta K (targetCharacter K c) :=
  canonicalTheta_inv_mem (calibration_slot D ξ i)

theorem calibration_totalLength (D : OriginalCalibration call s) (ξ : EngineParameter) :
    D.calibration.parameters.z = (D.calibration.data ξ).geometry.totalLength := by
  apply D.calibration.slot_sum.trans
  symm
  apply length_totalLength_eq (D.calibration.data ξ) s.allocation.keep.card
    (D.calibration.count ξ) s.childLength
  exact D.calibration.clipped_lengths ξ

end HeckeSkeleton.Moments.EngineStepV2.N6

#print axioms HeckeSkeleton.Moments.EngineStepV2.N6.width_le_two
#print axioms HeckeSkeleton.Moments.EngineStepV2.N6.fullJointBudget_two
#print axioms HeckeSkeleton.Moments.EngineStepV2.N6.childLength_le_mesh
#print axioms HeckeSkeleton.Moments.EngineStepV2.N6.keep_card_le_cap
