module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The preselected source losses fit the original reserve

All estimates use the reserve already stored in `SourceParameters`.
The mesh in the original edge loss is positive, so half of that edge
loss pays the whole reserve.  The multiplicative form also pays the
fixed slot-dependent exponents in N8b and the single N6 radius loss.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField EngineStep EngineInduction EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K}

theorem momentMesh_le_sourceReserve (c : TargetContext K) :
    (momentMesh K c.family).val ≤ sourceReserve c.family.lamA := by
  obtain ⟨_, _, _, _, _, hmesh, _, _, _, _⟩ :=
    HeckePort.Schedule.bounds 2
      (HeckePort.Schedule.finalSourceCap 2 0 1 c.family.lamA) 1 c.family.lamA
      (by norm_num)
      (HeckePort.Schedule.finalSourceCap_nonneg 2 0 1 c.family.lamA
        (by norm_num) le_rfl)
      zero_le_one c.family.lamA_pos
  exact hmesh

theorem sourceReserve_le_edgeLoss_half (c : TargetContext K) :
    sourceReserve c.family.lamA ≤ recipeInductionEdgeLoss c / 2 := by
  have hmesh := (momentMesh K c.family).property.le
  unfold recipeInductionEdgeLoss
  linarith

namespace SourceParameters

variable (p : SourceParameters c)

theorem loss_mul_le_reserve (a : ℝ)
    (ha : a ≤ 4096 * ((c.geometry.slots : ℝ) + 1)) :
    a * p.loss ≤ sourceReserve c.family.lamA :=
  (mul_le_mul_of_nonneg_right ha p.loss_pos.le).trans p.loss_reserve

theorem loss_mul_le_edgeLoss_half (a : ℝ)
    (ha : a ≤ 4096 * ((c.geometry.slots : ℝ) + 1)) :
    a * p.loss ≤ recipeInductionEdgeLoss c / 2 :=
  (p.loss_mul_le_reserve a ha).trans (sourceReserve_le_edgeLoss_half c)

theorem loss_le_edgeLoss_half : p.loss ≤ recipeInductionEdgeLoss c / 2 := by
  have hs : 0 ≤ (c.geometry.slots : ℝ) := Nat.cast_nonneg _
  simpa only [one_mul] using p.loss_mul_le_edgeLoss_half 1 (by linarith)

/-- After the two losses in the N8b denominator are paid, one original
positive source loss still remains available. -/
theorem loss_le_arithmeticRemainder :
    p.loss ≤ recipeInductionEdgeLoss c / 2 - 2 * p.loss := by
  have hs : 0 ≤ (c.geometry.slots : ℝ) := Nat.cast_nonneg _
  have h := p.loss_mul_le_edgeLoss_half 3 (by linarith)
  linarith

theorem arithmeticRemainder_pos :
    0 < recipeInductionEdgeLoss c / 2 - 2 * p.loss :=
  p.loss_pos.trans_le p.loss_le_arithmeticRemainder

/-- The actual fixed mesh can be paid together with the arithmetic
losses.  Half the original reserve remains after its largest possible
mesh cost, and the displayed source reserve pays the remaining powers. -/
theorem mesh_loss_le_arithmeticRemainder (κ a : ℝ) (hκ : κ ≤ 1)
    (ha : 2 * (a + 2) ≤ 4096 * ((c.geometry.slots : ℝ) + 1)) :
    κ * (momentMesh K c.family).val + a * p.loss ≤
      recipeInductionEdgeLoss c / 2 - 2 * p.loss := by
  have hmesh := momentMesh_le_sourceReserve c
  have hκmesh : κ * (momentMesh K c.family).val ≤ (momentMesh K c.family).val := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hκ (momentMesh K c.family).property.le
  have hpaid := p.loss_mul_le_reserve (2 * (a + 2)) ha
  unfold recipeInductionEdgeLoss
  nlinarith

theorem mesh_slot_loss_le_arithmeticRemainder (κ : ℝ) (hκ : κ ≤ 1) :
    κ * (momentMesh K c.family).val +
        (128 * ((c.geometry.slots : ℝ) + 1)) * p.loss ≤
      recipeInductionEdgeLoss c / 2 - 2 * p.loss := by
  apply p.mesh_loss_le_arithmeticRemainder κ _ hκ
  have hs : 0 ≤ (c.geometry.slots : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- Any fixed nonnegative combination of the two actual cutoff powers,
the tilt and the radius loss is paid once by the original reserve. -/
theorem weighted_losses_le_reserve (a b d e : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hbudget : a + b + d + e ≤ 4096 * ((c.geometry.slots : ℝ) + 1)) :
    a * p.firstCutoffExponent + b * p.secondCutoffExponent +
        d * p.tilt + e * p.loss ≤ sourceReserve c.family.lamA := by
  calc
    _ ≤ a * p.loss + b * p.loss + d * p.loss + e * p.loss := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left p.firstCutoff_small ha)
            (mul_le_mul_of_nonneg_left p.secondCutoff_small hb))
          (mul_le_mul_of_nonneg_left p.tilt_le_loss hd)) le_rfl
    _ = (a + b + d + e) * p.loss := by ring
    _ ≤ sourceReserve c.family.lamA := p.loss_mul_le_reserve _ hbudget

theorem weighted_losses_le_edgeLoss_half (a b d e : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hbudget : a + b + d + e ≤ 4096 * ((c.geometry.slots : ℝ) + 1)) :
    a * p.firstCutoffExponent + b * p.secondCutoffExponent +
        d * p.tilt + e * p.loss ≤ recipeInductionEdgeLoss c / 2 :=
  (p.weighted_losses_le_reserve a b d e ha hb hd hbudget).trans
    (sourceReserve_le_edgeLoss_half c)

theorem rpow_loss_mul_le_edgeLoss_half (Z a : ℝ) (hZ : 1 ≤ Z)
    (ha : a ≤ 4096 * ((c.geometry.slots : ℝ) + 1)) :
    Z ^ (a * p.loss) ≤ Z ^ (recipeInductionEdgeLoss c / 2) :=
  Real.rpow_le_rpow_of_exponent_le hZ (p.loss_mul_le_edgeLoss_half a ha)

end SourceParameters
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceParameters.loss_le_edgeLoss_half
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceParameters.weighted_losses_le_reserve
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceParameters.arithmeticRemainder_pos
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceParameters.mesh_loss_le_arithmeticRemainder
