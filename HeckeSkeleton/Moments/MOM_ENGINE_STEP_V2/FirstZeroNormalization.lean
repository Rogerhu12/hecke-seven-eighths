import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroInputBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T1: paying the original normalization with fixed small exponents

The complete original column length cancels against the square root in
the powerful count. The working row length is at most the original
parent width. Only three copies of the prescribed small source loss
remain, paid inside the original terminal reserve.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof

open NumberField HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K}

def firstColumnExponent (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  2 + recipeInductionSigma c / 16 + p.loss

theorem firstColumnExponent_pos (p : SourceParameters c) :
    0 < firstColumnExponent c p := by
  have hs : 0 < recipeInductionSigma c := (recipeInduction_budget (c := c)).1
  dsimp only [firstColumnExponent]
  linarith [p.loss_pos]

def firstCountingExponent (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  p.loss / (2 * firstColumnExponent c p)

theorem firstCountingExponent_pos (p : SourceParameters c) :
    0 < firstCountingExponent c p :=
  div_pos p.loss_pos (mul_pos (by norm_num) (firstColumnExponent_pos p))

theorem first_counting_loss_le (p : SourceParameters c) (call : Call c) :
    2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
      call.node.parameters.z + p.loss) * firstCountingExponent c p ≤ p.loss := by
  have hL := original_total_le call
  have hbound : 2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
      call.node.parameters.z + p.loss) ≤ 2 * firstColumnExponent c p := by
    dsimp only [firstColumnExponent]
    linarith
  have hproduct : 2 * firstColumnExponent c p * firstCountingExponent c p = p.loss := by
    dsimp only [firstCountingExponent]
    have hbase : firstColumnExponent c p ≠ 0 := (firstColumnExponent_pos p).ne'
    field_simp [hbase] <;> ring
  exact (mul_le_mul_of_nonneg_right hbound (firstCountingExponent_pos p).le).trans_eq hproduct

/-- One amplitude pays both the literal divisor-weighted profile and
the original-origin point profile. Its central square root is exact. -/
theorem first_profile_normalization
    (Z P C L m δ profile mask : ℝ)
    (hZ : 1 ≤ Z) (hP : 0 ≤ P) (hC : 0 ≤ C) (hm : 0 ≤ m) (hδ : 0 ≤ δ)
    (hprofile : profile ≤ P * Z ^ (-L)) (hprofile0 : 0 ≤ profile)
    (hmask : mask ≤ C * Z ^ (m + δ)) (hmask0 : 0 ≤ mask) :
    profile * mask ≤ ((1 + C) * P * Z ^ (m + 2 * δ)) /
        Real.sqrt (Z ^ (2 * (L + δ))) ∧
    profile ≤ ((1 + C) * P * Z ^ (m + 2 * δ)) /
        Real.sqrt (Z ^ (2 * (L + δ))) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hsqrt : Real.sqrt (Z ^ (2 * (L + δ))) = Z ^ (L + δ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZpos.le]
    congr 1
    ring
  have hnorm : ((1 + C) * P * Z ^ (m + 2 * δ)) /
      Real.sqrt (Z ^ (2 * (L + δ))) =
        (1 + C) * P * Z ^ (-L + m + δ) := by
    rw [hsqrt, mul_div_assoc, ← Real.rpow_sub hZpos]
    congr 2
    ring
  rw [hnorm]
  constructor
  · calc
      profile * mask ≤ (P * Z ^ (-L)) * (C * Z ^ (m + δ)) :=
        mul_le_mul hprofile hmask hmask0 (mul_nonneg hP (Real.rpow_nonneg hZpos.le _))
      _ = C * P * Z ^ (-L + m + δ) := by
        simp only [Real.rpow_add hZpos]
        ring
      _ ≤ (1 + C) * P * Z ^ (-L + m + δ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
        exact mul_le_mul_of_nonneg_right (by linarith) hP
  · calc
      profile ≤ P * Z ^ (-L) := hprofile
      _ ≤ P * Z ^ (-L + m + δ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hP
      _ ≤ (1 + C) * P * Z ^ (-L + m + δ) := by
        have hPZ : 0 ≤ P * Z ^ (-L + m + δ) :=
          mul_nonneg hP (Real.rpow_nonneg hZpos.le _)
        simpa only [one_mul, mul_assoc] using
          mul_le_mul_of_nonneg_right (by linarith : 1 ≤ 1 + C) hPZ

/-- The fixed counting exponent consumes at most one source loss.
The central exponent has canceled before the parent width is divided. -/
theorem first_parent_normalization (p : SourceParameters c) (call : Call c)
    (C P : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P) :
    (C * (P * call.base ^ (call.workingParameters.m + 2 * p.loss)) *
      (call.base ^ (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
        call.node.parameters.z + p.loss))) ^ firstCountingExponent c p) /
      call.parentNormalizer ≤ C * P * call.base ^ recipeInductionTerminalLoss c := by
  have hq := working_q_nonneg call
  have hw := working_width call
  have hcount := first_counting_loss_le p call
  have hterminal := source_loss_paid_by_terminal p
  have hexponent : call.workingParameters.m + 2 * p.loss +
      2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
        call.node.parameters.z + p.loss) * firstCountingExponent c p -
      (call.node.parameters.m + call.node.parameters.q) ≤ recipeInductionTerminalLoss c := by
    linarith [p.loss_pos]
  rw [← Real.rpow_mul call.base_pos.le]
  calc
    _ = C * P * (call.base ^ (call.workingParameters.m + 2 * p.loss) *
        call.base ^ (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z + p.loss) * firstCountingExponent c p)) /
        call.base ^ (call.node.parameters.m + call.node.parameters.q) := by
      dsimp only [Call.parentNormalizer]
      ring
    _ = C * P * call.base ^ (call.workingParameters.m + 2 * p.loss +
        2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z + p.loss) * firstCountingExponent c p -
        (call.node.parameters.m + call.node.parameters.q)) := by
      rw [← Real.rpow_add call.base_pos, mul_div_assoc, ← Real.rpow_sub call.base_pos]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hexponent) (mul_nonneg hC hP)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof
