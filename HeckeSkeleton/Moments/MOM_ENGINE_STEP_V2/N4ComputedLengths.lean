import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4ScaleWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SideGeometryData
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: the same actual source supplies its complete length binding

Both formal rectangles receive a length binding. The scale error is
computed from their actual positive scale product, so an absent rectangle
does not require an invented small scale bound. On an original rectangle
with the two-extraction window, the computed error is the original small
error exactly. Capacity and slot removal remain the base constructors.

Paper: Section 4.8, lines 2908--2919 and 2927--2946.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

/-- This error is a fixed function of the original scale product. -/
def computedScaleError (Z product degree error : ℝ) : ℝ :=
  max error (Real.logb Z product - degree)

theorem computedScaleError_nonneg (Z product degree error : ℝ) (herr : 0 ≤ error) :
    0 ≤ computedScaleError Z product degree error :=
  herr.trans (le_max_left _ _)

theorem product_le_computedScaleError (Z product degree error : ℝ) (hZ : 1 < Z) :
    product ≤ Z ^ (degree + computedScaleError Z product degree error) := by
  by_cases hp : 0 < product
  · apply (Real.logb_le_iff_le_rpow hZ hp).mp
    have hm := le_max_right error (Real.logb Z product - degree)
    change Real.logb Z product ≤ degree + max error (Real.logb Z product - degree)
    linarith
  · exact (le_of_not_gt hp).trans
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

theorem computedScaleError_eq_of_product_bound (Z product degree error : ℝ)
    (hZ : 1 < Z) (hp : 0 < product)
    (hproduct : product ≤ Z ^ (degree + error)) :
    computedScaleError Z product degree error = error := by
  apply max_eq_left
  have hlog := (Real.logb_le_iff_le_rpow hZ hp).mpr hproduct
  linarith

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}
variable {H : Type} {k : ℕ}
variable (s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k)

def sourceScaleProduct : ℝ := s.scale₁ * s.scale₂ * s.base ^ s.beforeLength

def sourceRawError (degree error : ℝ) : ℝ :=
  computedScaleError s.base (sourceScaleProduct s) degree error

variable {s} (D : OriginalCalibration call s)

include D in
theorem sourceScaleProduct_pos : 0 < sourceScaleProduct s := by
  have hleftNorm : 0 < idealNorm K (s.allocation.plainDivisor 0) := idealNorm_pos K _
  have hrightNorm : 0 < idealNorm K (s.allocation.plainDivisor (Fin.succ 0)) :=
    idealNorm_pos K _
  have hleft : s.scale₁ = s.base ^ D.calibration.parameters.n₁ *
      idealNorm K (s.allocation.plainDivisor 0) :=
    ((eq_div_iff hleftNorm.ne').mp D.calibration.left_scale).symm
  have hright : s.scale₂ = s.base ^ D.calibration.parameters.n₂ *
      idealNorm K (s.allocation.plainDivisor (Fin.succ 0)) :=
    ((eq_div_iff hrightNorm.ne').mp D.calibration.right_scale).symm
  have hZ : 0 < s.base := zero_lt_one.trans s.base_gt_one
  unfold sourceScaleProduct
  rw [hleft, hright]
  exact mul_pos
    (mul_pos (mul_pos (Real.rpow_pos_of_pos hZ _) hleftNorm)
      (mul_pos (Real.rpow_pos_of_pos hZ _) hrightNorm))
    (Real.rpow_pos_of_pos hZ _)

include D in
theorem sourceRawError_eq_of_product_bound (degree error : ℝ)
    (hproduct : sourceScaleProduct s ≤ s.base ^ (degree + error)) :
    sourceRawError s degree error = error :=
  computedScaleError_eq_of_product_bound s.base (sourceScaleProduct s) degree error
    s.base_gt_one (sourceScaleProduct_pos D) hproduct

variable (p : SourceParameters c)
variable (G : OriginalNominalGeometry (K := K) call.workingParameters s.base
  (recipeInductionSigma c))
variable (rootLength : ℝ)
variable (hm : D.calibration.parameters.m = rowParameter G (12 * p.loss))
variable (hq : D.calibration.parameters.q = supportParameter G (4 * p.loss) rootLength)
variable (direct : G.tag = .direct → call.node.data.geometry.slotCount = 0)

/-- The parent domain, original slot embedding, and N3's exact m/q
identities construct the binding on this same calibration. No row
witness, child capacity, or normalized mass estimate is assumed. -/
def originalSixthLengths :
    D.calibration.OriginalSixthLengthBinding call.node.data call.workingParameters
      (recipeInductionSigma c) G rootLength where
  slots := D.originalSlots
  parent_z := call.domain.total_length
  parent_region := by
    refine ⟨call.domain.kappa_lower, call.domain.kappa_upper, ?_⟩
    rcases call.domain.capacity with hz | hcapacity
    · exact Or.inl hz
    · right
      change call.node.parameters.n₁ + call.node.parameters.n₂ +
          6 * call.node.parameters.κ * call.node.parameters.z ≤
        call.workingParameters.m + call.workingParameters.q
      dsimp only [Call.workingParameters]
      linarith
  kappa := D.kappa_eq
  direct_slots := by
    intro hd
    have hcard : k ≤ call.node.data.geometry.slotCount := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective D.originalSlots.index D.originalSlots.index.injective
    rw [direct hd] at hcard
    exact Nat.eq_zero_of_le_zero hcard
  scales := reparameterizeWindows G
    (endpointWindows G s.base_gt_one (12 * p.loss) (4 * p.loss) rootLength
      (mul_nonneg (by norm_num) p.loss_pos.le)
      (mul_nonneg (by norm_num) p.loss_pos.le) (source_errors_small p))
    hm (congrArg (fun q : ℝ => q - rootLength) hq)
  rawScaleError := sourceRawError s G.skeleton.rawDegree p.loss
  rawScaleError_nonneg :=
    computedScaleError_nonneg s.base (sourceScaleProduct s) G.skeleton.rawDegree p.loss
      p.loss_pos.le
  original_scale_product :=
    product_le_computedScaleError s.base (sourceScaleProduct s) G.skeleton.rawDegree
      p.loss s.base_gt_one

theorem originalSixthLengths_rawError :
    (originalSixthLengths D p G rootLength hm hq direct).rawScaleError =
      sourceRawError s G.skeleton.rawDegree p.loss := by
  rfl

theorem originalSixthLengths_rowError :
    (originalSixthLengths D p G rootLength hm hq direct).scales.rowError = 12 * p.loss := by
  rfl

theorem originalSixthLengths_supportError :
    (originalSixthLengths D p G rootLength hm hq direct).scales.supportError = 4 * p.loss := by
  rfl

theorem originalSixthLengths_rawError_eq
    (hproduct : sourceScaleProduct s ≤ s.base ^ (G.skeleton.rawDegree + p.loss)) :
    (originalSixthLengths D p G rootLength hm hq direct).rawScaleError = p.loss :=
  sourceRawError_eq_of_product_bound D G.skeleton.rawDegree p.loss hproduct

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.product_le_computedScaleError
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.sourceScaleProduct_pos
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.originalSixthLengths
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.originalSixthLengths_rawError_eq
