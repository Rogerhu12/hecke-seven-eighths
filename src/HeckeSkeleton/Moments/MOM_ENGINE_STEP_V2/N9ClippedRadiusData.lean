module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9RadiusData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalClippedProfileBounds

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The literal N5b clipping coefficient in the N9 radius

The two dilation factors are computed from each original source and
its original calibration.  Only actual active labels have a uniform
coefficient bound.  No assertion about vanishing inactive profiles or
uniformly bounded inactive dilation factors is needed.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField MeasureTheory EngineStep CanonicalFullKappaPrime
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

namespace NormalizedData

variable (N : NormalizedData call) (orders : Finset (ℕ × ℕ))

def leftClippingCoefficient (b : N.Label) : ℝ :=
  CanonicalLogProfiles.clippingCoefficient
    (max
      (plainClippingFactor (N.family.leftSource b).base
        (N.family.leftCalibration b).parameters.n₁)
      (plainClippingFactor (N.family.leftSource b).base
        (N.family.leftCalibration b).parameters.n₂)) orders

def rightClippingCoefficient (b : N.Label) : ℝ :=
  CanonicalLogProfiles.clippingCoefficient
    (max
      (plainClippingFactor (N.family.rightSource b).base
        (N.family.rightCalibration b).parameters.n₁)
      (plainClippingFactor (N.family.rightSource b).base
        (N.family.rightCalibration b).parameters.n₂)) orders

theorem leftClippingCoefficient_one (b : N.Label) :
    1 ≤ N.leftClippingCoefficient orders b :=
  CanonicalLogProfiles.clippingCoefficient_one_le _
    ((plainClippingFactor_one_le _ _ (N.family.leftSource b).base_gt_one.le).trans
      (le_max_left _ _)) orders

theorem rightClippingCoefficient_one (b : N.Label) :
    1 ≤ N.rightClippingCoefficient orders b :=
  CanonicalLogProfiles.clippingCoefficient_one_le _
    ((plainClippingFactor_one_le _ _ (N.family.rightSource b).base_gt_one.le).trans
      (le_max_left _ _)) orders

end NormalizedData

/-- N5b supplies the original raw coefficients and the displayed
active bounds for their actual clipped coefficients.  N6 supplies the
two literal capacity identities for those same clipped coefficients.
The analytic radius is fixed separately before the moving call. -/
structure ClippedKernelRadiusData (N : NormalizedData call)
    (orders : Finset (ℕ × ℕ)) (cap J₁₁ J₁₂ J₂₁ J₂₂ : ℕ)
    (B radius : ℝ) where
  leftRawCoefficient : N.Label → ℝ
  rightRawCoefficient : N.Label → ℝ
  left_raw_nonneg : ∀ b : N.Active, 0 ≤ leftRawCoefficient b.val
  right_raw_nonneg : ∀ b : N.Active, 0 ≤ rightRawCoefficient b.val
  left_active_bound : ∀ b : N.Active,
    enlargedCoefficient (leftRawCoefficient b.val)
      (N.leftClippingCoefficient orders b.val) ≤ B
  right_active_bound : ∀ b : N.Active,
    enlargedCoefficient (rightRawCoefficient b.val)
      (N.rightClippingCoefficient orders b.val) ≤ B
  left_slots : ∀ b : N.Active, (N.family.leftSource b.val).allocation.keep.card ≤ cap
  right_slots : ∀ b : N.Active, (N.family.rightSource b.val).allocation.keep.card ≤ cap
  left_radius : ∀ (b : N.Active) z,
    (N.family.leftCapacity b.val).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius
        (enlargedCoefficient
          (enlargedCoefficient (leftRawCoefficient b.val)
            (N.leftClippingCoefficient orders b.val)) radius) J₁₁ J₁₂ z
  right_radius : ∀ (b : N.Active) z,
    (N.family.rightCapacity b.val).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius
        (enlargedCoefficient
          (enlargedCoefficient (rightRawCoefficient b.val)
            (N.rightClippingCoefficient orders b.val)) radius) J₂₁ J₂₂ z

namespace ClippedKernelRadiusData

variable {N : NormalizedData call} {orders : Finset (ℕ × ℕ)}
variable {cap J₁₁ J₁₂ J₂₁ J₂₂ : ℕ} {B radius : ℝ}
variable (D : ClippedKernelRadiusData N orders cap J₁₁ J₁₂ J₂₁ J₂₂ B radius)

/-- Forget only the computation of the N5b coefficients.  The actual
capacities, sources, kernels and original normalizers are unchanged. -/
def toKernelRadiusData : KernelRadiusData N cap J₁₁ J₁₂ J₂₁ J₂₂ B radius where
  leftCoefficient b := enlargedCoefficient (D.leftRawCoefficient b)
    (N.leftClippingCoefficient orders b)
  rightCoefficient b := enlargedCoefficient (D.rightRawCoefficient b)
    (N.rightClippingCoefficient orders b)
  left_nonneg b := enlargedCoefficient_nonneg (D.left_raw_nonneg b)
    (zero_le_one.trans (N.leftClippingCoefficient_one orders b.val))
  right_nonneg b := enlargedCoefficient_nonneg (D.right_raw_nonneg b)
    (zero_le_one.trans (N.rightClippingCoefficient_one orders b.val))
  left_le := D.left_active_bound
  right_le := D.right_active_bound
  left_slots := D.left_slots
  right_slots := D.right_slots
  left_radius := D.left_radius
  right_radius := D.right_radius

end ClippedKernelRadiusData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
