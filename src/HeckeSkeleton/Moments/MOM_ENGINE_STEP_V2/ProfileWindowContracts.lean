module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalClippedProfileBounds

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N5b: actual raw and clipped windows with their computed radius

Draft contract following PR #31's window and ownership review.
Only the original global dictionary is an input, supplied by N3.
N5b constructs the clipped representatives for every actual label.
The clipping coefficient is computed from the same calibration's
scales; its uniform cost bound is asserted on the actual active source.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {H : Type} {k : ℕ}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}

namespace OriginalCalibration

/-- The coefficient pays the two literal clipping factors, including
the constant term in the original polynomial radius. -/
def profileRadiusCoefficient (D : OriginalCalibration call s)
    (orders : Finset (ℕ × ℕ)) (rawCoefficient : ℝ) : ℝ :=
  CanonicalFullKappaPrime.enlargedCoefficient rawCoefficient
    (CanonicalLogProfiles.clippingCoefficient
      (max (plainClippingFactor s.base D.calibration.parameters.n₁)
        (plainClippingFactor s.base D.calibration.parameters.n₂)) orders)

end OriginalCalibration

/-- Original positive support is retained for N7b. Clipping starts in
the broad window; no second division of the original lower endpoint is
performed here. Both bounds use the same computed polynomial radius. -/
structure RawClippedProfileWindows (D : OriginalCalibration call s)
    (orders : Finset (ℕ × ℕ)) (rawCoefficient uniformCost : ℝ) (degree : ℕ) where
  coefficient_nonneg : 0 ≤ D.profileRadiusCoefficient orders rawCoefficient
  original : ∀ ξ, RawProfileWindow Set.univ Set.univ call.window orders
    (D.calibration.data ξ)
    (polynomialProfileRadius (D.profileRadiusCoefficient orders rawCoefficient)
      degree degree (WithLp.ofLp ξ))
  clipped : ∀ ξ, RawProfileWindow Set.univ Set.univ
    (Set.Icc 0 (2 * call.prepared.upper)) orders (D.calibration.clippedData ξ)
    (polynomialProfileRadius (D.profileRadiusCoefficient orders rawCoefficient)
      degree degree (WithLp.ofLp ξ))
  active_cost : (¬ ∀ ξ, s.energy (σ := Arithmetic.embedding c) ξ = 0) →
    D.profileRadiusCoefficient orders rawCoefficient ≤ uniformCost

/-- All orders, degrees and uniform costs precede the moving call.
The actual clipping radius is allowed to use the original source's
scales, and its cost is uniformly paid on the genuine active carrier. -/
structure UniformProfileWindowCertificate (c : TargetContext K)
    (frame : SourceFrame) (shape : ProfileShape) (orders : Finset (ℕ × ℕ)) where
  inputOrders : Finset (ℕ × ℕ)
  degree : ℕ
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  costCoefficient : ℝ
  costCoefficient_pos : 0 < costCoefficient
  windows : ∀ (call : Call c) (input : ProfileInput call),
    call.frame = frame → inputOrders ⊆ input.orders →
    ∀ {H : Type} {k : ℕ}
      {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}
      (D : OriginalCalibration call s) (scalarBound : ℝ),
      0 ≤ scalarBound → D.RawDictionary input shape scalarBound call.window →
      Nonempty (RawClippedProfileWindows D orders
        (coefficient * input.amplitude * scalarBound)
        (costCoefficient * input.amplitude * (1 + scalarBound)) degree)

def ProfileWindowTask (c : TargetContext K) : Prop :=
  ∀ (frame : SourceFrame) (shape : ProfileShape) (orders : Finset (ℕ × ℕ)),
    Nonempty (UniformProfileWindowCertificate c frame shape orders)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
