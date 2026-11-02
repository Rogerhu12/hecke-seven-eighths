import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChildInvariantData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationData
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActiveChildAnnulus

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N7b: the original window and the actual frozen capacity child

The original seminorm orders are allowed to depend on the physical
side. We use the single-child form of the active-annulus theorem, so
neither those orders nor the pre-removal radius have to be replaced.
The prepared upper endpoint is fixed by the original ProfileInput.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N7bProfileTransport

open NumberField HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

/-- The actual scheduled upper endpoint, before any transformed source
is selected, supplies the numerical hypothesis for active clipping. -/
theorem upper_bound (input : ProfileInput call) :
    1 ≤ 2 * call.prepared.upper := by
  have hp : (1 : ℝ) ≤ 2 ^ (call.rankBound - call.rank) :=
    one_le_pow₀ (by norm_num)
  have hu : 0 ≤ call.frame.upper := by linarith [call.frame.upper_large]
  have hmul : call.frame.upper ≤
      call.frame.upper * (2 : ℝ) ^ (call.rankBound - call.rank) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hu
  rw [input.regular.upper, rankedAnnulusUpper]
  linarith [call.frame.upper_large]

variable {H : Type} {k : ℕ}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}
variable {D : OriginalCalibration call s}
variable {G : D.calibration.NormalizedCapacityData}

/-- Strengthen only the support proof on the already selected child.
Its radius, removed slots, smooth representatives and frozen height
are exactly the ones supplied by the original capacity construction. -/
theorem active_windows
    {originalOrders : Finset (ℕ × ℕ)} {originalBudget : EngineParameter → ℝ}
    (original : ∀ ξ, RawProfileWindow Set.univ Set.univ call.window
      originalOrders (D.calibration.data ξ) (originalBudget ξ))
    (clipped : ∀ ξ, RawProfileWindow Set.univ Set.univ
      (Set.Icc 0 (2 * call.prepared.upper)) call.childOrders
        (D.calibration.clippedData ξ) (G.radius ξ))
    (out : G.Child) (hupper : 1 ≤ 2 * call.prepared.upper)
    (hactive : ¬ ∀ ξ, s.energy (σ := Arithmetic.embedding c) ξ = 0)
    (ξ : EngineParameter) :
    InFixedProfileWindow Set.univ Set.univ call.childWindow call.childOrders
      (out.frozenData ξ) := by
  have hlower : 0 ≤ call.prepared.lower / 2 :=
    div_nonneg call.prepared.lower_pos.le (by norm_num)
  exact (ActiveChildAnnulus.active_child_windows out
    (lo := call.prepared.lower / 2) (hi := 2 * call.prepared.upper)
    hlower hupper original clipped
    (fun _ _ _ => Set.mem_univ _) (fun _ => Set.mem_univ _) hactive ξ).2

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N7bProfileTransport

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N7bProfileTransport.upper_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N7bProfileTransport.active_windows
