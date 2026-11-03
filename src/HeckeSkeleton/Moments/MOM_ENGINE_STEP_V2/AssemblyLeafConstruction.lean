import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyCalibrationBridge
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9ProfileWindowData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedMassContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# One original leaf and its same normalized data

The fixed N4 demand, N5 window certificate and N6 analytic choices are
selected before the moving call. This module then composes the original
N1, N2 and N3 task statements on a single actual packet. It retains the
N2 source comparison and the original N5 windows alongside the N4
geometry and the actual N6 normalization.

The N8 mass packet and the N9 results below are projections of this one
record. Their capacities are definitionally the same. No task theorem
is imported or used to supply a proof.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep Blueprint

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {p : SourceParameters c}

/-- The original N4 conclusion after its fixed-frame demand has been
selected. This is the body of `UniformOriginalCapacityTask`. -/
def CapacityProducer (frame : SourceFrame) (demand : UniformDemand) : Prop :=
  ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
    demand.Ready call input → ∀ packet : RawLeafPacket call p,
    packet.Realizes → ∀ (seed : OrdinarySeed packet)
      (support : seed.ordinary.PassiveSupport input)
      (calibrations : (seed.refinement input support).Calibrations)
      (pattern : Fin packet.block.primeCount → Bool),
    (∀ side a rectangle, N4.CalibrationBinding seed support side a rectangle
      (calibrations.side side a rectangle) pattern) →
    ∃ certificate : OriginalCapacityCertificate seed support calibrations,
      (∀ side a rectangle, (certificate.geometry side a rectangle).pattern = pattern) ∧
      ∀ side a rectangle,
        (certificate.geometry side a rectangle).lengths.rawScaleError = p.loss

theorem capacityProducer_exists (capacity : UniformOriginalCapacityTask c p)
    (frame : SourceFrame) :
    ∃ demand : UniformDemand, CapacityProducer (c := c) (p := p) frame demand :=
  capacity frame

/-- The original N6 conclusion after its analytic choices have been
selected. It is uniform in the call, source and profile window. -/
def FullKappaProducer {loss : ℝ} (choices : FullKappaChoices c loss) : Prop :=
  ∀ (call : Call c) {H Row ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    {R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι}
    {side : Bool} {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter Row k}
    (D : OriginalCalibration call s) (G : SideGeometryData R side s D),
    D.SourceConditions → ∀ (B : ℝ) (J₁ J₂ : ℕ) (windows : FullKappaWindows D B J₁ J₂),
      Nonempty (FullKappaSideResult choices G windows)

theorem fullKappaProducer_exists (normalization : FullKappaTask c)
    (loss : ℝ) (loss_pos : 0 < loss) :
    ∃ choices : FullKappaChoices c loss, FullKappaProducer choices :=
  normalization loss loss_pos

variable {call : Call c} {frame : SourceFrame} {orders : Finset (ℕ × ℕ)}

/-- Every later projection names this same original seed, residual
support, calibration, geometry, window and normalization. -/
structure LeafNormalization (packet : RawLeafPacket call p) (input : ProfileInput call)
    (choices : FullKappaChoices c p.loss)
    (W : UniformProfileWindowCertificate c frame CalibrationConstruction.shape orders)
    (horders : call.childOrders ⊆ orders) where
  seed : OrdinarySeed packet
  support : seed.ordinary.PassiveSupport input
  support_actual : seed.CanonicalSupport input support
  residual_mask : seed.ResidualMaskIdentity
  refinement_bound : seed.RefinementBound input support
  calibrations : (seed.refinement input support).Calibrations
  calibration_actual : ∀ side a rectangle,
    OriginalCalibrationSpec seed input support side a rectangle
      (calibrations.side side a rectangle)
  geometry : OriginalCapacityCertificate seed support calibrations
  scaleError : ∀ side a rectangle,
    (geometry.geometry side a rectangle).lengths.rawScaleError = p.loss
  windows : calibrations.ProfileWindows orders (W.coefficient * input.amplitude * 1)
    (W.costCoefficient * input.amplitude * (1 + 1)) W.degree
  normalization : ∀ side a rectangle,
    FullKappaSideResult choices (geometry.geometry side a rectangle)
      ((windows side a rectangle).toFullKappaWindows horders)

namespace LeafNormalization

variable {packet : RawLeafPacket call p} {input : ProfileInput call}
variable {choices : FullKappaChoices c p.loss}
variable {W : UniformProfileWindowCertificate c frame CalibrationConstruction.shape orders}
variable {horders : call.childOrders ⊆ orders}
variable (L : LeafNormalization packet input choices W horders)

/-- The N8 packet keeps the exact coefficient selected by the original
N5 clipping construction and the same N6 result. -/
noncomputable def massPacket : CanonicalMassPacket packet input choices where
  seed := L.seed
  support := L.support
  support_actual := L.support_actual
  residual_mask := L.residual_mask
  calibrations := L.calibrations
  calibration_actual := L.calibration_actual
  geometry := L.geometry
  coefficient side a rectangle :=
    (L.calibrations.side side a rectangle).profileRadiusCoefficient orders
      (W.coefficient * input.amplitude * 1)
  firstDegree _ _ _ := W.degree
  secondDegree _ _ _ := W.degree
  windows side a rectangle := (L.windows side a rectangle).toFullKappaWindows horders
  normalization := L.normalization

/-- N9 receives the actual geometry and N6 result, retaining the richer
raw/clipped N5 windows needed for its active-source cost. -/
noncomputable def fullKappaResults : L.calibrations.FullKappaResults choices horders L.windows :=
  fun side a rectangle =>
    ⟨L.geometry.geometry side a rectangle, L.normalization side a rectangle⟩

noncomputable def capacities : L.calibrations.Capacities :=
  L.calibrations.fullKappaCapacities L.fullKappaResults

@[simp] theorem massPacket_capacities : L.massPacket.capacities = L.capacities := rfl

@[simp] theorem fullKappaResults_capacities :
    L.calibrations.fullKappaCapacities L.fullKappaResults = L.capacities := rfl

end LeafNormalization

/-- Compose the existing task statements at one call. Every readiness
premise is precisely an original N4 or N5 requirement, to be supplied
by the common U1 input after its fixed demands have been combined. -/
theorem leafNormalization_of_tasks
    (atoms : OriginalAtomTask c p)
    (refinement : PassiveRefinementTask c p)
    (calibration : OriginalCalibrationTask c p)
    (frame : SourceFrame) (demand : UniformDemand)
    (capacity : CapacityProducer (c := c) (p := p) frame demand)
    (choices : FullKappaChoices c p.loss) (normalize : FullKappaProducer choices)
    (orders : Finset (ℕ × ℕ))
    (W : UniformProfileWindowCertificate c frame CalibrationConstruction.shape orders)
    (call : Call c) (input : ProfileInput call)
    (hframe : call.frame = frame) (ready : demand.Ready call input)
    (inputOrders : W.inputOrders ⊆ input.orders) (horders : call.childOrders ⊆ orders)
    (packet : RawLeafPacket call p) (hpacket : packet.Realizes) :
    Nonempty (LeafNormalization packet input choices W horders) := by
  classical
  obtain ⟨seed⟩ := atoms call packet hpacket
  obtain ⟨support, support_actual, residual_mask, refinement_bound⟩ :=
    refinement call input packet hpacket seed
  obtain ⟨calibrations, calibration_actual, bindings⟩ :=
    calibrations_with_bindings calibration call input packet hpacket seed support
      support_actual residual_mask
  obtain ⟨geometry, _pattern, scaleError⟩ :=
    capacity call input hframe ready packet hpacket seed support calibrations
      (CalibrationClass.pattern packet) bindings
  let windows : calibrations.ProfileWindows orders
      (W.coefficient * input.amplitude * 1)
      (W.costCoefficient * input.amplitude * (1 + 1)) W.degree :=
    fun side a rectangle => Classical.choice
      (W.windows call input hframe inputOrders (calibrations.side side a rectangle)
        1 zero_le_one (Classical.choice (calibration_actual side a rectangle).dictionary))
  refine ⟨{
    seed := seed
    support := support
    support_actual := support_actual
    residual_mask := residual_mask
    refinement_bound := refinement_bound
    calibrations := calibrations
    calibration_actual := calibration_actual
    geometry := geometry
    scaleError := scaleError
    windows := windows
    normalization := ?_ }⟩
  intro side a rectangle
  exact Classical.choice
    (normalize call (R := packet.R) (side := side)
      (calibrations.side side a rectangle) (geometry.geometry side a rectangle)
      (geometry.conditions side a rectangle)
      ((calibrations.side side a rectangle).profileRadiusCoefficient orders
        (W.coefficient * input.amplitude * 1)) W.degree W.degree
      ((windows side a rectangle).toFullKappaWindows horders))

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.capacityProducer_exists
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.fullKappaProducer_exists
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.LeafNormalization.massPacket
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.LeafNormalization.fullKappaResults
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.LeafNormalization.massPacket_capacities
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.leafNormalization_of_tasks
