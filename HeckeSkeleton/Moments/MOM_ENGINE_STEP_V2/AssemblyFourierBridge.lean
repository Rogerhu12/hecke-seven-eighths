import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyLeafConstruction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyCalibrationProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalChildFourierControl

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fourier atom control for the same original normalized leaves

The zero-frequency data are the same selected original calibration.
Their global original-field identities construct the logarithmic
profiles through CalibrationProfiles.OriginalFields. N6 supplies the
radii of these same selected capacities.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open Blueprint EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem originalCalibration_allowed_eq_zero
    {packet : RawLeafPacket call p}
    (seed : OrdinarySeed packet) (input : ProfileInput call)
    (support : seed.ordinary.PassiveSupport input)
    (side : Bool) (a : support.labels side) (rectangle : Bool)
    (D : OriginalCalibration call (seed.canonicalSource input support side a rectangle))
    (spec : OriginalCalibrationSpec seed input support side a rectangle D)
    (ξ : EngineParameter) :
    (D.calibration.data ξ).allowedRow = (D.calibration.data 0).allowedRow := by
  funext u
  exact propext ((spec.allowed_exact ξ u).trans (spec.allowed_exact 0 u).symm)

/-- Project the original global identities from the same N3
specification. No additional task hypothesis is introduced. -/
theorem originalFields_of_spec
    {packet : RawLeafPacket call p}
    (seed : OrdinarySeed packet) (input : ProfileInput call)
    (support : seed.ordinary.PassiveSupport input)
    (side : Bool) (a : support.labels side) (rectangle : Bool)
    (D : OriginalCalibration call (seed.canonicalSource input support side a rectangle))
    (spec : OriginalCalibrationSpec seed input support side a rectangle D) :
    CalibrationProfiles.OriginalFields
      (seed := seed) (input := input) (support := support)
      (side := side) (a := a) (rectangle := rectangle) D where
  inverseBackground := spec.inverse_background
  direction := spec.direction
  rowCharacter ξ u := by
    rw [spec.correction, spec.moving, spec.sector]
    exact spec.row_character ξ u
  allowed := originalCalibration_allowed_eq_zero seed input support side a rectangle D spec
  inverse_profile := spec.inverse_profile
  left_profile := spec.left_profile
  right_profile := spec.right_profile
  prime_profile := spec.prime_profile
  slotCoefficient := spec.slot_coefficient

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable {geometry : GeometryFamily second}
variable {frame : SourceFrame} {orders : Finset (ℕ × ℕ)}

/-- Internal composition from the original-field views of the same
selected calibrations. The final task-facing wrapper derives these
views from its existing N3 specifications. -/
noncomputable def leafFamilyFourierControl_of_originalFields
    (input : ProfileInput call) (raw : RawFamily geometry)
    (choices : FullKappaChoices c p.loss)
    (W : UniformProfileWindowCertificate c frame CalibrationConstruction.shape orders)
    (horders : call.childOrders ⊆ orders)
    (leaves : ∀ j : Fin raw.count,
      LeafNormalization (raw.packet j) input choices W horders)
    (fields : ∀ (j : Fin raw.count) (side : Bool)
      (a : (leaves j).support.labels side) (rectangle : Bool),
      CalibrationProfiles.OriginalFields
        (seed := (leaves j).seed) (input := input)
        (support := (leaves j).support) (side := side) (a := a)
        (rectangle := rectangle) ((leaves j).calibrations.side side a rectangle)) :
    let N := canonicalMassData raw input choices (fun j => (leaves j).massPacket)
    N.family.FourierAtomControl N.labels W.degree W.degree W.degree W.degree := by
  let N := canonicalMassData raw input choices (fun j => (leaves j).massPacket)
  change N.family.FourierAtomControl N.labels W.degree W.degree W.degree W.degree
  refine CanonicalLogProfiles.familyFourierControl N.family N.labels
    (fun b => (fields b.1 false b.2.1 b.2.2.2.1).profiles)
    (fun b => (fields b.1 true b.2.2.1 b.2.2.2.2).profiles)
    (fun _ => 0) (fun _ => 0) ?_ ?_ ?_ ?_
    (fun b => ((leaves b.1).normalization false b.2.1 b.2.2.2.1).profiles.coefficient)
    (fun b => ((leaves b.1).normalization true b.2.2.1 b.2.2.2.2).profiles.coefficient)
    ?_ ?_ W.degree W.degree W.degree W.degree ?_ ?_
  · intro b ξ
    exact (fields b.1 false b.2.1 b.2.2.2.1).data_eq_moving ξ
  · intro b ξ
    exact (fields b.1 true b.2.2.1 b.2.2.2.2).data_eq_moving ξ
  · intro b ξ
    exact ((leaves b.1).calibration_actual false b.2.1 b.2.2.2.1).height ξ
  · intro b ξ
    exact ((leaves b.1).calibration_actual true b.2.2.1 b.2.2.2.2).height ξ
  · intro b _
    exact ((leaves b.1).normalization false b.2.1 b.2.2.2.1).profiles.coefficient_nonnegative
  · intro b _
    exact ((leaves b.1).normalization true b.2.2.1 b.2.2.2.2).profiles.coefficient_nonnegative
  · intro b _ z
    simpa only [WithLp.ofLp_toLp,
      ActualAllocatedSource.Calibration.FullKappaProfileInput.coefficient,
      ActualAllocatedSource.Calibration.FullKappaProfileInput.factor] using
      ((leaves b.1).normalization false b.2.1 b.2.2.2.1).capacity_radius (WithLp.toLp 2 z)
  · intro b _ z
    simpa only [WithLp.ofLp_toLp,
      ActualAllocatedSource.Calibration.FullKappaProfileInput.coefficient,
      ActualAllocatedSource.Calibration.FullKappaProfileInput.factor] using
      ((leaves b.1).normalization true b.2.2.1 b.2.2.2.2).capacity_radius (WithLp.toLp 2 z)

/-- The same N3 specifications and the same N6 capacities provide
Fourier atom control with the original common N5 degree. -/
noncomputable def leafFamilyFourierControl
    (input : ProfileInput call) (raw : RawFamily geometry)
    (choices : FullKappaChoices c p.loss)
    (W : UniformProfileWindowCertificate c frame CalibrationConstruction.shape orders)
    (horders : call.childOrders ⊆ orders)
    (leaves : ∀ j : Fin raw.count,
      LeafNormalization (raw.packet j) input choices W horders) :
    let N := canonicalMassData raw input choices (fun j => (leaves j).massPacket)
    N.family.FourierAtomControl N.labels W.degree W.degree W.degree W.degree := by
  exact leafFamilyFourierControl_of_originalFields input raw choices W horders leaves
    (fun j side a rectangle =>
      originalFields_of_spec (leaves j).seed input (leaves j).support
        side a rectangle ((leaves j).calibrations.side side a rectangle)
        ((leaves j).calibration_actual side a rectangle))

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.originalCalibration_allowed_eq_zero
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.originalFields_of_spec
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.leafFamilyFourierControl_of_originalFields
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.leafFamilyFourierControl
