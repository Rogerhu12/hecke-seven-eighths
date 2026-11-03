import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalCalibration

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

/-- N3: the literal canonical residual source, all original arithmetic
atoms, exact finite costs and global original profile formulas. -/
theorem original_calibration (c : TargetContext K) (p : SourceParameters c) :
    OriginalCalibrationTask c p := by
  intro call input packet hpacket seed support canonical masks
  refine ⟨CanonicalCalibration.family seed input support hpacket canonical masks, ?_⟩
  intro side a rectangle
  let profiles := CanonicalCalibration.dictionary seed input support hpacket canonical masks
    side a rectangle
  exact {
    inverse_background := fun _ => rfl
    direction := fun _ => rfl
    row_character := fun _ _ => rfl
    inverse_profile := profiles.inverse_eq
    left_profile := profiles.left_eq
    right_profile := profiles.right_eq
    prime_profile := profiles.prime_eq
    slot_coefficient := fun _ _ => rfl
    parameters := CanonicalCalibration.parameters_eq seed input support hpacket canonical masks
      side a rectangle
    height := CanonicalCalibration.height_eq seed input support hpacket canonical masks side a rectangle
    moving := CanonicalCalibration.moving_eq seed input support hpacket canonical masks side a rectangle
    correction := CanonicalCalibration.correction_eq seed input support hpacket canonical masks
      side a rectangle
    remaining := CanonicalCalibration.remaining_eq seed input support hpacket canonical masks
      side a rectangle
    sector := CanonicalCalibration.sector_eq seed input support hpacket canonical masks side a rectangle
    original_slots := fun _ => rfl
    norm_left := rfl
    norm_right := rfl
    allowed_exact := CanonicalCalibration.allowed_exact seed input support hpacket canonical masks
      side a rectangle
    dictionary := ⟨CanonicalCalibration.dictionary seed input support hpacket canonical masks
      side a rectangle⟩
    timeIndependent := CanonicalCalibration.timeIndependent seed input support hpacket canonical masks
      side a rectangle
    primeSupport := CanonicalCalibration.primeSupport seed input support hpacket canonical masks
      side a rectangle }

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.original_calibration
