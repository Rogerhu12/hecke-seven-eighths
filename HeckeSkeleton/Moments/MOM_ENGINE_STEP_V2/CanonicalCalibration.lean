import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationParameters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationClass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Complete calibration of the fixed canonical residual source

The original packet fixes its class, moving list, remaining ideal and
raw parameters. The actual row arithmetic and every global profile are
proved from those fields. This construction does not call a task theorem
or consume a completed calibration as an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalCalibration

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}
variable (seed : OrdinarySeed packet) (input : ProfileInput call)
variable (support : seed.ordinary.PassiveSupport input)
variable (hpacket : packet.Realizes)
variable (canonical : seed.CanonicalSupport input support)
variable (masks : seed.ResidualMaskIdentity)
variable (side : Bool) (a : support.labels side) (rectangle : Bool)

local notation "s" => seed.canonicalSource input support side a rectangle
local notation "pattern" => CalibrationClass.pattern packet
local notation "ν" => CalibrationClass.sector packet

abbrev data : EngineParameter → MomentData K c.family.omega (targetCharacter K c) :=
  CalibrationAtoms.data seed input support side a rectangle pattern ν

include hpacket in
theorem ordinary (h : seed.ordinary.rows.live) :
    (data seed input support side a rectangle 0).rowCharacter ((s).row h).momentIdeal ∉
      call.node.data.theta := by
  change call.localizedSource.source.recipe.correction *
      ((seed.phases.moving true).append
        (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
          (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
          packet.R.rightMultiplicity pattern)).character *
      completeIdealRowCharacter K
        ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        (probeData K c) (momentRowCharacters K c) ν
        ((seed.ordinary.originalSource side false).row h).momentIdeal ∉ call.node.data.theta
  rw [seed.ordinary.originalSource_momentIdeal]
  exact CalibrationClass.ordinary_nonexceptional seed hpacket h

/-- The same constructor serves both sides, both comparison rectangles
and every nonempty actual residual allocation. -/
def original : OriginalCalibration call s :=
  CalibrationAssembly.original seed input support canonical masks side a rectangle
    (CalibrationAtoms.moving seed pattern) (CalibrationAtoms.correction seed)
    (Or.inr (CalibrationAtoms.correction_mem seed)) (fun _ => ν)
    (CalibrationAtoms.remaining seed)
    (CalibrationAtoms.dictionary seed input support side a rectangle pattern ν
      (CalibrationClass.ordinary_pattern seed.ordinary hpacket)
      (CalibrationClass.ordinary_sector seed.ordinary hpacket))
    (CalibrationParameters.parameters seed input support side a rectangle)
    (CalibrationParameters.left_scale seed input support side a rectangle)
    (CalibrationParameters.right_scale seed input support side a rectangle)
    (CalibrationParameters.slot_sum seed input support side a rectangle)
    (fun h _ => CalibrationParameters.cutoff seed input support side a rectangle hpacket h)
    (fun h _ => ordinary seed input support hpacket side a rectangle h)
    (CalibrationParameters.kappa seed input support side a rectangle)

@[simp] theorem data_eq :
    (original seed input support hpacket canonical masks side a rectangle).calibration.data =
      data seed input support side a rectangle := rfl

@[simp] theorem parameters_eq :
    (original seed input support hpacket canonical masks side a rectangle).calibration.parameters =
      CalibrationParameters.parameters seed input support side a rectangle := rfl

@[simp] theorem height_eq (ξ : EngineParameter) :
    (original seed input support hpacket canonical masks side a rectangle).calibration.height ξ =
      0 := rfl

@[simp] theorem moving_eq :
    (original seed input support hpacket canonical masks side a rectangle).recipe.moving =
      CalibrationAtoms.moving seed pattern := rfl

@[simp] theorem correction_eq :
    (original seed input support hpacket canonical masks side a rectangle).recipe.correction =
      CalibrationAtoms.correction seed := rfl

@[simp] theorem remaining_eq :
    (original seed input support hpacket canonical masks side a rectangle).recipe.remaining =
      CalibrationAtoms.remaining seed := rfl

@[simp] theorem sector_eq :
    (original seed input support hpacket canonical masks side a rectangle).recipe.sector =
      fun _ => ν := rfl

def dictionary :
    (original seed input support hpacket canonical masks side a rectangle).RawDictionary
      input CalibrationConstruction.shape 1 call.window :=
  CalibrationConstruction.dictionary seed input support side a rectangle
    (CalibrationAtoms.moving seed pattern) (CalibrationAtoms.correction seed)
    (Or.inr (CalibrationAtoms.correction_mem seed)) (fun _ => ν)
    (CalibrationAtoms.remaining seed)

theorem allowed_exact (ξ : EngineParameter) (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((original seed input support hpacket canonical masks side a rectangle).calibration.data ξ).allowedRow u ↔
      ∃ h ∈ (s).rows, ((s).row h).momentIdeal = u :=
  CalibrationConstruction.allowed_exact seed input support side a rectangle
    (CalibrationAtoms.moving seed pattern) (CalibrationAtoms.correction seed)
    (Or.inr (CalibrationAtoms.correction_mem seed)) (fun _ => ν)
    (CalibrationAtoms.remaining seed) ξ u

theorem timeIndependent (ξ : EngineParameter) :
    ProfileTimeIndependent
      ((original seed input support hpacket canonical masks side a rectangle).calibration.data ξ) :=
  CalibrationConstruction.timeIndependent seed input support side a rectangle
    (CalibrationAtoms.moving seed pattern) (CalibrationAtoms.correction seed)
    (Or.inr (CalibrationAtoms.correction_mem seed)) (fun _ => ν)
    (CalibrationAtoms.remaining seed) ξ

theorem primeSupport (ξ : EngineParameter) :
    PrimeProfileSupport
      ((original seed input support hpacket canonical masks side a rectangle).calibration.data ξ) :=
  CalibrationConstruction.primeSupport seed input support side a rectangle
    (CalibrationAtoms.moving seed pattern) (CalibrationAtoms.correction seed)
    (Or.inr (CalibrationAtoms.correction_mem seed)) (fun _ => ν)
    (CalibrationAtoms.remaining seed) ξ

def family : (seed.refinement input support).Calibrations where
  side := original seed input support hpacket canonical masks

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalCalibration

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalCalibration.original
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalCalibration.dictionary
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalCalibration.allowed_exact
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalCalibration.family
