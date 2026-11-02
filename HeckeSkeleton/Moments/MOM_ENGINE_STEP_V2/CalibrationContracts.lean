import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalCalibrationData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N3: calibration of the original canonical residual source

The data, raw parameters, moving factors, remaining mask, sectors and
original occurrences are fixed by the same original packet and seed.
The global dictionary uses every real profile argument, with one fixed
shape and scalar allowance. `OriginalCalibration` itself fixes all
three costs to the actual finite source maxima. Paper: lines 2908--2946.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

/-- Every exact field is tied to the original canonical source. In
particular an arbitrary calibrated child or a larger allowed predicate
cannot be substituted while satisfying this contract. -/
structure OriginalCalibrationSpec (seed : OrdinarySeed packet) (input : ProfileInput call)
    (support : seed.ordinary.PassiveSupport input) (side : Bool)
    (a : support.labels side) (rectangle : Bool)
    (D : OriginalCalibration call (seed.canonicalSource input support side a rectangle)) : Prop where
  inverse_background : ∀ ξ,
    (D.calibration.data ξ).inverseBackground = call.node.data.inverseBackground
  direction : ∀ ξ,
    (D.calibration.data ξ).direction = call.node.data.direction
  row_character : ∀ ξ u,
    (D.calibration.data ξ).rowCharacter u =
      CalibrationAtoms.correction seed *
        (CalibrationAtoms.moving seed (CalibrationClass.pattern packet)).character *
        completeIdealRowCharacter K
          ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
          (probeData K c) (momentRowCharacters K c)
          (CalibrationClass.sector packet) u
  inverse_profile : ∀ ξ u t x,
    (D.calibration.data ξ).inverseTest.profile u t x =
      (seed.inverseProfile input).formula.value ξ x
  left_profile : ∀ ξ u t x,
    (D.calibration.data ξ).plainTest₁.profile u t x =
      (seed.plainProfile input side rectangle false).formula.value ξ x
  right_profile : ∀ ξ u t x,
    (D.calibration.data ξ).plainTest₂.profile u t x =
      (seed.plainProfile input side rectangle true).formula.value ξ x
  prime_profile : ∀ ξ (i : Fin (D.calibration.data ξ).geometry.slotCount) t x,
    ((D.calibration.data ξ).geometry.slots i).profile t x =
      (seed.primeProfile input side
        (SlotRestriction.index
          (seed.canonicalSource input support side a rectangle).allocation.keep
          (Fin.cast (D.calibration.count ξ) i))).formula.value ξ x
  slot_coefficient : ∀ ξ (i : Fin (D.calibration.data ξ).geometry.slotCount),
    (D.calibration.data ξ).slotCoefficient i =
      call.node.data.slotCoefficient
        (seed.slotIndex side
          (SlotRestriction.index
            (seed.canonicalSource input support side a rectangle).allocation.keep
            (Fin.cast (D.calibration.count ξ) i)))
  parameters : D.calibration.parameters =
    CalibrationParameters.parameters seed input support side a rectangle
  height : ∀ ξ, D.calibration.height ξ = 0
  moving : D.recipe.moving = CalibrationAtoms.moving seed (CalibrationClass.pattern packet)
  correction : D.recipe.correction = CalibrationAtoms.correction seed
  remaining : D.recipe.remaining = CalibrationAtoms.remaining seed
  sector : D.recipe.sector = fun _ => CalibrationClass.sector packet
  original_slots : ∀ i, D.originalSlots.index i = seed.slotIndex side i
  norm_left : D.normProfiles.left =
    fun ξ _ => (seed.plainProfile input side rectangle false).formula.value ξ
  norm_right : D.normProfiles.right =
    fun ξ _ => (seed.plainProfile input side rectangle true).formula.value ξ
  allowed_exact : ∀ ξ u, (D.calibration.data ξ).allowedRow u ↔
    ∃ h ∈ (seed.canonicalSource input support side a rectangle).rows,
      ((seed.canonicalSource input support side a rectangle).row h).momentIdeal = u
  dictionary : Nonempty (D.RawDictionary input CalibrationConstruction.shape 1 call.window)
  timeIndependent : ∀ ξ, ProfileTimeIndependent (D.calibration.data ξ)
  primeSupport : ∀ ξ, PrimeProfileSupport (D.calibration.data ξ)

def OriginalCalibrationTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (call : Call c) (input : ProfileInput call) (packet : RawLeafPacket call p),
    packet.Realizes → ∀ (seed : OrdinarySeed packet)
      (support : seed.ordinary.PassiveSupport input),
      seed.CanonicalSupport input support → seed.ResidualMaskIdentity →
      ∃ C : (seed.refinement input support).Calibrations,
        ∀ side a rectangle,
          OriginalCalibrationSpec seed input support side a rectangle (C.side side a rectangle)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
