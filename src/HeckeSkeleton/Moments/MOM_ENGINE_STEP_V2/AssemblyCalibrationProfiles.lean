module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalRefinement
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyLogProfileData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Global original formulas for the same calibrated source

The retained indices below come from the actual source allocation and
the calibration's existing count proof. Their transport to frequency
zero does not change an occurrence. A derived view of the original
global field identities then constructs the whole logarithmic profile
realization, without importing a calibration task or its implementation.

The fixed theta, plain background, common mask and slot lengths are
already supplied by the original calibration. No second calibration,
support, allocation or capacity is selected here.
-/

open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly.CalibrationProfiles

open Blueprint EngineStep
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
variable {seed : OrdinarySeed packet} {input : ProfileInput call}
variable {support : seed.ordinary.PassiveSupport input}
variable {side : Bool} {a : support.labels side} {rectangle : Bool}
variable (D : OriginalCalibration call
  (seed.canonicalSource input support side a rectangle))

theorem count_eq_zero (ξ : EngineParameter) :
    (D.calibration.data ξ).geometry.slotCount =
      (D.calibration.data 0).geometry.slotCount :=
  (D.calibration.count ξ).trans (D.calibration.count 0).symm

/-- The actual retained occurrence, before any frequency-zero
transport. The source's original keep is used literally. -/
noncomputable def retainedIndex (ξ : EngineParameter)
    (i : Fin (D.calibration.data ξ).geometry.slotCount) :
    Fin (seed.ordinary.residualSlotCount side) :=
  SlotRestriction.index
    (seed.canonicalSource input support side a rectangle).allocation.keep
    (Fin.cast (D.calibration.count ξ) i)

/-- Both frequency carriers map to the same original retained slot. -/
theorem retainedIndex_cast_to_zero (ξ : EngineParameter)
    (i : Fin (D.calibration.data ξ).geometry.slotCount) :
    retainedIndex D 0 (Fin.cast (count_eq_zero D ξ) i) = retainedIndex D ξ i := by
  exact congrArg
    (SlotRestriction.index
      (seed.canonicalSource input support side a rectangle).allocation.keep)
    (finCast_to_common (D.calibration.count ξ) (D.calibration.count 0) i)

theorem slot_length_eq_zero (ξ : EngineParameter)
    (i : Fin (D.calibration.data ξ).geometry.slotCount) :
    ((D.calibration.data ξ).geometry.slots i).length =
      ((D.calibration.data 0).geometry.slots
        (Fin.cast (count_eq_zero D ξ) i)).length := by
  have hcast :
      Fin.cast (D.calibration.count 0) (Fin.cast (count_eq_zero D ξ) i) =
        Fin.cast (D.calibration.count ξ) i :=
    finCast_to_common (D.calibration.count ξ) (D.calibration.count 0) i
  rw [D.calibration.lengths ξ i,
    D.calibration.lengths 0 (Fin.cast (count_eq_zero D ξ) i), hcast]

/-- Each zero-frequency slot names the same original parent formula. -/
noncomputable def primeFormula
    (i : Fin (D.calibration.data 0).geometry.slotCount) : ProfileFormula :=
  (seed.primeProfile input side (retainedIndex D 0 i)).formula

/-- A view derived from global original-field identities. Its fields
are not task assumptions: the eventual original-calibration contract
supplies them for the same selected calibration. -/
structure OriginalFields : Prop where
  inverseBackground : ∀ ξ,
    (D.calibration.data ξ).inverseBackground = call.node.data.inverseBackground
  direction : ∀ ξ, (D.calibration.data ξ).direction = call.node.data.direction
  rowCharacter : ∀ ξ u,
    (D.calibration.data ξ).rowCharacter u =
      D.recipe.correction * D.recipe.moving.character *
        completeIdealRowCharacter K
          ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
          (probeData K c) (momentRowCharacters K c) (D.recipe.sector u) u
  allowed : ∀ ξ, (D.calibration.data ξ).allowedRow = (D.calibration.data 0).allowedRow
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
      (seed.primeProfile input side (retainedIndex D ξ i)).formula.value ξ x
  slotCoefficient : ∀ ξ (i : Fin (D.calibration.data ξ).geometry.slotCount),
    (D.calibration.data ξ).slotCoefficient i =
      call.node.data.slotCoefficient (seed.slotIndex side (retainedIndex D ξ i))

namespace OriginalFields

variable {D : OriginalCalibration call
  (seed.canonicalSource input support side a rectangle)}
variable (V : OriginalFields D)

include V

/-- All fields not supplied by the global original formulas follow
from the existing calibration or its fixed complete moving recipe. -/
theorem logProfileData :
    LogProfileData D.calibration.data
      (seed.plainProfile input side rectangle false).formula
      (seed.plainProfile input side rectangle true).formula
      (primeFormula D) where
  count := count_eq_zero D
  theta ξ := (D.theta_eq ξ).trans (D.theta_eq 0).symm
  inverseBackground ξ := (V.inverseBackground ξ).trans (V.inverseBackground 0).symm
  direction ξ := (V.direction ξ).trans (V.direction 0).symm
  plainBackground ξ := (D.plain_background ξ).trans (D.plain_background 0).symm
  rowCharacter ξ := by
    funext u
    exact (V.rowCharacter ξ u).trans (V.rowCharacter 0 u).symm
  allowed := V.allowed
  mask ξ := by
    funext u I
    exact (D.recipe.mask ξ u I).trans (D.recipe.mask 0 u I).symm
  inverse ξ := by
    apply idealTest_ext_profile
    funext u t x
    rw [V.inverse_profile ξ u t x, V.inverse_profile 0 u t x]
    exact ProfilePhase.value_eq_zero_of_zero_phase
      (seed.inverseProfile input).formula rfl rfl ξ x
  left_profile := V.left_profile
  right_profile := V.right_profile
  prime_profile ξ i t x := by
    change ((D.calibration.data ξ).geometry.slots i).profile t x =
      (seed.primeProfile input side
        (retainedIndex D 0 (Fin.cast (count_eq_zero D ξ) i))).formula.value ξ x
    rw [retainedIndex_cast_to_zero D ξ i]
    exact V.prime_profile ξ i t x
  lengths := slot_length_eq_zero D
  slotCoefficient ξ i := by
    rw [V.slotCoefficient ξ i,
      V.slotCoefficient 0 (Fin.cast (count_eq_zero D ξ) i),
      retainedIndex_cast_to_zero D ξ i]

/-- The original record is the same calibration at frequency zero. -/
noncomputable def profiles :
    CanonicalLogProfiles.OriginalLogProfiles K c.family.omega
      (targetCharacter K c) EngineParameter :=
  V.logProfileData.profiles

theorem data_eq_moving (ξ : EngineParameter) :
    D.calibration.data ξ = V.profiles.moving ξ :=
  V.logProfileData.data_eq_moving ξ

end OriginalFields
end HeckeSkeleton.Moments.EngineStepV2.Assembly.CalibrationProfiles

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.CalibrationProfiles.count_eq_zero
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.CalibrationProfiles.retainedIndex
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.CalibrationProfiles.retainedIndex_cast_to_zero
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.CalibrationProfiles.slot_length_eq_zero
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.CalibrationProfiles.primeFormula
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.CalibrationProfiles.OriginalFields.logProfileData
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.CalibrationProfiles.OriginalFields.profiles
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.CalibrationProfiles.OriginalFields.data_eq_moving
