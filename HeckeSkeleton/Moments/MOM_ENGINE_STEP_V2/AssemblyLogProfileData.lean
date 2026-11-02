import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyMomentDataExt
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyProfilePhase
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalChildFourierControl

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Whole moment data from the original global profile identities

This module isolates the structural transport needed by the Fourier
bridge. Its hypotheses describe the same data at zero frequency, the
global original profile formulas, and the literal retained-slot count
transport. They contain no analytic bound or task proposition.

The original-log-profile record is constructed from these identities.
Exact supports and row enumerations follow from the base data laws;
neither is selected again when the Fourier parameter changes.
-/

open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open Blueprint EngineStep NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- A derived view of global original-field identities. The formulas
are fixed before the Fourier parameter; prime formulas use the original
zero-frequency slot carrier. This record is not an additional task. -/
structure LogProfileData
    (data : EngineParameter → MomentData K ω ψ)
    (left right : ProfileFormula)
    (slot : Fin (data 0).geometry.slotCount → ProfileFormula) : Prop where
  count : ∀ ξ, (data ξ).geometry.slotCount = (data 0).geometry.slotCount
  theta : ∀ ξ, (data ξ).theta = (data 0).theta
  inverseBackground : ∀ ξ, (data ξ).inverseBackground = (data 0).inverseBackground
  direction : ∀ ξ, (data ξ).direction = (data 0).direction
  plainBackground : ∀ ξ, (data ξ).plainBackground = (data 0).plainBackground
  rowCharacter : ∀ ξ, (data ξ).rowCharacter = (data 0).rowCharacter
  allowed : ∀ ξ, (data ξ).allowedRow = (data 0).allowedRow
  mask : ∀ ξ, (data ξ).commonMask = (data 0).commonMask
  inverse : ∀ ξ, (data ξ).inverseTest = (data 0).inverseTest
  left_profile : ∀ ξ u t x, (data ξ).plainTest₁.profile u t x = left.value ξ x
  right_profile : ∀ ξ u t x, (data ξ).plainTest₂.profile u t x = right.value ξ x
  prime_profile : ∀ ξ (i : Fin (data ξ).geometry.slotCount) t x,
    ((data ξ).geometry.slots i).profile t x =
      (slot (Fin.cast (count ξ) i)).value ξ x
  lengths : ∀ ξ (i : Fin (data ξ).geometry.slotCount),
    ((data ξ).geometry.slots i).length =
      ((data 0).geometry.slots (Fin.cast (count ξ) i)).length
  slotCoefficient : ∀ ξ (i : Fin (data ξ).geometry.slotCount),
    (data ξ).slotCoefficient i =
      (data 0).slotCoefficient (Fin.cast (count ξ) i)

namespace LogProfileData

variable {data : EngineParameter → MomentData K ω ψ}
variable {left right : ProfileFormula}
variable {slot : Fin (data 0).geometry.slotCount → ProfileFormula}
variable (H : LogProfileData data left right slot)

include H

/-- The zero-frequency count proof does not change any slot index. -/
theorem cast_zero (i : Fin (data 0).geometry.slotCount) :
    Fin.cast (H.count 0) i = i := by
  apply Fin.ext
  rfl

theorem prime_profile_zero (i : Fin (data 0).geometry.slotCount) (t x : ℝ) :
    ((data 0).geometry.slots i).profile t x = (slot i).value 0 x := by
  simpa only [H.cast_zero i] using H.prime_profile 0 i t x

/-- The zero-frequency data retain every fixed arithmetic and profile
factor. Only the pure logarithmic Fourier multipliers become atoms. -/
noncomputable def profiles :
    CanonicalLogProfiles.OriginalLogProfiles K ω ψ EngineParameter where
  original := data 0
  left := ProfilePhase.atom left
  right := ProfilePhase.atom right
  slot i := ProfilePhase.atom (slot i)
  left_positive := ProfilePhase.positivePlainProfile_of_formula left 0
    (data 0).plainTest₁ (H.left_profile 0)
  right_positive := ProfilePhase.positivePlainProfile_of_formula right 0
    (data 0).plainTest₂ (H.right_profile 0)
  slot_positive i := ProfilePhase.positivePrimeProfile_of_formula (slot i) 0
    ((data 0).geometry.slots i) (H.prime_profile_zero i)

/-- The whole moment record agrees with its original logarithmic
realization, using only the supplied global identities. -/
theorem data_eq_moving (ξ : EngineParameter) : data ξ = H.profiles.moving ξ := by
  refine momentData_ext_fields
    (H.theta ξ) (H.inverseBackground ξ) (H.direction ξ)
    (H.plainBackground ξ) (H.rowCharacter ξ) (H.allowed ξ)
    (H.mask ξ) (H.inverse ξ) ?_ ?_ ?_ ?_
  · apply idealTest_ext_profile
    funext u t x
    change (data ξ).plainTest₁.profile u t x =
      (data 0).plainTest₁.profile u t x * (ProfilePhase.atom left).multiplier ξ x
    rw [H.left_profile ξ u t x, H.left_profile 0 u t x]
    exact ProfilePhase.value_eq_zero_mul_multiplier left ξ x
  · apply idealTest_ext_profile
    funext u t x
    change (data ξ).plainTest₂.profile u t x =
      (data 0).plainTest₂.profile u t x * (ProfilePhase.atom right).multiplier ξ x
    rw [H.right_profile ξ u t x, H.right_profile 0 u t x]
    exact ProfilePhase.value_eq_zero_mul_multiplier right ξ x
  · apply slotGeometry_ext_cast
      (left := (data ξ).geometry) (right := (H.profiles.moving ξ).geometry)
      (H.count ξ)
    intro i
    apply primeWindow_ext_profile
      (left := (data ξ).geometry.slots i)
      (right := (H.profiles.moving ξ).geometry.slots (Fin.cast (H.count ξ) i))
      (H.lengths ξ i)
    funext t x
    change ((data ξ).geometry.slots i).profile t x =
      ((data 0).geometry.slots (Fin.cast (H.count ξ) i)).profile t x *
        (ProfilePhase.atom (slot (Fin.cast (H.count ξ) i))).multiplier ξ x
    rw [H.prime_profile ξ i t x, H.prime_profile_zero (Fin.cast (H.count ξ) i) t x]
    exact ProfilePhase.value_eq_zero_mul_multiplier (slot (Fin.cast (H.count ξ) i)) ξ x
  · exact fin_fun_heq_of_cast (H.count ξ)
      (data ξ).slotCoefficient (data 0).slotCoefficient (H.slotCoefficient ξ)

end LogProfileData
end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.LogProfileData.cast_zero
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.LogProfileData.prime_profile_zero
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.LogProfileData.profiles
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.LogProfileData.data_eq_moving
