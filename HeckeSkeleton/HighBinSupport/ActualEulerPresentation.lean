import HeckeSkeleton.HighBinSupport.ActualTargetEuler
import HeckeSkeleton.HighBinSupport.ActualEulerInput
import HeckeSkeleton.HighBinSupport.ActualExceptionalControl

/-!
Compatibility consumers of the original high-bin presentation. Its Euler
provider is now the canonical arithmetic data by definition, so the
provider-equality arguments retained in these APIs are witnessed by `rfl`.
The original Euler calibration, joint analyticity and all exceptional
estimates are supplied by the proved constructors. The remaining named
presentation choices and identities are still an upstream construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton.Physical

variable (K : Type) [Field K] [NumberField K]

theorem highInitialEulerControl_of_arithmetic
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c)) :
    TRowEulerInput K _ (targetData K c).probe (targetCharacter K c) P.euler := by
  rw [hEuler]
  exact HighBinActualInitial.targetTRowEulerInput K c

theorem fullHighEulerControl_of_arithmetic
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c)) :
    FullHighEulerControl K c P :=
  fullHighEulerControl_of_initial_exceptional K c P
    (highInitialEulerControl_of_arithmetic K c P hEuler)
    (highExceptionalEulerControl_of_arithmetic K c P hEuler)

#print axioms highInitialEulerControl_of_arithmetic
#print axioms fullHighEulerControl_of_arithmetic

end HeckeSkeleton
