import HeckeSkeleton.HighBinSupport.ActualEulerInput
import HeckeSkeleton.HighBinSupport.ActualExceptionalControl

/-!
Consumers of the original high-bin presentation with the canonical
arithmetic Euler data. The only presentation-identification premise is
an equality of data; the original Euler calibration, joint analyticity
and all exceptional estimates are supplied by the proved constructors.

The named `actualHighPresentation` remains an upstream construction.
This module does not assume or assert its missing data identification.
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
