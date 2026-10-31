import HeckeSkeleton.TargetArithmeticData
import HeckeSkeleton.HighBinSupport.ActualEulerInput

/-!
# The actual target specialization of the arithmetic Euler construction

These three declarations are moved verbatim from the generic arithmetic
modules. Their names, statements and proofs are unchanged. The actual
probe, allowed generators and mixed-Gauss calibration are provided by the
same `HeckeSkeleton` target choices.

Keeping these specializations here lets the generic Fourier/Euler proofs
and the construction of their arithmetic data avoid `Base.highExpansion`
and the full theta build. Consumers that need a named target import this
module explicitly.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler

namespace HeckeSkeleton.HighBinActualEuler

variable (K : Type) [Field K] [NumberField K]

/-- Instantiation at the named target data uses the existing arithmetic
provider, rather than adding a calibration field to the new Euler data. -/
theorem target_rowPhaseData_eta (c : HeckeSkeleton.TargetContext K)
    (u : FrequencyRow K (HeckeSkeleton.places K c))
    (p : ExteriorPrime K (HeckeSkeleton.places K c)) :
    (rowPhaseData K (HeckeSkeleton.places K c)
      (HeckeSkeleton.probeData K c) (HeckeSkeleton.targetCharacter K c) u p).eta =
        primeCoefficient K (HeckeSkeleton.targetCharacter K c) p.val :=
  rowPhaseData_eta K _ _ _ (HeckeSkeleton.arithmeticCalibration K c) u p

#print axioms target_rowPhaseData_eta

end HeckeSkeleton.HighBinActualEuler

namespace HeckeSkeleton.HighBinActualInitial

variable (K : Type) [Field K] [NumberField K]

/-- The named target uses precisely the existing allowed generators,
mixed calibration and exterior-unramified target provider. -/
theorem targetRowEulerCalibrationInput (c : HeckeSkeleton.TargetContext K) :
    RowEulerCalibrationInput K (HeckeSkeleton.places K c)
      (HeckeSkeleton.probeData K c) (HeckeSkeleton.targetCharacter K c)
      (arithmeticHighEulerData K (HeckeSkeleton.places K c)
        (HeckeSkeleton.probeData K c) (HeckeSkeleton.targetCharacter K c)) :=
  arithmeticRowEulerCalibrationInput K _ _ (HeckeSkeleton.allowedGenerators K c) _
    (HeckeSkeleton.arithmeticCalibration K c)
    (fun p => HeckeSkeleton.target_unramified_outside K c p.val p.property)

/-- The concrete target specialization uses its actual probe and places,
without importing the unrelated expansion fields into the statement. -/
theorem targetTRowEulerInput (c : HeckeSkeleton.TargetContext K) :
    TRowEulerInput K (HeckeSkeleton.places K c)
      (HeckeSkeleton.probeData K c) (HeckeSkeleton.targetCharacter K c)
      (arithmeticHighEulerData K (HeckeSkeleton.places K c)
        (HeckeSkeleton.probeData K c) (HeckeSkeleton.targetCharacter K c)) :=
  arithmeticTRowEulerInput K _ _ (HeckeSkeleton.allowedGenerators K c) _
    (HeckeSkeleton.arithmeticCalibration K c)
    (fun p => HeckeSkeleton.target_unramified_outside K c p.val p.property)

#print axioms targetRowEulerCalibrationInput
#print axioms targetTRowEulerInput

end HeckeSkeleton.HighBinActualInitial
