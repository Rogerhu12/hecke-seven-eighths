import HeckeSkeleton.HighBinSupport.ActualInitialCalibration
import HeckeSkeleton.HighBinSupport.ActualEulerRegion

/-!
The original `TRowEulerInput` filled by the actual arithmetic provider.
Initial calibration, product convergence and joint analyticity are all
conclusions of the underlying arithmetic and analytic proofs. No Euler
identity or analytic conclusion is supplied as an input hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinActualInitial

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinContinuation
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem arithmeticTRowEulerInput (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (hψ : ∀ p : ExteriorPrime K S, UnramifiedAt K ψ p.val) :
    TRowEulerInput K S P ψ (arithmeticHighEulerData K S P ψ) where
  initial := arithmeticRowEulerCalibrationInput K S P hP ψ hcal hψ
  local_product Q u v hv := rowCorrection_multipliable_rowEulerRegion K S P ψ
    (arithmeticHighEulerData K S P ψ) Q u v hv
  correction_analytic Q u := rowCorrection_analyticOnNhd_rowEulerRegion K S P ψ Q u

#print axioms arithmeticTRowEulerInput

end HeckeSkeleton.HighBinActualInitial
