import HeckeSkeleton.HighBinSupport.ActualEulerData
import HeckeSkeleton.Theta
import HeckeGeneral.Characters.UnramifiedPrimeCoefficientAlgebra
import HeckeGeneral.Analysis.HeckeConjugation

/-!
# The actual mixed-Gauss calibration of the Euler coefficient

The finite table's coefficient is `-theta(p) * gamma_1(p) * gamma_2(p)`.
It is the target coefficient by the repository's existing arithmetic
calibration, including when the target is ramified and its coefficient is
zero. The final theorem specializes this identity to `targetData`, using
`HeckeSkeleton.arithmeticCalibration` from the existing arithmetic choice.
No Euler-series identity is assumed here.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinActualEuler

open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance calibrationPrimeResidueField (p : ExteriorPrime K S) :
    Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _

local instance calibrationPrimeResidueFintype (p : ExteriorPrime K S) :
    Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _

/-- The mixed calibration at the actual prime, with its Mobius sign and
the original ideal coefficients specialized to prime coefficients. -/
theorem prime_mixed_calibration (P : ProbeData K S)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (p : ExteriorPrime K S) :
    conj (primeCoefficient K P.Lambda p.val) *
      thetaGamma K S P.arithmetic (exteriorPrimeIdeal K S p) 2 *
      thetaGamma K S P.arithmetic (exteriorPrimeIdeal K S p) 1 =
        -primeCoefficient K P.G p.val := by
  have h := hcal.mixed_calibration (exteriorPrimeIdeal K S p) p.val.irreducible.squarefree
  change conj (idealCoefficient (primeCoefficient K P.Lambda) p.val.asIdeal) *
      thetaGamma K S P.arithmetic (exteriorPrimeIdeal K S p) 2 *
      thetaGamma K S P.arithmetic (exteriorPrimeIdeal K S p) 1 =
    (UniqueFactorizationMonoid.moebius p.val.asIdeal : ℂ) *
      idealCoefficient (primeCoefficient K P.G) p.val.asIdeal at h
  simpa only [idealCoefficient_prime, p.val.irreducible.moebius_eq,
    Int.cast_neg, Int.cast_one, neg_one_mul] using h

/-- Multiplication by the two unramified correction characters preserves
the target's possible ramified zero. -/
theorem thetaPeriod_primeCoefficient (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (p : ExteriorPrime K S) :
    primeCoefficient K (thetaPeriod K S P ψ) p.val =
      conj (primeCoefficient K P.Lambda p.val) * conj (primeCoefficient K P.G p.val) *
        primeCoefficient K ψ p.val := by
  have hL := (hcal.lambda_unramified p.val p.property).inv K
  have hG := (hcal.G_unramified p.val p.property).inv K
  unfold thetaPeriod
  rw [mul_comm (conjugate P.Lambda * conjugate P.G) ψ,
    primeCoefficient_mul_right_unramified K ψ (conjugate P.Lambda * conjugate P.G)
      p.val (hL.mul K hG),
    primeCoefficient_mul_right_unramified K (conjugate P.Lambda) (conjugate P.G) p.val hG,
    primeCoefficient_inv, primeCoefficient_inv]
  ring

/-- The actual raw Gauss eta is the original target Euler coefficient.
No unramifiedness assumption is made on the target character. -/
theorem rowPhaseData_eta (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) :
    (rowPhaseData K S P ψ u p).eta = primeCoefficient K ψ p.val := by
  have hmix := prime_mixed_calibration K S P hcal p
  have hG : conj (primeCoefficient K P.G p.val) * primeCoefficient K P.G p.val = 1 := by
    rw [primeCoefficient_of_unramified K P.G p.val (hcal.G_unramified p.val p.property)]
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  change primeCoefficient K (thetaPeriod K S P ψ) p.val *
    -(1 * HighBin.ActualGaussPhases.normalizedFamily
        (thetaPrimeCharacter K S P.arithmetic p) (primeAddCharacter K S P.arithmetic p) 1 *
      HighBin.ActualGaussPhases.normalizedFamily
        (thetaPrimeCharacter K S P.arithmetic p) (primeAddCharacter K S P.arithmetic p) 2) = _
  rw [normalizedFamily_eq_thetaGamma K S P.arithmetic p 1 (by norm_num),
    normalizedFamily_eq_thetaGamma K S P.arithmetic p 2 (by norm_num),
    thetaPeriod_primeCoefficient K S P ψ hcal p]
  calc
    _ = -(conj (primeCoefficient K P.G p.val) * primeCoefficient K ψ p.val) *
        (conj (primeCoefficient K P.Lambda p.val) *
          thetaGamma K S P.arithmetic (exteriorPrimeIdeal K S p) 2 *
          thetaGamma K S P.arithmetic (exteriorPrimeIdeal K S p) 1) := by ring
    _ = -(conj (primeCoefficient K P.G p.val) * primeCoefficient K ψ p.val) *
        (-primeCoefficient K P.G p.val) := by rw [hmix]
    _ = (conj (primeCoefficient K P.G p.val) * primeCoefficient K P.G p.val) *
        primeCoefficient K ψ p.val := by ring
    _ = _ := by rw [hG, one_mul]

/-- The Fourier table and the project target coefficient have exactly
the same q normalization, not merely the same norm. -/
theorem raw_eta_eq_targetCoefficient (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) :
    HighBin.FiniteLocalTable.eta (p.val.asIdeal.absNorm : ℂ)
      (primeCoefficient K (thetaPeriod K S P ψ) p.val)
      (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
        (primeAddCharacter K S P.arithmetic p)) = primeCoefficient K ψ p.val := by
  have h := HighBin.ActualGaussPhases.contractivePhaseData_eta
    (thetaPrimeCharacter K S P.arithmetic p) (thetaPrimeCharacter_order K S P.arithmetic p)
    (primeAddCharacter K S P.arithmetic p) (primeAddCharacter_isPrimitive K S P.arithmetic p)
    (primeCoefficient K (thetaPeriod K S P ψ) p.val)
    (norm_primeCoefficient_le_one K _ p.val) (rowPrimeUnit K S P u p)
  rw [card_primeIdealResidueField] at h
  exact h.symm.trans (rowPhaseData_eta K S P ψ hcal u p)

/-- The D phase in the regular finite table is exactly the project's
target times conjugate-row coefficient. The row's unit phase is derived
from its genuine arithmetic character, and eta from mixed calibration. -/
theorem regular_D_phase_identification (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : p ∉ exteriorSupport K S u.ideal) :
    HighBin.FiniteLocalTable.eta (p.val.asIdeal.absNorm : ℂ)
        (primeCoefficient K (thetaPeriod K S P ψ) p.val)
        (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
          (primeAddCharacter K S P.arithmetic p)) *
      (thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p))⁻¹ =
        primeCoefficient K ψ p.val * conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val) := by
  have hu : ‖primeCoefficient K (arithmeticRowCharacter K S P u) p.val‖ = 1 := by
    rw [← rowPrimeUnit_character_of_not_mem_row K S P u p hp]
    exact HighBin.ActualGaussPhases.unitPhase_norm _ _
  rw [raw_eta_eq_targetCoefficient K S P ψ hcal u p,
    rowPrimeUnit_character_of_not_mem_row K S P u p hp, Complex.inv_eq_conj hu]

/-- Instantiation at the named target data uses the existing arithmetic
provider, rather than adding a calibration field to the new Euler data. -/
theorem target_rowPhaseData_eta (c : HeckeSkeleton.TargetContext K)
    (u : FrequencyRow K (HeckeSkeleton.places K c))
    (p : ExteriorPrime K (HeckeSkeleton.places K c)) :
    (rowPhaseData K (HeckeSkeleton.places K c)
      (HeckeSkeleton.probeData K c) (HeckeSkeleton.targetCharacter K c) u p).eta =
        primeCoefficient K (HeckeSkeleton.targetCharacter K c) p.val :=
  rowPhaseData_eta K _ _ _ (HeckeSkeleton.arithmeticCalibration K c) u p

#print axioms prime_mixed_calibration
#print axioms rowPhaseData_eta
#print axioms raw_eta_eq_targetCoefficient
#print axioms regular_D_phase_identification
#print axioms target_rowPhaseData_eta

end HeckeSkeleton.HighBinActualEuler
