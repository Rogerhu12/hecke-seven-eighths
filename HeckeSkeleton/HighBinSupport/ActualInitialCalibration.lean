import HeckeSkeleton.HighBinSupport.ActualLocalBlockSummation
import HeckeSkeleton.HighBinSupport.ActualDeletedEulerProduct
import HeckeSkeleton.HighBinSupport.ActualGaussCalibration
import HeckeSkeleton.HighBinSupport.ActualGaussSigns
import HeckeSkeleton.HighBinSupport.LocalSeriesFactorization

/-!
# Calibration of the original four-ideal series

Every local quantity is evaluated from the original prime-power Fourier
sums, the original unit sector, and the existing mixed-Gauss arithmetic
calibration. The target's exterior unramifiedness is retained explicitly:
it is needed when multiplying its prime coefficients with a possibly
ramified row character. The named target supplies that property from the
repository's existing provider.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinActualInitial

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinContinuation
open HighBin.FiniteLocalTable HighBin.ValuationSeries
open scoped Classical BigOperators Topology ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance initialPrimeField (p : ExteriorPrime K S) :
    Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _

local instance initialPrimeFintype (p : ExteriorPrime K S) :
    Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _

theorem actual_ratio_eq_rowCoordR (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) (s z : ℂ) :
    ratio (p.val.asIdeal.absNorm : ℂ) (primeCoefficient K (thetaPeriod K S P ψ) p.val)
        ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)) =
      coordR (rowPhaseData K S P ψ u p) (p.val.asIdeal.absNorm : ℝ) s z := by
  have h := HighBin.ActualGaussPhases.raw_ratio_eq_contractive
    (thetaPrimeCharacter K S P.arithmetic p) (thetaPrimeCharacter_order K S P.arithmetic p)
    (primeAddCharacter K S P.arithmetic p) (primeAddCharacter_isPrimitive K S P.arithmetic p)
    (primeCoefficient K (thetaPeriod K S P ψ) p.val)
    (norm_primeCoefficient_le_one K _ p.val) (rowPrimeUnit K S P u p) s z
  simpa only [card_primeIdealResidueField, rowPhaseData, coordV,
    Complex.ofReal_natCast] using h

theorem actual_ratio_norm_lt_one (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) {s z : ℂ}
    (hs : 4 < s.re) (hz : 2 < z.re) :
    ‖ratio (p.val.asIdeal.absNorm : ℂ) (primeCoefficient K (thetaPeriod K S P ψ) p.val)
      ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z))‖ < 1 := by
  rw [actual_ratio_eq_rowCoordR K S P ψ u p s z]
  have h := coordR_swept_half (rowPhaseData K S P ψ u p)
    (p.val.asIdeal.absNorm : ℝ) 1 0 (exteriorPrime_norm_two_le K S p)
    (by norm_num) (by norm_num) s z (by norm_num; linarith) (by norm_num; linarith)
  exact lt_of_le_of_lt h (by norm_num)

theorem actual_V_norm_lt_one (p : ExteriorPrime K S) {z : ℂ} (hz : 0 < z.re) :
    ‖(p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)‖ < 1 := by
  have h := norm_localTerm_lt_one
    (q := (p.val.asIdeal.absNorm : ℝ)) (a := (1 : ℂ)) (s := 6 * z)
    (by have hq := exteriorPrime_norm_two_le K S p; linarith) (by simp)
    (by norm_num [Complex.mul_re]; linarith)
  simpa only [one_mul, neg_mul, Complex.ofReal_natCast] using h

theorem actual_E_eq_ratio (P : ProbeData K S) (ψ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s z : ℂ) :
    rowE K S P ψ p * (p.val.asIdeal.absNorm : ℂ) ^ (4 - 6 * s) *
        (p.val.asIdeal.absNorm : ℂ) ^ (-6 * z) =
      ratio (p.val.asIdeal.absNorm : ℂ) (primeCoefficient K (thetaPeriod K S P ψ) p.val)
        ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)) := by
  have hq : (p.val.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p.val)))
  have he : (4 : ℂ) - 6 * s = 4 + (6 : ℕ) * (-s) := by push_cast; ring
  rw [he, Complex.cpow_add _ _ hq, Complex.cpow_natCast, Complex.cpow_nat_mul]
  unfold rowE ratio
  ring

theorem rowLocalLRatio_eq_rational (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hψ : UnramifiedAt K ψ p.val) (s w z : ℂ) :
    rowLocalLRatio K S P ψ u s w z p =
      (1 - rowD K S P ψ u p * (p.val.asIdeal.absNorm : ℂ) ^ (-s)) /
        ((1 - (p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)) *
          (1 - rowW K S P u p * (p.val.asIdeal.absNorm : ℂ) ^ (-w))) := by
  have hcoef : primeCoefficient K (ψ * conjugate (arithmeticRowCharacter K S P u)) p.val =
      rowD K S P ψ u p := by
    rw [mul_comm ψ, primeCoefficient_mul_right_unramified K
      (conjugate (arithmeticRowCharacter K S P u)) ψ p.val hψ,
      primeCoefficient_inv]
    unfold rowD rowW
    ring
  simp only [rowLocalLRatio, heckeLocalEulerFactor, eulerPolynomial,
    primeCoefficient_one, hcoef, residueCard, Complex.ofReal_natCast, one_mul,
    neg_mul, rowW, div_eq_mul_inv, inv_inv, mul_inv_rev]
  ring

theorem rowW_eq_zero_of_mem_row (P : ProbeData K S) (u : FrequencyRow K S)
    (p : ExteriorPrime K S) (hp : p ∈ exteriorSupport K S u.ideal) :
    rowW K S P u p = 0 :=
  HighBinVerified.RowPrimeCharacter.row_primeCoefficient_eq_zero_of_dvd K S P
    (arithmeticRowCharacterInput K S P) u p ((mem_exteriorSupport_iff K S u.ideal p).mp hp)

theorem row_exponent_eq_zero_of_not_mem (u : FrequencyRow K S)
    (p : ExteriorPrime K S) (hp : p ∉ exteriorSupport K S u.ideal) :
    primeExponents u.ideal.val p.val = 0 := by
  apply Finsupp.notMem_support_iff.mp
  intro h
  apply hp
  exact (mem_exteriorSupport_iff K S u.ideal p).mpr
    ((mem_idealPrimeSupport_iff K u.ideal.val p.val).mp h)

theorem row_exponent_eq_ramifiedIndex (u : FrequencyRow K S)
    (p : ExteriorPrime K S) (hp : p ∈ exteriorSupport K S u.ideal) :
    primeExponents u.ideal.val p.val = (rowRamifiedIndex K S u p hp).val + 1 := by
  have hpos : 0 < primeExponents u.ideal.val p.val := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp
      ((mem_idealPrimeSupport_iff K u.ideal.val p.val).mpr
        ((mem_exteriorSupport_iff K S u.ideal p).mp hp)))
  rw [rowRamifiedIndex_val]
  omega

theorem actual_finiteTable_eq_ramifiedTable (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) (s w z : ℂ)
    (hs : 4 < s.re) (hz : 2 < z.re) (j : Fin 5) :
    finiteTableCorrection (p.val.asIdeal.absNorm : ℂ)
      (primeCoefficient K (thetaPeriod K S P ψ) p.val)
      (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
        (primeAddCharacter K S P.arithmetic p))
      (thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p))
      ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ((p.val.asIdeal.absNorm : ℂ) ^ (-w))
      ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)) j =
    ramifiedTableValue (rowPhaseData K S P ψ u p) (p.val.asIdeal.absNorm : ℝ) s w z j := by
  have hV : 1 - coordV (p.val.asIdeal.absNorm : ℝ) z ≠ 0 := by
    have hn := actual_V_norm_lt_one K S p (show 0 < z.re by linarith)
    intro h
    have h' : (p.val.asIdeal.absNorm : ℂ) ^ (-6 * z) = 1 := by
      simpa only [coordV, Complex.ofReal_natCast] using (sub_eq_zero.mp h).symm
    simpa [h'] using hn
  have hR : 1 - coordR (rowPhaseData K S P ψ u p)
      (p.val.asIdeal.absNorm : ℝ) s z ≠ 0 := by
    have hn := actual_ratio_norm_lt_one K S P ψ u p hs hz
    rw [actual_ratio_eq_rowCoordR K S P ψ u p s z] at hn
    intro h
    have h' := (sub_eq_zero.mp h).symm
    simpa [h'] using hn
  have h := HighBin.ActualGaussPhases.finiteTable_eq_contractiveGaussTable
    (thetaPrimeCharacter K S P.arithmetic p) (thetaPrimeCharacter_order K S P.arithmetic p)
    (primeAddCharacter K S P.arithmetic p) (primeAddCharacter_isPrimitive K S P.arithmetic p)
    (primeCoefficient K (thetaPeriod K S P ψ) p.val)
    (norm_primeCoefficient_le_one K _ p.val) (rowPrimeUnit K S P u p) s w z j
    (by simpa only [card_primeIdealResidueField] using hV)
    (by simpa only [card_primeIdealResidueField, rowPhaseData] using hR)
  simpa only [card_primeIdealResidueField, rowPhaseData, coordV,
    Complex.ofReal_natCast] using h

end HeckeSkeleton.HighBinActualInitial
