import HeckeSkeleton.HighBinSupport.ActualInitialLocal
import HeckeSkeleton.HighBinSupport.LocalBlockSummation

/-!
# Summing the original four-exponent prime blocks

The original absolute-convergence theorem supplies all Fubini hypotheses.
The squarefree and denominator zero branches reduce the positive completed
index to the exact `ValuationSeries.markedSeries`. The completed-unit row
is summed separately, including its extra denominator series at j = 0.
An actual mark deletes exactly this unit row.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinActualInitial

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open HighBin.FiniteLocalTable HighBin.ValuationSeries
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance summationPrimeField (p : ExteriorPrime K S) :
    Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _

local instance summationPrimeFintype (p : ExteriorPrime K S) :
    Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _

/-- The original prime block, with all summability hypotheses discharged
from the actual initial-domain norm majorant. -/
theorem primeBlockTerm_tsum_eq_markedSeries (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) (p : ExteriorPrime K S) :
    (∑' n : FourExponent, primeBlockTerm K S P ψ Q u s w z p n) =
      (if p ∈ Q then 0 else completedUnitSeries
        (thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p))
        ((p.val.asIdeal.absNorm : ℂ) ^ (-w))
        ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z))
        (primeExponents u.ideal.val p.val)) +
      markedSeries p.val.asIdeal.absNorm (primeCoefficient K (thetaPeriod K S P ψ) p.val)
        (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
          (primeAddCharacter K S P.arithmetic p))
        (thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p))
        ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ((p.val.asIdeal.absNorm : ℂ) ^ (-w))
        ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z))
        (primeExponents u.ideal.val p.val) := by
  have hbase : Summable (primeBlockBase K S P ψ u s w z p) := by
    apply (primeBlockTerm_absolute K S P ψ ∅ u s w z hs hw hz p).of_norm.congr
    intro n
    simp only [primeBlockTerm, Finset.notMem_empty, false_and, if_false]
  have hlocal := hbase.congr (primeBlockBase_eq_localBlockValue K S P hP ψ u s w z p)
  have hq : (1 : ℝ) < p.val.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.val
  have hnorm (a : ℂ) : ‖(p.val.asIdeal.absNorm : ℂ) ^ a‖ =
      (p.val.asIdeal.absNorm : ℝ) ^ a.re := by
    simpa only [Complex.ofReal_natCast] using
      Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < p.val.asIdeal.absNorm by linarith) a
  have hV : ‖(p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)‖ < 1 := by
    rw [hnorm]
    apply Real.rpow_lt_one_of_one_lt_of_neg hq
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.re_ofNat, Complex.im_ofNat,
      neg_zero, zero_mul, sub_zero]
    linarith
  have hρ : ‖thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p)‖ = 1 :=
    HighBin.ActualGaussPhases.unitPhase_norm _ _
  have hY : ‖thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p) *
      (p.val.asIdeal.absNorm : ℂ) ^ (-w)‖ < 1 := by
    rw [norm_mul, hρ, one_mul, hnorm, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  calc
    _ = ∑' n : FourExponent, if p ∈ Q ∧ n.1.1 + 3 * n.1.2 = 0 then 0 else
        localBlockValue p.val.asIdeal.absNorm (primeCoefficient K (thetaPeriod K S P ψ) p.val)
          (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
            (primeAddCharacter K S P.arithmetic p))
          (thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p))
          ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ((p.val.asIdeal.absNorm : ℂ) ^ (-w))
          ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z))
          (primeExponents u.ideal.val p.val) n :=
      tsum_congr (primeBlockTerm_eq_localBlockValue K S P hP ψ Q u s w z p)
    _ = _ := localMarkedBlock_tsum _ _ _ _ _ _ _ _ (p ∈ Q) hlocal hV hY

#print axioms primeBlockTerm_tsum_eq_markedSeries

end HeckeSkeleton.HighBinActualInitial
