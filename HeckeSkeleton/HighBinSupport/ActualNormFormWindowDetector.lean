import HeckeSkeleton.HighBinSupport.ActualNormFormPrimeDetector
import HeckeSkeleton.HighBinSupport.ActualNormFormRepeatedTuples
import HeckeGeneral.Analysis.MomentPrimeWindows

/-!
The annular logarithmic detector at the repository's actual prime windows.

The original target's ray filter is empty. The only difference between
the complete prime sum and its exterior window is therefore the fixed
finite set S. We identify the literal finite window sum, prove its fixed
deletion error, and absorb it together with the higher-power error into
one scale-independent constant. The remaining analytic operation is the
zero-free contour move.
-/

noncomputable section
namespace HighBinVerified.NormFormActual

open NumberField IsDedekindDomain MeasureTheory Complex Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open NormFormMellin NormFormPrimeDetector
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def annularPrimeTerm (phi : ℝ → ℂ) (chi : HeckeCharacter K) (P t : ℝ)
    (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  phi ((p.asIdeal.absNorm : ℝ) / P) * primeCoefficient K chi p *
    (p.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)

theorem summable_annularPrimeTerm (phi : ℝ → ℂ)
    (hann : Function.support phi ⊆ Ioo (1 : ℝ) 2)
    (chi : HeckeCharacter K) (P t : ℝ) :
    Summable (annularPrimeTerm K phi chi P t) := by
  apply summable_of_ne_finset_zero (s := analyticPrimeSupport K phi P)
  intro p hp
  have hz : phi ((p.asIdeal.absNorm : ℝ) / P) = 0 := by
    by_contra hne
    exact hp ((analyticPrimeSupport_spec K phi hann P p).mpr hne)
  simp only [annularPrimeTerm, hz, zero_mul]

/-- A literal finite sum over the original exterior prime window. -/
def actualWindowPrimePolynomial (g : PrimeWindowGeometry) (chi : HeckeCharacter K)
    (Z t : ℝ) (i : Fin g.slots) : ℂ :=
  ∑ p ∈ primeWindow K S g ∅ Z i, windowWeight K S g Z i p *
    primeCoefficient K chi p.val *
      (p.val.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)

theorem actualWindowPrimePolynomial_eq_exterior_tsum (g : PrimeWindowGeometry)
    (chi : HeckeCharacter K) (Z t : ℝ) (i : Fin g.slots) :
    actualWindowPrimePolynomial K S g chi Z t i =
      ∑' p : ExteriorPrime K S,
        annularPrimeTerm K (g.weight i).toFun chi (primeScale g Z) t p.val := by
  change (∑ p ∈ primeWindow K S g ∅ Z i,
    annularPrimeTerm K (g.weight i).toFun chi (primeScale g Z) t p.val) = _
  symm
  apply tsum_eq_sum
  intro p hp
  have hz : (g.weight i).toFun ((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) = 0 := by
    by_contra hne
    apply hp
    apply (mem_physicalPrimeWindow_iff_analytic K S g ∅ Z i p).mpr
    refine ⟨?_, by simp⟩
    exact (analyticPrimeSupport_spec K (g.weight i).toFun
      (g.support_annular i) (primeScale g Z) p.val).mpr hne
  simp only [annularPrimeTerm, hz, zero_mul]

def fixedPrimeDeletionMass : ℝ :=
  ∑ p : S, (p.val.asIdeal.absNorm : ℝ) ^ (-(1 / 2 : ℝ))

theorem fixedPrimeDeletionMass_nonneg : 0 ≤ fixedPrimeDeletionMass K S :=
  Finset.sum_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem norm_fixedPrimeDeletion_le (phi : ℝ → ℂ) (chi : HeckeCharacter K)
    (P t M : ℝ) (hM : 0 ≤ M) (hphi : ∀ y : ℝ, ‖phi y‖ ≤ M) :
    ‖∑' p : S, annularPrimeTerm K phi chi P t p.val‖ ≤
      M * fixedPrimeDeletionMass K S := by
  rw [tsum_fintype]
  calc
    _ ≤ ∑ p : S, ‖annularPrimeTerm K phi chi P t p.val‖ := norm_sum_le _ _
    _ ≤ ∑ p : S, M * (p.val.asIdeal.absNorm : ℝ) ^ (-(1 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hq : (0 : ℝ) < (p.val.asIdeal.absNorm : ℝ) := by
        exact_mod_cast lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p.val)
      have hcast : (((p.val.asIdeal.absNorm : ℝ) : ℂ)) = (p.val.asIdeal.absNorm : ℂ) := by simp
      rw [annularPrimeTerm, norm_mul, norm_mul, ← hcast,
        Complex.norm_cpow_eq_rpow_re_of_pos hq]
      have hre : (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I).re = -(1 / 2 : ℝ) := by simp
      rw [hre]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hq.le _)
      exact (mul_le_mul (hphi _) (norm_primeCoefficient_le_one K chi p.val)
        (norm_nonneg _) hM).trans_eq (mul_one M)
    _ = _ := (Finset.mul_sum ..).symm

/-- The initial detector is now attached to `primeWindow K S g ∅` itself.
The single constant is chosen before all characters, scales, slots,
frequencies and initial vertical lines. -/
theorem exists_actual_primeWindow_detector_error (g : PrimeWindowGeometry)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (chi : HeckeCharacter K) (Z t : ℝ) (i : Fin g.slots)
      (hP : 1 < primeScale g Z) {sigma : ℝ}, 1 < sigma →
      ‖actualWindowPrimePolynomial K S g chi Z t i +
        (2 * (Real.pi : ℂ))⁻¹ * (∫ r : ℝ,
          annularMellinKernel (divideLogTest (g.weight i) (g.support_annular i)
            (primeScale g Z) hP) (primeScale g Z) (1 / 2) sigma r *
            heckeLogDerivative K chi (idealVerticalPoint sigma r - (t : ℂ) * Complex.I))‖ ≤
          C * (primeScale g Z) ^ delta := by
  obtain ⟨M, hM, hprofile⟩ := exists_primeWindow_profile_norm_bound g
  let A := M * HigherPrimePowers.higherPowerConstant K delta * (2 : ℝ) ^ delta
  let D := M * fixedPrimeDeletionMass K S
  have hA : 0 ≤ A := le_of_lt (mul_pos
    (mul_pos hM (HigherPrimePowers.higherPowerConstant_pos K delta))
      (Real.rpow_pos_of_pos (by norm_num) _))
  have hD : 0 ≤ D := mul_nonneg hM.le (fixedPrimeDeletionMass_nonneg K S)
  refine ⟨A + D + 1, by linarith, ?_⟩
  intro chi Z t i hP sigma hsigma
  let L : ℂ := (2 * (Real.pi : ℂ))⁻¹ * (∫ r : ℝ,
    annularMellinKernel (divideLogTest (g.weight i) (g.support_annular i)
      (primeScale g Z) hP) (primeScale g Z) (1 / 2) sigma r *
      heckeLogDerivative K chi (idealVerticalPoint sigma r - (t : ℂ) * Complex.I))
  let f := annularPrimeTerm K (g.weight i).toFun chi (primeScale g Z) t
  have hsum := summable_annularPrimeTerm K (g.weight i).toFun
    (g.support_annular i) chi (primeScale g Z) t
  have hpart := hsum.tsum_subtype_add_tsum_subtype_compl S
  have heq : actualWindowPrimePolynomial K S g chi Z t i + L =
      ((∑' p, f p) + L) - ∑' p : S, f p.val := by
    rw [actualWindowPrimePolynomial_eq_exterior_tsum, ← hpart]
    change (∑' p : ExteriorPrime K S, f p.val) + L = _
    ring
  have hmain := norm_annular_phase_sum_add_logDerivative_integral_le K (g.weight i)
    (g.support_annular i) chi (primeScale g Z) delta t M hP hdelta hM.le
    (hprofile i) hsigma
  have hdelete := norm_fixedPrimeDeletion_le K S (g.weight i).toFun chi
    (primeScale g Z) t M hM.le (hprofile i)
  have hP0 : 0 < primeScale g Z := by linarith
  have hpow : 1 ≤ (primeScale g Z) ^ delta := Real.one_le_rpow hP.le hdelta.le
  change ‖actualWindowPrimePolynomial K S g chi Z t i + L‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖(∑' p, f p) + L‖ + ‖∑' p : S, f p.val‖ := norm_sub_le _ _
    _ ≤ M * HigherPrimePowers.higherPowerConstant K delta *
        (2 * primeScale g Z) ^ delta + D := add_le_add hmain hdelete
    _ = A * (primeScale g Z) ^ delta + D := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hP0.le]
      dsimp only [A]
      ring
    _ ≤ A * (primeScale g Z) ^ delta + D * (primeScale g Z) ^ delta := by
      have hDpow : D ≤ D * (primeScale g Z) ^ delta := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hD
      exact add_le_add le_rfl hDpow
    _ ≤ (A + D + 1) * (primeScale g Z) ^ delta := by
      nlinarith

end HighBinVerified.NormFormActual

#print axioms HighBinVerified.NormFormActual.actualWindowPrimePolynomial_eq_exterior_tsum
#print axioms HighBinVerified.NormFormActual.exists_actual_primeWindow_detector_error
