import HeckeGeneral.Analysis.PhysicalProbeMellin
import HeckeGeneral.Analysis.MellinInverseConvergence
import HeckeGeneral.Analysis.IdealMobiusDeletion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Regularity of the actual principal spectrum on its initial line Re=2.
The reciprocal bound is obtained from the proved S-excluded ideal series;
the Gaussian supplies integrability. The physical probe bound supplies the
Fourier-side integrability by MellinInverseConvergence. No independent
PrincipalSpectralRegularity hypothesis is used by the final consumers. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open scoped BigOperators Classical Topology

variable (K : Type) [Field K] [NumberField K]

theorem norm_heckeDeletedContinuation_inv_le_norm_series
    (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(heckeDeletedContinuation K χ S s)⁻¹‖ ≤
      ∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ)) := by
  have hs1 : 1 < s.re := by linarith
  have hsum := IdealMobiusReciprocal.absolutelySummable_excluded K S
    (primeCoefficient K χ) (norm_primeCoefficient_le_one K χ) hs1
  have he := IdealMobiusReciprocal.hecke_excluded_moebius_series_eq_reciprocal K χ S hs1
  simp_rw [← IdealMobiusReciprocal.hecke_excludedTerm_eq_literal] at he
  rw [← he]
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (summable_nonzeroIdeal_norm_rpow K (by norm_num : (1 : ℝ) < 2))
  intro I
  unfold IdealMobiusReciprocal.excludedTerm
  split_ifs
  · rw [IdealMobiusReciprocal.term, norm_dirichletTerm _ _ _ _ (idealNorm_pos K I)]
    calc
      _ ≤ 1 * idealNorm K I ^ (-s.re) := mul_le_mul_of_nonneg_right
        (IdealMobiusReciprocal.norm_coefficient_le_one K (primeCoefficient K χ)
          (norm_primeCoefficient_le_one K χ) I)
        (Real.rpow_nonneg (idealNorm_pos K I).le _)
      _ ≤ _ := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_le (one_le_idealNorm K I) (by linarith)
  · simp only [norm_zero]
    exact Real.rpow_nonneg (idealNorm_pos K I).le (-(2 : ℝ))

theorem reflected_mellinSpectralLine_eq (F : ℂ → ℂ) (y : ℝ) :
    mellinSpectralLine (11 / 16 - 2) (fun s => F ((11 / 16 : ℂ) - s)) y =
      F (2 - ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) := by
  unfold mellinSpectralLine
  apply congrArg F
  push_cast
  ring

end HeckeGeneral.Analysis

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped BigOperators Classical Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def principalInitialSpectralLine (P : ProbeData K S) (ψ : HeckeCharacter K) (y : ℝ) : ℂ :=
  principalSpectrum K S P ψ (2 - ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)

theorem continuous_principalInitialSpectralLine (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8))) :
    Continuous (principalInitialSpectralLine K S P ψ) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  let s : ℂ := 2 - ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I
  have hs : 1 < s.re := by dsimp [s]; norm_num
  have hL := (heckeEulerDeletionPolynomial_analyticAt K ψ (exceptionalPrimes K S) s).mul
    (analyticAt_heckeContinuation K ψ hs)
  have hLne : heckeDeletedContinuation K ψ (exceptionalPrimes K S) s ≠ 0 :=
    mul_ne_zero (heckeEulerDeletionPolynomial_ne_zero K ψ _ (by linarith))
      (heckeContinuation_ne_zero K ψ hs)
  have he : AnalyticAt ℂ (fun z : ℂ => Complex.exp ((z - 5 / 6) ^ 2)) s := by fun_prop
  have hnum := he.mul (hH s (by dsimp [rightHalfPlane]; linarith))
  have hF : AnalyticAt ℂ (principalSpectrum K S P ψ) s := hnum.div hL hLne
  have hline : Continuous (fun x : ℝ => 2 - ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) :=
    continuous_const.sub ((Complex.continuous_ofReal.comp
      (continuous_const.mul continuous_id)).mul continuous_const)
  exact hF.continuousAt.comp
    (f := fun x : ℝ => 2 - ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    (x := y) hline.continuousAt

theorem norm_principalCorrection_le (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hH : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2)
    {s : ℂ} (hs : 7 / 8 < s.re) : ‖principalCorrection K S P ψ s‖ ≤ 3 / 2 := by
  have ht := norm_add_le (principalCorrection K S P ψ s - 1) 1
  rw [sub_add_cancel] at ht
  have hb := hH s hs
  norm_num at ht
  linarith

theorem norm_principalInitialSpectralLine_le (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hH : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2)
    (y : ℝ) :
    ‖principalInitialSpectralLine K S P ψ y‖ ≤
      (Real.exp ((7 / 6 : ℝ) ^ 2) * (3 / 2) *
        (∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ)))) *
        Real.exp (-((2 * Real.pi) ^ 2) * y ^ 2) := by
  let s : ℂ := 2 - ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I
  have hs : s.re = 2 := by dsimp [s]; norm_num
  have hg : ‖Complex.exp ((s - 5 / 6) ^ 2)‖ =
      Real.exp ((7 / 6 : ℝ) ^ 2) * Real.exp (-((2 * Real.pi) ^ 2) * y ^ 2) := by
    rw [Complex.norm_exp]
    have hr : ((s - 5 / 6) ^ 2).re = (7 / 6 : ℝ) ^ 2 - (2 * Real.pi) ^ 2 * y ^ 2 := by
      dsimp [s]
      simp only [pow_two, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
      norm_num
      ring
    rw [hr, sub_eq_add_neg, Real.exp_add]
    apply congrArg (fun r : ℝ => Real.exp ((7 / 6 : ℝ) ^ 2) * Real.exp r)
    ring
  have hcor := norm_principalCorrection_le K S P ψ hH (s := s) (by rw [hs]; norm_num)
  have hinv := norm_heckeDeletedContinuation_inv_le_norm_series K ψ
    (exceptionalPrimes K S) (s := s) (by rw [hs])
  change ‖principalSpectrum K S P ψ s‖ ≤ _
  rw [principalSpectrum, principalDetectorNumerator, div_eq_mul_inv, norm_mul, norm_mul, hg]
  calc
    _ ≤ (Real.exp ((7 / 6 : ℝ) ^ 2) * Real.exp (-((2 * Real.pi) ^ 2) * y ^ 2)) *
        (3 / 2) * (∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcor (by positivity)) hinv
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem integrable_principalInitialSpectralLine (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2) :
    Integrable (principalInitialSpectralLine K S P ψ) := by
  have hg := integrable_exp_neg_mul_sq (b := (2 * Real.pi) ^ 2) (by positivity)
  apply (hg.const_mul (Real.exp ((7 / 6 : ℝ) ^ 2) * (3 / 2) *
    (∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ))))).mono'
    (continuous_principalInitialSpectralLine K S P ψ hH).aestronglyMeasurable
  exact ae_of_all _ (norm_principalInitialSpectralLine_le K S P ψ hHbound)

theorem principalSpectralRegularity_of_physicalProbeBound
    (P : ProbeData K S) (ψ : HeckeCharacter K) {b : ℝ} (hb2 : b < 2)
    (hf : PhysicalProbeBound (principalLineProbe K S P ψ) b)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2) :
    PrincipalSpectralRegularity K S P ψ := by
  have he : mellinSpectralLine (11 / 16 - 2)
      (fun s => principalSpectrum K S P ψ ((11 / 16 : ℂ) - s)) =
      principalInitialSpectralLine K S P ψ :=
    funext (reflected_mellinSpectralLine_eq (principalSpectrum K S P ψ))
  apply positiveLineRegularity_of_physicalProbeBound 2 (principalSpectrum K S P ψ) hb2
  · rwa [← principalLineProbe_eq_positiveLineInverse]
  · rw [he]
    exact integrable_principalInitialSpectralLine K S P ψ hH hHbound
  · rw [he]
    exact continuous_principalInitialSpectralLine K S P ψ hH

theorem heckeContinuation_zeroFreeOn_of_principalProbe_contraction
    (P : ProbeData K S) (ψ : HeckeCharacter K) {b : ℝ}
    (hb : 7 / 8 ≤ b) (hb2 : b < 2)
    (hf : PhysicalProbeBound (principalLineProbe K S P ψ) b)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2) :
    MeromorphicZeroFreeOn (heckeContinuation K ψ) (rightHalfPlane b) := by
  apply heckeContinuation_zeroFreeOn_of_principalProbe K S P ψ hb hb2
    (principalSpectralRegularity_of_physicalProbeBound K S P ψ hb2 hf hH hHbound) hf hH
  intro s hs hz
  have he := hHbound s hs
  rw [hz] at he
  norm_num at he

end HeckeGeneral.ThetaSkeleton.Physical
