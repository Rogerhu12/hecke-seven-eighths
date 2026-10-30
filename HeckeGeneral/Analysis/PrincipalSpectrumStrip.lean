import HeckeGeneral.Analysis.PrincipalSpectrumRegularity
import HeckeGeneral.Analysis.GaussianContour

/-! Actual principal-spectrum analyticity and uniform Gaussian bounds
on every finite strip to the right of Re=2. Only the named analyticity
and contraction hypotheses for the actual Euler correction are consumed. -/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped BigOperators Classical Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem analyticAt_principalSpectrum_of_two_le (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    {s : ℂ} (hs : 2 ≤ s.re) : AnalyticAt ℂ (principalSpectrum K S P ψ) s := by
  have hs1 : 1 < s.re := by linarith
  have hL := (heckeEulerDeletionPolynomial_analyticAt K ψ (exceptionalPrimes K S) s).mul
    (analyticAt_heckeContinuation K ψ hs1)
  have hLne : heckeDeletedContinuation K ψ (exceptionalPrimes K S) s ≠ 0 :=
    mul_ne_zero (heckeEulerDeletionPolynomial_ne_zero K ψ _ (by linarith))
      (heckeContinuation_ne_zero K ψ hs1)
  have he : AnalyticAt ℂ (fun z : ℂ => Complex.exp ((z - 5 / 6) ^ 2)) s := by fun_prop
  exact (he.mul (hH s (by dsimp [rightHalfPlane]; linarith))).div hL hLne

def principalSpectrumStripConstant (c : ℝ) : ℝ :=
  Real.exp ((c - 5 / 6) ^ 2) * (3 / 2) *
    (∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ)))

theorem principalSpectrumStripConstant_nonneg (c : ℝ) :
    0 ≤ principalSpectrumStripConstant K c := by
  have ht : 0 ≤ ∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ)) :=
    tsum_nonneg fun I => Real.rpow_nonneg (idealNorm_pos K I).le _
  unfold principalSpectrumStripConstant
  positivity

theorem norm_principalSpectrum_vertical_le (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2)
    {c σ : ℝ} (hσ : σ ∈ Icc 2 c) (t : ℝ) :
    ‖principalSpectrum K S P ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      principalSpectrumStripConstant K c * Real.exp (-(t ^ 2)) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hs : s.re = σ := by simp [s]
  have hB : 0 ≤ c - 5 / 6 := by linarith [hσ.1, hσ.2]
  have habs : |σ - 5 / 6| ≤ c - 5 / 6 := by
    rw [abs_of_nonneg (by linarith [hσ.1])]
    linarith [hσ.2]
  have hg : ‖Complex.exp ((s - 5 / 6) ^ 2)‖ ≤
      Real.exp ((c - 5 / 6) ^ 2) * Real.exp (-(t ^ 2)) := by
    simpa only [s, gaussianContourFactor, Complex.ofReal_div, Complex.ofReal_ofNat] using
      gaussianContourFactor_strip_bound (5 / 6) (c - 5 / 6) σ t hB habs
  have hcor := norm_principalCorrection_le K S P ψ hHbound (s := s)
    (by rw [hs]; linarith [hσ.1])
  have hinv := norm_heckeDeletedContinuation_inv_le_norm_series K ψ
    (exceptionalPrimes K S) (s := s) (by rw [hs]; exact hσ.1)
  change ‖principalSpectrum K S P ψ s‖ ≤ _
  rw [principalSpectrum, principalDetectorNumerator, div_eq_mul_inv, norm_mul, norm_mul]
  calc
    _ ≤ (Real.exp ((c - 5 / 6) ^ 2) * Real.exp (-(t ^ 2))) * (3 / 2) *
        (∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ))) :=
      mul_le_mul (mul_le_mul hg hcor (norm_nonneg _) (by positivity)) hinv
        (norm_nonneg _) (by positivity)
    _ = _ := by unfold principalSpectrumStripConstant; ring

def twistedPrincipalSpectrum (P : ProbeData K S) (ψ : HeckeCharacter K) (Z : ℝ)
    (s : ℂ) : ℂ := (Z : ℂ) ^ (s - 11 / 16) * principalSpectrum K S P ψ s

theorem differentiableAt_twistedPrincipalSpectrum_of_two_le
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    {Z : ℝ} (hZ : 0 < Z) {s : ℂ} (hs : 2 ≤ s.re) :
    DifferentiableAt ℂ (twistedPrincipalSpectrum K S P ψ Z) s := by
  exact ((differentiableAt_id.sub_const (11 / 16 : ℂ)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).mul
      (analyticAt_principalSpectrum_of_two_le K S P ψ hH hs).differentiableAt

theorem norm_twistedPrincipalSpectrum_vertical_le
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2)
    {c σ Z : ℝ} (hσ : σ ∈ Icc 2 c) (hZ : 0 < Z) (t : ℝ) :
    ‖twistedPrincipalSpectrum K S P ψ Z ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Z ^ (σ - 11 / 16) * principalSpectrumStripConstant K c) * Real.exp (-(t ^ 2)) := by
  rw [twistedPrincipalSpectrum, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  have hre : (((σ : ℂ) + (t : ℂ) * Complex.I) - 11 / 16).re = σ - 11 / 16 := by simp
  rw [hre]
  exact (mul_le_mul_of_nonneg_left (norm_principalSpectrum_vertical_le K S P ψ hHbound hσ t)
    (Real.rpow_nonneg hZ.le _)).trans_eq (mul_assoc _ _ _).symm

theorem norm_twistedPrincipalSpectrum_strip_le
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2)
    {c Z : ℝ} (hZ : 0 < Z) (hZ1 : Z ≤ 1) {σ : ℝ} (hσ : σ ∈ Icc 2 c) (t : ℝ) :
    ‖twistedPrincipalSpectrum K S P ψ Z ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Z ^ (2 - 11 / 16 : ℝ) * principalSpectrumStripConstant K c) * Real.exp (-(t ^ 2)) := by
  apply (norm_twistedPrincipalSpectrum_vertical_le K S P ψ hHbound hσ hZ t).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hZ hZ1 (by linarith [hσ.1]))
      (principalSpectrumStripConstant_nonneg K c)) (Real.exp_pos _).le

end HeckeGeneral.ThetaSkeleton.Physical
