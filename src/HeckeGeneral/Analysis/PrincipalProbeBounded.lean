import HeckeGeneral.Analysis.PowerHeightComparison
import HeckeGeneral.Analysis.PrincipalEulerFactor

/-!
# The principal closure without the contraction hypothesis

The earlier principal closure assumed `|H^S_ψ - 1| ≤ 1/2` on `Re s > 7/8`.  It
uses that contraction only for a uniform bound of `H^S_ψ` on `Re s ≥ 2` (line
regularity, local integrability and the rightward contour shifts) and for its
non-vanishing.  Here the closure is re-proved from those two properties, and
`PrincipalEulerFactor` supplies them unconditionally from the literal local
formula: `H^S_ψ` is analytic and zero-free on `Re s > 2/3` and bounded on every
closed half-plane inside it.  No enlargement of the excluded set is needed.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped BigOperators Classical Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A uniform bound for the actual principal correction on `Re s ≥ 2`. -/
def PrincipalCorrectionBound (P : ProbeData K S) (ψ : HeckeCharacter K) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ s : ℂ, 2 ≤ s.re → ‖principalCorrection K S P ψ s‖ ≤ C

/-- The contraction implies the bound with `C = 3/2`. -/
theorem principalCorrectionBound_of_contraction (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2) :
    PrincipalCorrectionBound K S P ψ (3 / 2) := by
  refine ⟨by norm_num, fun s hs => ?_⟩
  exact norm_principalCorrection_le K S P ψ hHbound (by linarith)

/-- The closed form gives a bound on `Re s ≥ 2`. -/
theorem exists_principalCorrectionBound (P : ProbeData K S) (ψ : HeckeCharacter K) :
    ∃ C : ℝ, PrincipalCorrectionBound K S P ψ C := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_principalCorrection_le K S P ψ (σ₁ := 2) (by norm_num)
  exact ⟨C, hC0, hC⟩

/-! ### The initial line `Re s = 2` -/

/-- The Gaussian bound on the initial line, with the correction bounded by `C`
(the contraction version is `norm_principalInitialSpectralLine_le`). -/
private theorem norm_principalInitialSpectralLine_le_of_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) {C : ℝ}
    (hC : PrincipalCorrectionBound K S P ψ C) (y : ℝ) :
    ‖principalInitialSpectralLine K S P ψ y‖ ≤
      (Real.exp ((7 / 6 : ℝ) ^ 2) * C *
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
  have hcor : ‖principalCorrection K S P ψ s‖ ≤ C := hC.2 s (by rw [hs])
  have hinv := norm_heckeDeletedContinuation_inv_le_norm_series K ψ
    (exceptionalPrimes K S) (s := s) (by rw [hs])
  change ‖principalSpectrum K S P ψ s‖ ≤ _
  rw [principalSpectrum, principalDetectorNumerator, div_eq_mul_inv, norm_mul, norm_mul, hg]
  calc
    _ ≤ (Real.exp ((7 / 6 : ℝ) ^ 2) * Real.exp (-((2 * Real.pi) ^ 2) * y ^ 2)) *
        C * (∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcor (by positivity)) hinv
        (norm_nonneg _) (mul_nonneg (by positivity) hC.1)
    _ = _ := by ring

theorem integrable_principalInitialSpectralLine_of_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) {C : ℝ}
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hC : PrincipalCorrectionBound K S P ψ C) :
    Integrable (principalInitialSpectralLine K S P ψ) := by
  have hg := integrable_exp_neg_mul_sq (b := (2 * Real.pi) ^ 2) (by positivity)
  apply (hg.const_mul (Real.exp ((7 / 6 : ℝ) ^ 2) * C *
    (∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ))))).mono'
    (continuous_principalInitialSpectralLine K S P ψ hH).aestronglyMeasurable
  exact ae_of_all _ (norm_principalInitialSpectralLine_le_of_bound K S P ψ hC)

theorem principalSpectralRegularity_of_physicalProbeBound_of_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) {b C : ℝ} (hb2 : b < 2)
    (hf : PhysicalProbeBound (principalLineProbe K S P ψ) b)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hC : PrincipalCorrectionBound K S P ψ C) :
    PrincipalSpectralRegularity K S P ψ := by
  have he : mellinSpectralLine (11 / 16 - 2)
      (fun s => principalSpectrum K S P ψ ((11 / 16 : ℂ) - s)) =
      principalInitialSpectralLine K S P ψ :=
    funext (reflected_mellinSpectralLine_eq (principalSpectrum K S P ψ))
  apply positiveLineRegularity_of_physicalProbeBound 2 (principalSpectrum K S P ψ) hb2
  · rwa [← principalLineProbe_eq_positiveLineInverse]
  · rw [he]
    exact integrable_principalInitialSpectralLine_of_bound K S P ψ hH hC
  · rw [he]
    exact continuous_principalInitialSpectralLine K S P ψ hH

/-- Continuity of the principal probe on `(0, ∞)`, from the integrable initial
spectrum (the contraction version is `continuousOn_principalLineProbe`). -/
private theorem continuousOn_principalLineProbe_of_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) {C : ℝ}
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hC : PrincipalCorrectionBound K S P ψ C) :
    ContinuousOn (principalLineProbe K S P ψ) (Ioi 0) := by
  rw [principalLineProbe_eq_positiveLineInverse]
  apply continuousOn_positiveLineInverse_of_integrable
  have he : mellinSpectralLine (11 / 16 - 2)
      (fun s => principalSpectrum K S P ψ ((11 / 16 : ℂ) - s)) =
      principalInitialSpectralLine K S P ψ :=
    funext (reflected_mellinSpectralLine_eq (principalSpectrum K S P ψ))
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [he]
  exact integrable_principalInitialSpectralLine_of_bound K S P ψ hH hC

theorem locallyIntegrableOn_principalLineProbe_of_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) {C : ℝ}
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hC : PrincipalCorrectionBound K S P ψ C) :
    LocallyIntegrableOn (principalLineProbe K S P ψ) (Ioi 0) := by
  exact (continuousOn_principalLineProbe_of_bound K S P ψ hH hC).locallyIntegrableOn
    measurableSet_Ioi

/-! ### Strips to the right of `Re s = 2` and the rightward contour shift -/

/-- The strip constant `e^{(c - 5/6)^2} C ∑ N(I)^{-2}` (with `C = 3/2` it is
`principalSpectrumStripConstant`). -/
private def boundedStripConstant (C c : ℝ) : ℝ :=
  Real.exp ((c - 5 / 6) ^ 2) * C *
    (∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ)))

private theorem boundedStripConstant_nonneg {C : ℝ} (hC : 0 ≤ C) (c : ℝ) :
    0 ≤ boundedStripConstant K C c := by
  have ht : 0 ≤ ∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ)) :=
    tsum_nonneg fun I => Real.rpow_nonneg (idealNorm_pos K I).le _
  unfold boundedStripConstant
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hC) ht

private theorem norm_principalSpectrum_vertical_le_of_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) {C : ℝ}
    (hC : PrincipalCorrectionBound K S P ψ C)
    {c σ : ℝ} (hσ : σ ∈ Icc 2 c) (t : ℝ) :
    ‖principalSpectrum K S P ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      boundedStripConstant K C c * Real.exp (-(t ^ 2)) := by
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
  have hcor : ‖principalCorrection K S P ψ s‖ ≤ C := hC.2 s (by rw [hs]; exact hσ.1)
  have hinv := norm_heckeDeletedContinuation_inv_le_norm_series K ψ
    (exceptionalPrimes K S) (s := s) (by rw [hs]; exact hσ.1)
  change ‖principalSpectrum K S P ψ s‖ ≤ _
  rw [principalSpectrum, principalDetectorNumerator, div_eq_mul_inv, norm_mul, norm_mul]
  calc
    _ ≤ (Real.exp ((c - 5 / 6) ^ 2) * Real.exp (-(t ^ 2))) * C *
        (∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ))) :=
      mul_le_mul (mul_le_mul hg hcor (norm_nonneg _) (by positivity)) hinv
        (norm_nonneg _) (mul_nonneg (by positivity) hC.1)
    _ = _ := by unfold boundedStripConstant; ring

private theorem norm_twistedPrincipalSpectrum_vertical_le_of_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) {C : ℝ}
    (hC : PrincipalCorrectionBound K S P ψ C)
    {c σ Z : ℝ} (hσ : σ ∈ Icc 2 c) (hZ : 0 < Z) (t : ℝ) :
    ‖twistedPrincipalSpectrum K S P ψ Z ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Z ^ (σ - 11 / 16) * boundedStripConstant K C c) * Real.exp (-(t ^ 2)) := by
  rw [twistedPrincipalSpectrum, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  have hre : (((σ : ℂ) + (t : ℂ) * Complex.I) - 11 / 16).re = σ - 11 / 16 := by simp
  rw [hre]
  exact (mul_le_mul_of_nonneg_left (norm_principalSpectrum_vertical_le_of_bound K S P ψ hC hσ t)
    (Real.rpow_nonneg hZ.le _)).trans_eq (mul_assoc _ _ _).symm

private theorem norm_twistedPrincipalSpectrum_strip_le_of_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) {C : ℝ}
    (hC : PrincipalCorrectionBound K S P ψ C)
    {c Z : ℝ} (hZ : 0 < Z) (hZ1 : Z ≤ 1) {σ : ℝ} (hσ : σ ∈ Icc 2 c) (t : ℝ) :
    ‖twistedPrincipalSpectrum K S P ψ Z ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Z ^ (2 - 11 / 16 : ℝ) * boundedStripConstant K C c) * Real.exp (-(t ^ 2)) := by
  apply (norm_twistedPrincipalSpectrum_vertical_le_of_bound K S P ψ hC hσ hZ t).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hZ hZ1 (by linarith [hσ.1]))
      (boundedStripConstant_nonneg K hC.1 c)) (Real.exp_pos _).le

/-- The rightward contour shift of the principal probe for `0 < Z ≤ 1`. -/
private theorem principalLineProbe_eq_shiftedLine_of_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) {C : ℝ}
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hC : PrincipalCorrectionBound K S P ψ C)
    {c Z : ℝ} (hc : 2 ≤ c) (hZ : 0 < Z) (hZ1 : Z ≤ 1) :
    principalLineProbe K S P ψ Z =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
        twistedPrincipalSpectrum K S P ψ Z ((c : ℂ) + (t : ℂ) * Complex.I) := by
  have he := verticalIntegral_eq_of_gaussian_strip hc
    (f := twistedPrincipalSpectrum K S P ψ Z)
    (fun z hz _ => differentiableAt_twistedPrincipalSpectrum_of_two_le K S P ψ hH hZ hz)
    (fun σ hσ t => norm_twistedPrincipalSpectrum_strip_le_of_bound K S P ψ hC hZ hZ1 hσ t)
  norm_num only [Complex.ofReal_ofNat] at he
  rw [principalLineProbe_eq_positiveLineInverse]
  simp only [positiveLineInverse, Complex.ofReal_ofNat, Complex.ofReal_div]
  change (2 * (Real.pi : ℂ))⁻¹ *
    (∫ t : ℝ, twistedPrincipalSpectrum K S P ψ Z ((2 : ℂ) + (t : ℂ) * Complex.I)) = _
  rw [he]

/-- The shift constant (with `C = 3/2` it is `principalProbeShiftConstant`). -/
private def boundedShiftConstant (C c : ℝ) : ℝ :=
  ‖(2 * (Real.pi : ℂ))⁻¹‖ * boundedStripConstant K C c *
    ∫ t : ℝ, Real.exp (-(t ^ 2))

private theorem boundedShiftConstant_nonneg {C : ℝ} (hC : 0 ≤ C) (c : ℝ) :
    0 ≤ boundedShiftConstant K C c := by
  have hg : 0 ≤ ∫ t : ℝ, Real.exp (-(t ^ 2)) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (boundedStripConstant_nonneg K hC c)) hg

private theorem norm_principalLineProbe_le_shift_power_of_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) {C : ℝ}
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hC : PrincipalCorrectionBound K S P ψ C)
    {c Z : ℝ} (hc : 2 ≤ c) (hZ : 0 < Z) (hZ1 : Z ≤ 1) :
    ‖principalLineProbe K S P ψ Z‖ ≤ boundedShiftConstant K C c * Z ^ (c - 11 / 16) := by
  rw [principalLineProbe_eq_shiftedLine_of_bound K S P ψ hH hC hc hZ hZ1, norm_mul]
  have hg : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hi := norm_integral_le_of_norm_le
    (hg.const_mul (Z ^ (c - 11 / 16) * boundedStripConstant K C c))
    (ae_of_all _ (norm_twistedPrincipalSpectrum_vertical_le_of_bound K S P ψ hC
      ⟨hc, le_rfl⟩ hZ))
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        (∫ t : ℝ, (Z ^ (c - 11 / 16) * boundedStripConstant K C c) *
          Real.exp (-(t ^ 2))) := mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; unfold boundedShiftConstant; ring

theorem principalLineProbe_isBigO_rpow_near_zero_of_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) {C : ℝ}
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hC : PrincipalCorrectionBound K S P ψ C) (N : ℝ) :
    principalLineProbe K S P ψ =O[𝓝[>] (0 : ℝ)] (fun Z : ℝ => Z ^ N) := by
  let c : ℝ := max 2 (N + 11 / 16)
  have hc : 2 ≤ c := le_max_left _ _
  have hcN : N ≤ c - 11 / 16 := by
    have h := le_max_right (2 : ℝ) (N + 11 / 16)
    dsimp [c]
    linarith
  apply Asymptotics.IsBigO.of_bound (boundedShiftConstant K C c)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with Z hZ
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hZ.1.le N)]
  exact (norm_principalLineProbe_le_shift_power_of_bound K S P ψ hH hC hc hZ.1 hZ.2.le).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hZ.1 hZ.2.le hcN)
      (boundedShiftConstant_nonneg K hC.1 c))

/-! ### The closure -/

theorem heckeContinuation_zeroFreeOn_of_principalProbe_bounded
    (P : ProbeData K S) (ψ : HeckeCharacter K) {b C : ℝ}
    (hb : 7 / 8 ≤ b) (hb2 : b < 2)
    (hf : PhysicalProbeBound (principalLineProbe K S P ψ) b)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHne : ∀ s ∈ rightHalfPlane (7 / 8), principalCorrection K S P ψ s ≠ 0)
    (hC : PrincipalCorrectionBound K S P ψ C) :
    MeromorphicZeroFreeOn (heckeContinuation K ψ) (rightHalfPlane b) := by
  exact heckeContinuation_zeroFreeOn_of_principalProbe K S P ψ hb hb2
    (principalSpectralRegularity_of_physicalProbeBound_of_bound K S P ψ hb2 hf hH hC) hf hH hHne

/-- The principal closure from a power-height comparison, with no hypothesis
on the principal correction: all of its properties follow from the closed form. -/
theorem principal_zeroFree_of_powerHeightComparison_closedForm
    (P : ProbeData K S) (ψ : HeckeCharacter K) (J : ℝ → ℂ) {B σ : ℝ}
    (hB : B ≤ 1) (hσ : 0 < σ) (hσsmall : σ < (B - 7 / 8) / 2)
    (hlow : ∀ ε : ℝ, 0 < ε → J =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + ε)))
    (hhigh : PowerHeightComparison J (principalLineProbe K S P ψ) (B - 11 / 16) σ) :
    MeromorphicZeroFreeOn (heckeContinuation K ψ) (rightHalfPlane (B - σ)) := by
  have hsub : rightHalfPlane (7 / 8) ⊆ rightHalfPlane (2 / 3) := by
    intro s hs
    have h : (7 / 8 : ℝ) < s.re := hs
    show (2 / 3 : ℝ) < s.re
    linarith
  have hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)) :=
    (analyticOnNhd_principalCorrection K S P ψ).mono hsub
  have hHne : ∀ s ∈ rightHalfPlane (7 / 8), principalCorrection K S P ψ s ≠ 0 :=
    fun s hs => principalCorrection_ne_zero K S P ψ (hsub hs)
  obtain ⟨C, hC⟩ := exists_principalCorrectionBound K S P ψ
  have hf : PhysicalProbeBound (principalLineProbe K S P ψ) (B - σ) :=
    physicalProbeBound_of_low_and_powerHeightComparison hσ hσsmall hlow hhigh
      (locallyIntegrableOn_principalLineProbe_of_bound K S P ψ hH hC)
      (principalLineProbe_isBigO_rpow_near_zero_of_bound K S P ψ hH hC)
  exact heckeContinuation_zeroFreeOn_of_principalProbe_bounded K S P ψ
    (by linarith) (by linarith) hf hH hHne hC

end HeckeGeneral.ThetaSkeleton.Physical
