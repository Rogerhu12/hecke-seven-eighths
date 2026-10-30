import HeckeGeneral.Analysis.PrincipalSpectrumStrip
import HeckeGeneral.Analysis.GaussianStripShift

/-! Rapid decay of the actual principal line probe at zero, obtained by
moving its Gaussian contour to any line c>=2. No physical growth bound,
Mellin inversion hypothesis, or independent tail hypothesis is assumed. -/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped BigOperators Classical Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem principalLineProbe_eq_shiftedLine
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2)
    {c Z : ℝ} (hc : 2 ≤ c) (hZ : 0 < Z) (hZ1 : Z ≤ 1) :
    principalLineProbe K S P ψ Z =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
        twistedPrincipalSpectrum K S P ψ Z ((c : ℂ) + (t : ℂ) * Complex.I) := by
  have he := verticalIntegral_eq_of_gaussian_strip hc
    (f := twistedPrincipalSpectrum K S P ψ Z)
    (fun z hz _ => differentiableAt_twistedPrincipalSpectrum_of_two_le K S P ψ hH hZ hz)
    (fun σ hσ t => norm_twistedPrincipalSpectrum_strip_le K S P ψ hHbound hZ hZ1 hσ t)
  norm_num only [Complex.ofReal_ofNat] at he
  rw [principalLineProbe_eq_positiveLineInverse]
  simp only [positiveLineInverse, Complex.ofReal_ofNat, Complex.ofReal_div]
  change (2 * (Real.pi : ℂ))⁻¹ *
    (∫ t : ℝ, twistedPrincipalSpectrum K S P ψ Z ((2 : ℂ) + (t : ℂ) * Complex.I)) = _
  rw [he]

def principalProbeShiftConstant (c : ℝ) : ℝ :=
  ‖(2 * (Real.pi : ℂ))⁻¹‖ * principalSpectrumStripConstant K c *
    ∫ t : ℝ, Real.exp (-(t ^ 2))

theorem principalProbeShiftConstant_nonneg (c : ℝ) :
    0 ≤ principalProbeShiftConstant K c := by
  have hg : 0 ≤ ∫ t : ℝ, Real.exp (-(t ^ 2)) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (principalSpectrumStripConstant_nonneg K c)) hg

theorem norm_principalLineProbe_le_shift_power
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2)
    {c Z : ℝ} (hc : 2 ≤ c) (hZ : 0 < Z) (hZ1 : Z ≤ 1) :
    ‖principalLineProbe K S P ψ Z‖ ≤ principalProbeShiftConstant K c * Z ^ (c - 11 / 16) := by
  rw [principalLineProbe_eq_shiftedLine K S P ψ hH hHbound hc hZ hZ1, norm_mul]
  have hg : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hi := norm_integral_le_of_norm_le
    (hg.const_mul (Z ^ (c - 11 / 16) * principalSpectrumStripConstant K c))
    (ae_of_all _ (norm_twistedPrincipalSpectrum_vertical_le K S P ψ hHbound ⟨hc, le_rfl⟩ hZ))
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        (∫ t : ℝ, (Z ^ (c - 11 / 16) * principalSpectrumStripConstant K c) *
          Real.exp (-(t ^ 2))) := mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; unfold principalProbeShiftConstant; ring

/-- The rapid-origin component of PhysicalProbeBound is proved directly
from the actual Euler correction and the actual excluded reciprocal. -/
theorem principalLineProbe_isBigO_rpow_near_zero
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2)
    (N : ℝ) :
    principalLineProbe K S P ψ =O[𝓝[>] (0 : ℝ)] (fun Z : ℝ => Z ^ N) := by
  let c : ℝ := max 2 (N + 11 / 16)
  have hc : 2 ≤ c := le_max_left _ _
  have hcN : N ≤ c - 11 / 16 := by
    have h := le_max_right (2 : ℝ) (N + 11 / 16)
    dsimp [c]
    linarith
  apply Asymptotics.IsBigO.of_bound (principalProbeShiftConstant K c)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with Z hZ
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hZ.1.le N)]
  exact (norm_principalLineProbe_le_shift_power K S P ψ hH hHbound hc hZ.1 hZ.2.le).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hZ.1 hZ.2.le hcN)
      (principalProbeShiftConstant_nonneg K c))

end HeckeGeneral.ThetaSkeleton.Physical
