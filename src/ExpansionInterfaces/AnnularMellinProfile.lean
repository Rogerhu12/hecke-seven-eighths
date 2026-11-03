import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.MellinInversion
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Genuine Mellin data for a smooth annular profile

Only the physical profile, smoothness, and support away from zero are
stored.  Entire Mellin continuation, absolute vertical integrability, and
Mellin inversion are derived.  No polynomial estimate is an input.
-/

noncomputable section
namespace ExpansionInterfaces.Mellin
open MeasureTheory Set Filter Asymptotics
open scoped Classical BigOperators FourierTransform SchwartzMap Topology ContDiff

def vertical (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem vertical_re (σ t : ℝ) : (vertical σ t).re = σ := by simp [vertical]
@[simp] theorem vertical_im (σ t : ℝ) : (vertical σ t).im = t := by simp [vertical]

structure AnnularProfile where
  function : ℝ → ℂ
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
  smooth : ContDiff ℝ ∞ function
  supported : Function.support function ⊆ Icc lower upper

namespace AnnularProfile

theorem zero_below (W : AnnularProfile) {x : ℝ} (hx : x < W.lower) :
    W.function x = 0 := by
  by_contra hn
  exact (not_le_of_gt hx) (W.supported hn).1

theorem zero_above (W : AnnularProfile) {x : ℝ} (hx : W.upper < x) :
    W.function x = 0 := by
  by_contra hn
  exact (not_le_of_gt hx) (W.supported hn).2

theorem isBigO_top (W : AnnularProfile) (a : ℝ) :
    W.function =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  apply isBigO_iff.mpr
  refine ⟨1, ?_⟩
  filter_upwards [eventually_gt_atTop W.upper] with x hx
  simp [W.zero_above hx]

theorem isBigO_zero (W : AnnularProfile) (a : ℝ) :
    W.function =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-a)) := by
  apply isBigO_iff.mpr
  refine ⟨1, ?_⟩
  have hn : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < W.lower :=
    (eventually_lt_nhds W.lower_pos).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn] with x hx
  simp [W.zero_below hx]

theorem convergent (W : AnnularProfile) (s : ℂ) : MellinConvergent W.function s := by
  exact mellinConvergent_of_isBigO_rpow
    (W.smooth.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (W.isBigO_top (s.re + 1)) (by linarith)
    (W.isBigO_zero (s.re - 1)) (by linarith)

theorem mellin_differentiable (W : AnnularProfile) : Differentiable ℂ (mellin W.function) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow
    (W.smooth.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (W.isBigO_top (s.re + 1)) (by linarith)
    (W.isBigO_zero (s.re - 1)) (by linarith)

/-- The logarithmic profile uses precisely Mathlib's Mellin/Fourier sign. -/
def logProfileFun (W : AnnularProfile) (σ : ℝ) (u : ℝ) : ℂ :=
  Real.exp (-σ * u) • W.function (Real.exp (-u))

theorem logProfile_smooth (W : AnnularProfile) (σ : ℝ) :
    ContDiff ℝ ∞ (W.logProfileFun σ) := by
  have hW := W.smooth
  unfold logProfileFun
  fun_prop

theorem logProfile_compact (W : AnnularProfile) (σ : ℝ) :
    HasCompactSupport (W.logProfileFun σ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (-Real.log W.upper) (-Real.log W.lower)))
  intro u hu
  have hW : W.function (Real.exp (-u)) ≠ 0 := by
    intro hz
    exact hu (by simp [logProfileFun, hz])
  have hb := W.supported hW
  have hlo := Real.log_le_log W.lower_pos hb.1
  have hhi := Real.log_le_log (Real.exp_pos (-u)) hb.2
  rw [Real.log_exp] at hlo hhi
  constructor <;> linarith

def logProfile (W : AnnularProfile) (σ : ℝ) : SchwartzMap ℝ ℂ :=
  (W.logProfile_compact σ).toSchwartzMap (W.logProfile_smooth σ)

theorem mellin_vertical_eq_fourier (W : AnnularProfile) (σ t : ℝ) :
    mellin W.function (vertical σ t) =
      𝓕 (W.logProfile σ : ℝ → ℂ) (t / (2 * Real.pi)) := by
  change mellin W.function (vertical σ t) =
    𝓕 (fun u : ℝ => Real.exp (-σ * u) • W.function (Real.exp (-u))) (t / (2 * Real.pi))
  simpa only [vertical_re, vertical_im] using
    (mellin_eq_fourier W.function (s := vertical σ t))

theorem vertical_integrable (W : AnnularProfile) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin W.function) σ := by
  have hi := (𝓕 (W.logProfile σ)).integrable.comp_div
    (by positivity : 2 * Real.pi ≠ 0)
  change Integrable (fun t : ℝ => 𝓕 (W.logProfile σ : ℝ → ℂ) (t / (2 * Real.pi))) at hi
  change Integrable (fun t : ℝ => mellin W.function (vertical σ t))
  simpa only [mellin_vertical_eq_fourier] using hi

theorem vertical_norm_integrable (W : AnnularProfile) (σ : ℝ) :
    Integrable (fun t : ℝ => ‖mellin W.function (vertical σ t)‖) :=
  (W.vertical_integrable σ).norm

/-- Exact 1/(2*pi) normalization, proved from the physical smooth profile. -/
theorem inversion (W : AnnularProfile) (σ x : ℝ) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, mellin W.function (vertical σ t) * (x : ℂ) ^ (-vertical σ t)) =
        W.function x := by
  have h := mellinInv_mellin_eq σ W.function hx (W.convergent σ)
    (W.vertical_integrable σ) W.smooth.continuous.continuousAt
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ, (x : ℂ) ^ (-vertical σ t) * mellin W.function (vertical σ t)) =
      W.function x at h
  simpa only [mul_comm (mellin W.function _)] using h

end AnnularProfile
end ExpansionInterfaces.Mellin
