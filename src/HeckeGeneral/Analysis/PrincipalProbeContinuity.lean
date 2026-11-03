import HeckeGeneral.Analysis.PrincipalSpectrumRegularity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Local integrability of the actual principal probe is derived from
the integrable initial spectrum, independently of any physical growth bound. -/

noncomputable section
namespace HeckeGeneral.Analysis

open MeasureTheory Set
open scoped FourierTransform

theorem continuousOn_mellinInv_of_integrable (σ : ℝ) (F : ℂ → ℂ)
    (hF : Integrable (mellinSpectralLine σ F)) :
    ContinuousOn (mellinInv σ F) (Ioi 0) := by
  have hc : Continuous (𝓕 (mellinSpectralLine σ F)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hF
  have hInv : Continuous (𝓕⁻ (mellinSpectralLine σ F)) := by
    have he : 𝓕⁻ (mellinSpectralLine σ F) =
        (𝓕 (mellinSpectralLine σ F)) ∘ (fun x : ℝ => -x) := by
      funext x
      exact Real.fourierInv_eq_fourier_neg _ x
    rw [he]
    exact hc.comp continuous_neg
  have he : ContinuousOn (fun x : ℝ =>
      (x : ℂ) ^ (-(σ : ℂ)) • 𝓕⁻ (mellinSpectralLine σ F) (-Real.log x)) (Ioi 0) := by
    intro x hx
    have hp : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (-(σ : ℂ))) x :=
      (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hx)).comp
        Complex.continuous_ofReal.continuousAt
    exact (hp.smul (hInv.continuousAt.comp (Real.continuousAt_log (ne_of_gt hx)).neg)).continuousWithinAt
  apply he.congr
  intro x hx
  exact mellinInv_eq_fourierInv σ F hx

theorem continuousOn_positiveLineInverse_of_integrable (c a : ℝ) (F : ℂ → ℂ)
    (hF : Integrable (mellinSpectralLine (a - c) (fun s => F ((a : ℂ) - s)))) :
    ContinuousOn (positiveLineInverse c a F) (Ioi 0) := by
  have he : positiveLineInverse c a F = mellinInv (a - c) (fun s => F ((a : ℂ) - s)) :=
    funext (positiveLineInverse_eq_mellinInv c a F)
  rw [he]
  exact continuousOn_mellinInv_of_integrable _ _ hF

end HeckeGeneral.Analysis

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Characters HeckeGeneral.Analysis

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem continuousOn_principalLineProbe (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2) :
    ContinuousOn (principalLineProbe K S P ψ) (Ioi 0) := by
  rw [principalLineProbe_eq_positiveLineInverse]
  apply continuousOn_positiveLineInverse_of_integrable
  have he : mellinSpectralLine (11 / 16 - 2)
      (fun s => principalSpectrum K S P ψ ((11 / 16 : ℂ) - s)) =
      principalInitialSpectralLine K S P ψ :=
    funext (reflected_mellinSpectralLine_eq (principalSpectrum K S P ψ))
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [he]
  exact integrable_principalInitialSpectralLine K S P ψ hH hHbound

theorem locallyIntegrableOn_principalLineProbe (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2) :
    LocallyIntegrableOn (principalLineProbe K S P ψ) (Ioi 0) :=
  (continuousOn_principalLineProbe K S P ψ hH hHbound).locallyIntegrableOn measurableSet_Ioi

end HeckeGeneral.ThetaSkeleton.Physical
