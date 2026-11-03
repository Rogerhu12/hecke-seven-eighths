import HeckeGeneral.Analysis.MellinInverseLine
import HeckeGeneral.Analysis.LogGaussianMellin

/-!
The physical bound itself supplies the second integrability condition of
Fourier inversion. Only integrability and continuity of the spectral line
remain source-side conditions; integrability of its Fourier transform is
derived, not an additional transferred assumption.
-/

noncomputable section
namespace HeckeGeneral.Analysis

open MeasureTheory Set
open scoped FourierTransform Topology

theorem integrable_fourier_spectralLine_of_mellinConvergent
    (σ : ℝ) (F : ℂ → ℂ) (h : MellinConvergent (mellinInv σ F) (σ : ℂ)) :
    Integrable (𝓕 (mellinSpectralLine σ F)) := by
  have hlog := (mellinConvergent_iff_log_integrable (mellinInv σ F) (σ : ℂ)).mp h
  have hneg := hlog.comp_neg
  have he (u : ℝ) : Complex.exp ((σ : ℂ) * ((-u : ℝ) : ℂ)) *
      mellinInv σ F (Real.exp (-u)) = 𝓕⁻ (mellinSpectralLine σ F) u := by
    have hc : Complex.exp ((σ : ℂ) * ((-u : ℝ) : ℂ)) = (Real.exp (-σ * u) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hc]
    exact mellinInv_log_weight σ F u
  have hInv : Integrable (𝓕⁻ (mellinSpectralLine σ F)) := by
    convert hneg using 1
    funext u
    exact (he u).symm
  have hInvNeg := hInv.comp_neg
  simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hInvNeg

theorem positiveLineRegularity_of_mellinConvergent
    (c a : ℝ) (F : ℂ → ℂ)
    (hF : Integrable (mellinSpectralLine (a - c) (fun s => F ((a : ℂ) - s))))
    (hcont : Continuous (mellinSpectralLine (a - c) (fun s => F ((a : ℂ) - s))))
    (hconv : MellinConvergent (positiveLineInverse c a F) ((a - c : ℝ) : ℂ)) :
    PositiveLineRegularity c a F := by
  refine ⟨hF, integrable_fourier_spectralLine_of_mellinConvergent (a - c) _ ?_, hcont⟩
  have he : positiveLineInverse c a F =
      mellinInv (a - c) (fun s => F ((a : ℂ) - s)) :=
    funext (positiveLineInverse_eq_mellinInv c a F)
  rwa [he] at hconv

theorem PhysicalProbeBound.mellinConvergent {f : ℝ → ℂ} {b c : ℝ}
    (hf : PhysicalProbeBound f b) (hbc : b < c) :
    MellinConvergent f ((11 / 16 : ℂ) - (c : ℂ)) := by
  have ht : f =O[Filter.atTop] (fun Z : ℝ => Z ^ (-((11 / 16 : ℝ) - b))) := by
    simpa only [show -((11 / 16 : ℝ) - b) = b - 11 / 16 by ring] using hf.2.1
  apply mellinConvergent_of_isBigO_rpow
    (a := (11 / 16 : ℝ) - b) (b := (11 / 16 : ℝ) - c - 1) hf.1 ht
  · norm_num
    linarith
  · exact hf.2.2 (-((11 / 16 : ℝ) - c - 1))
  · norm_num

theorem positiveLineRegularity_of_physicalProbeBound (c : ℝ) (F : ℂ → ℂ) {b : ℝ}
    (hbc : b < c) (hf : PhysicalProbeBound (positiveLineInverse c (11 / 16) F) b)
    (hF : Integrable (mellinSpectralLine (11 / 16 - c) (fun s => F ((11 / 16 : ℂ) - s))))
    (hcont : Continuous (mellinSpectralLine (11 / 16 - c) (fun s => F ((11 / 16 : ℂ) - s)))) :
    PositiveLineRegularity c (11 / 16) F := by
  apply positiveLineRegularity_of_mellinConvergent c (11 / 16) F
  · simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hF
  · simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hcont
  · simpa only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_ofNat] using
      hf.mellinConvergent hbc

end HeckeGeneral.Analysis
