import Mathlib.Analysis.MellinInversion
import HeckeGeneral.Analysis.MellinZeroDetector

/-!
The reverse Mellin inversion needed for the physical line-2 detector.
The input is ordinary Fourier integrability and continuity of the actual
spectral line. No Mellin identity or zero-free conclusion is assumed.
-/

noncomputable section
namespace HeckeGeneral.Analysis

open MeasureTheory Set
open scoped FourierTransform

def mellinSpectralLine (σ : ℝ) (F : ℂ → ℂ) (y : ℝ) : ℂ :=
  F ((σ : ℂ) + 2 * Real.pi * y * Complex.I)

theorem mellinInv_log_weight (σ : ℝ) (F : ℂ → ℂ) (u : ℝ) :
    Real.exp (-σ * u) • mellinInv σ F (Real.exp (-u)) =
      𝓕⁻ (mellinSpectralLine σ F) u := by
  rw [mellinInv_eq_fourierInv σ F (Real.exp_pos _), Real.log_exp, neg_neg]
  change (Real.exp (-σ * u) : ℂ) *
    ((Real.exp (-u) : ℂ) ^ (-(σ : ℂ)) * 𝓕⁻ (mellinSpectralLine σ F) u) = _
  rw [← mul_assoc]
  have hc : (Real.exp (-σ * u) : ℂ) * (Real.exp (-u) : ℂ) ^ (-(σ : ℂ)) = 1 := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.exp_ne_zero (-u)),
      ← Complex.ofReal_log (Real.exp_pos (-u)).le, Real.log_exp,
      Complex.ofReal_exp, ← Complex.exp_add]
    have he : ((-σ * u : ℝ) : ℂ) + ((-u : ℝ) : ℂ) * (-(σ : ℂ)) = 0 := by
      push_cast
      ring
    rw [he, Complex.exp_zero]
  rw [hc, one_mul]

/-- Mellin inversion in the direction used by the detector. The Fourier
transform is integrable as well as the spectral line itself. -/
theorem mellin_mellinInv_eq (σ : ℝ) (F : ℂ → ℂ)
    (hF : Integrable (mellinSpectralLine σ F))
    (hFF : Integrable (𝓕 (mellinSpectralLine σ F)))
    (hcont : Continuous (mellinSpectralLine σ F)) (t : ℝ) :
    mellin (mellinInv σ F) ((σ : ℂ) + (t : ℂ) * Complex.I) =
      F ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  rw [mellin_eq_fourier]
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  rw [hre, him]
  have he : (fun u : ℝ => Real.exp (-σ * u) • mellinInv σ F (Real.exp (-u))) =
      𝓕⁻ (mellinSpectralLine σ F) := funext (mellinInv_log_weight σ F)
  rw [he, hcont.fourier_fourierInv_eq hF hFF]
  unfold mellinSpectralLine
  congr 1
  push_cast
  field_simp

def positiveLineInverse (c a : ℝ) (F : ℂ → ℂ) (Z : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
    (Z : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I - (a : ℂ)) *
      F ((c : ℂ) + (t : ℂ) * Complex.I)

/-- Changing the line parameter t to -t gives exactly the standard Mellin
inverse, with the normalization and both signs retained. -/
theorem positiveLineInverse_eq_mellinInv (c a : ℝ) (F : ℂ → ℂ) (Z : ℝ) :
    positiveLineInverse c a F Z =
      mellinInv (a - c) (fun s => F ((a : ℂ) - s)) Z := by
  unfold positiveLineInverse mellinInv
  simp only [Complex.real_smul, smul_eq_mul, one_div, Complex.ofReal_inv,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  calc
    _ = ∫ t : ℝ,
        (Z : ℂ) ^ ((c : ℂ) + ((-t : ℝ) : ℂ) * Complex.I - (a : ℂ)) *
          F ((c : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) :=
      (integral_neg_eq_self _ volume).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      congr 2 <;> push_cast <;> ring

/-- Precisely the ordinary spectral regularity needed for the line
identity. This carries neither a Mellin identity nor an analytic bound
for the physical probe. -/
def PositiveLineRegularity (c a : ℝ) (F : ℂ → ℂ) : Prop :=
  let φ := mellinSpectralLine (a - c) (fun s => F ((a : ℂ) - s))
  Integrable φ ∧ Integrable (𝓕 φ) ∧ Continuous φ

theorem mellin_positiveLineInverse (c a : ℝ) (F : ℂ → ℂ)
    (hF : PositiveLineRegularity c a F) (t : ℝ) :
    mellin (positiveLineInverse c a F) ((a : ℂ) - ((c : ℂ) + (t : ℂ) * Complex.I)) =
      F ((c : ℂ) + (t : ℂ) * Complex.I) := by
  have he : positiveLineInverse c a F =
      mellinInv (a - c) (fun s => F ((a : ℂ) - s)) :=
    funext (positiveLineInverse_eq_mellinInv c a F)
  rw [he]
  have hs : (a : ℂ) - ((c : ℂ) + (t : ℂ) * Complex.I) =
      ((a - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hs, mellin_mellinInv_eq _ _ hF.1 hF.2.1 hF.2.2]
  congr 1
  push_cast
  ring

theorem physicalMellin_positiveLineInverse (c : ℝ) (F : ℂ → ℂ)
    (hF : PositiveLineRegularity c (11 / 16) F) (t : ℝ) :
    physicalMellin (positiveLineInverse c (11 / 16) F)
      ((c : ℂ) + (t : ℂ) * Complex.I) = F ((c : ℂ) + (t : ℂ) * Complex.I) := by
  simpa only [physicalMellin, Complex.ofReal_div, Complex.ofReal_ofNat] using
    mellin_positiveLineInverse c (11 / 16) F hF t

end HeckeGeneral.Analysis
