/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The finite-rectangle calculation adapts openai/math, commit fd4aeeb2,
OAI/NumberTheory/DirichletL/Hecke/PrimeDyadicContour.lean.
The limiting argument below is independent of the Hecke project.
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# A quantitative vertical-contour shift

Holomorphy on a closed strip and a uniform inverse-quadratic majorant imply
equality of the two infinite vertical integrals.  Neither a contour identity
nor the vanishing of horizontal segments is assumed in the final theorem.
-/

noncomputable section
open Filter MeasureTheory Set Complex
open scoped Topology

namespace PrimeCancellation.Contour

theorem finite_rectangle (F : ℂ → ℂ) (a b T : ℝ)
    (hhol : DifferentiableOn ℂ F (uIcc a b ×ℂ uIcc (-T) T)) :
    (∫ t : ℝ in -T..T, F ((b : ℂ) + t * I)) =
      (∫ t : ℝ in -T..T, F ((a : ℂ) + t * I)) +
        I * ((∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * I)) -
          (∫ x : ℝ in a..b, F ((x : ℂ) + T * I))) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    F ((a : ℂ) + (-T) * I) ((b : ℂ) + T * I) (by simpa using hhol)
  have hr :
      (∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * I)) -
        (∫ x : ℝ in a..b, F ((x : ℂ) + T * I)) +
        I * (∫ t : ℝ in -T..T, F ((b : ℂ) + t * I)) -
        I * (∫ t : ℝ in -T..T, F ((a : ℂ) + t * I)) = 0 := by
    simpa [smul_eq_mul] using h
  have hh := congrArg (fun z : ℂ => -I * z) hr
  ring_nf at hh ⊢
  simp only [I_sq] at hh
  linear_combination hh

theorem vertical_integrable_of_quadratic_bound (F : ℂ → ℂ) (σ C : ℝ)
    (hcont : Continuous (fun t : ℝ => F ((σ : ℂ) + t * I)))
    (hbound : ∀ t : ℝ, ‖F ((σ : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2)) :
    Integrable (fun t : ℝ => F ((σ : ℂ) + t * I)) := by
  apply (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    simpa only [div_eq_mul_inv] using hbound t)

theorem norm_vertical_integral_le (F : ℂ → ℂ) (σ C : ℝ)
    (hbound : ∀ t : ℝ, ‖F ((σ : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2)) :
    ‖∫ t : ℝ, F ((σ : ℂ) + t * I)‖ ≤ C * Real.pi := by
  calc
    _ ≤ ∫ t : ℝ, C * (1 + t ^ 2)⁻¹ :=
      norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul C)
        (Filter.Eventually.of_forall (fun t => by
          simpa only [div_eq_mul_inv] using hbound t))
    _ = C * Real.pi := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem norm_horizontal_integral_le (F : ℂ → ℂ) (a b t C : ℝ) (hab : a ≤ b)
    (hbound : ∀ x ∈ Icc a b, ‖F ((x : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2)) :
    ‖∫ x : ℝ in a..b, F ((x : ℂ) + t * I)‖ ≤
      (C / (1 + t ^ 2)) * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [uIoc_of_le hab] at hx
  exact hbound x ⟨hx.1.le, hx.2⟩

theorem horizontal_integral_tendsto_zero (F : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ,
      ‖F ((x : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2))
    (v : ℝ → ℝ) (hv : Tendsto (fun T => 1 + (v T) ^ 2) atTop atTop) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + (v T) * I))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => (C / (1 + (v T) ^ 2)) * |b - a|)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop hv).mul_const |b - a|
  exact squeeze_zero_norm
    (fun T => norm_horizontal_integral_le F a b (v T) C hab
      (fun x hx => hbound x hx (v T))) hlim

/-- Shifting an infinite vertical line: all side limits are proved from the
uniform bound, and line integrability is proved rather than postulated. -/
theorem integral_eq_of_strip_quadratic_decay (F : ℂ → ℂ) (a b C : ℝ)
    (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ F z)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖F ((σ : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2)) :
    (∫ t : ℝ, F ((a : ℂ) + t * I)) =
      ∫ t : ℝ, F ((b : ℂ) + t * I) := by
  have hcont (σ : ℝ) (hσ : σ ∈ Icc a b) :
      Continuous (fun t : ℝ => F ((σ : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hdiff _ (by simpa using hσ.1) (by simpa using hσ.2)).continuousAt.comp
      (by fun_prop)
  have ha := vertical_integrable_of_quadratic_bound F a C
    (hcont a ⟨le_rfl, hab⟩) (hbound a ⟨le_rfl, hab⟩)
  have hb := vertical_integrable_of_quadratic_bound F b C
    (hcont b ⟨hab, le_rfl⟩) (hbound b ⟨hab, le_rfl⟩)
  have hden : Tendsto (fun T : ℝ => 1 + T ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by decide : 2 ≠ 0))
  have htop := horizontal_integral_tendsto_zero F a b C hab hbound
    (fun T => T) hden
  have hbottom := horizontal_integral_tendsto_zero F a b C hab hbound
    (fun T => -T) (by simpa only [neg_sq] using hden)
  have hleft := intervalIntegral_tendsto_integral ha
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  have hright := intervalIntegral_tendsto_integral hb
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  have hhol (T : ℝ) : DifferentiableOn ℂ F (uIcc a b ×ℂ uIcc (-T) T) := by
    intro z hz
    have hre : z.re ∈ Icc a b := by
      have hzre : z.re ∈ uIcc a b := hz.1
      simpa only [uIcc_of_le hab] using hzre
    exact (hdiff z hre.1 hre.2).differentiableWithinAt
  have heq (T : ℝ) := finite_rectangle F a b T (hhol T)
  have hsame := hleft.add ((hbottom.sub htop).const_mul I)
  simp only [sub_self, mul_zero, add_zero] at hsame
  simp only [id_eq, Complex.ofReal_neg] at hsame hright
  have hsame' := hsame.congr' (Filter.Eventually.of_forall (fun T => (heq T).symm))
  exact (tendsto_nhds_unique hright hsame').symm

end PrimeCancellation.Contour

#print axioms PrimeCancellation.Contour.finite_rectangle
#print axioms PrimeCancellation.Contour.vertical_integrable_of_quadratic_bound
#print axioms PrimeCancellation.Contour.norm_vertical_integral_le
#print axioms PrimeCancellation.Contour.norm_horizontal_integral_le
#print axioms PrimeCancellation.Contour.horizontal_integral_tendsto_zero
#print axioms PrimeCancellation.Contour.integral_eq_of_strip_quadratic_decay
