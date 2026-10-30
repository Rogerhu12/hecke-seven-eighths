import HeckeSkeleton.HighBinSupport.BoundaryRectangle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
/-!
Parameter integration of finite contour transport and a quantitative
three-variable horizontal-face bound. The integrability premises are
Fubini hypotheses; the only decay input is an explicit one-dimensional
profile seminorm. The resulting finite-box difference is not assumed.
-/

noncomputable section
namespace HighBinBoundary

open MeasureTheory Set Complex
open scoped BigOperators

/-- The s-integration stays outermost, as in the project's rowContourBox. -/
def parameterBox {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (F : ℂ → α → ℂ) (σ H : ℝ) : ℂ :=
  ∫ t : ℝ in -H..H, ∫ q, F ((σ : ℂ) + t * I) q ∂μ

/-- Integrate the actual two horizontal faces; only the arithmetic row set
is fixed. No amplitude-dependent set is moved. -/
theorem parameter_rectangle_identity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (F : ℂ → α → ℂ)
    (l r H : ℝ) (hH : 0 ≤ H)
    (hl : Integrable (fun p : ℝ × α => F ((l : ℂ) + p.1 * I) p.2)
      ((volume.restrict (Ioc (-H) H)).prod μ))
    (hr : Integrable (fun p : ℝ × α => F ((r : ℂ) + p.1 * I) p.2)
      ((volume.restrict (Ioc (-H) H)).prod μ))
    (hF : ∀ᵐ q ∂μ, DifferentiableOn ℂ (fun s => F s q)
      (uIcc l r ×ℂ uIcc (-H) H)) :
    parameterBox μ F r H - parameterBox μ F l H =
      ∫ q, I * ((∫ x : ℝ in l..r, F ((x : ℂ) + (-H) * I) q) -
        (∫ x : ℝ in l..r, F ((x : ℂ) + H * I) q)) ∂μ := by
  have hHH : -H ≤ H := by linarith
  have hli : Integrable (fun q => ∫ t : ℝ in -H..H, F ((l : ℂ) + t * I) q) μ := by
    simpa only [intervalIntegral.integral_of_le hHH] using hl.integral_prod_right
  have hri : Integrable (fun q => ∫ t : ℝ in -H..H, F ((r : ℂ) + t * I) q) μ := by
    simpa only [intervalIntegral.integral_of_le hHH] using hr.integral_prod_right
  have hs (σ : ℝ)
      (hσ : Integrable (fun p : ℝ × α => F ((σ : ℂ) + p.1 * I) p.2)
        ((volume.restrict (Ioc (-H) H)).prod μ)) :
      parameterBox μ F σ H = ∫ q, (∫ t : ℝ in -H..H, F ((σ : ℂ) + t * I) q) ∂μ := by
    unfold parameterBox
    simp only [intervalIntegral.integral_of_le hHH]
    exact integral_integral_swap hσ
  rw [hs r hr, hs l hl, ← integral_sub hri hli]
  apply integral_congr_ae
  filter_upwards [hF] with q hq
  exact finite_rectangle_identity (fun s => F s q) l r H hq

/-- Uniform bounded faces imply a bound for the original finite box. -/
theorem parameter_rectangle_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (F : ℂ → α → ℂ)
    (l r H M : ℝ) (hH : 0 ≤ H)
    (hl : Integrable (fun p : ℝ × α => F ((l : ℂ) + p.1 * I) p.2)
      ((volume.restrict (Ioc (-H) H)).prod μ))
    (hr : Integrable (fun p : ℝ × α => F ((r : ℂ) + p.1 * I) p.2)
      ((volume.restrict (Ioc (-H) H)).prod μ))
    (hF : ∀ᵐ q ∂μ, DifferentiableOn ℂ (fun s => F s q)
      (uIcc l r ×ℂ uIcc (-H) H))
    (hminus : ∀ᵐ q ∂μ, ∀ x ∈ uIcc l r, ‖F ((x : ℂ) + (-H) * I) q‖ ≤ M)
    (hplus : ∀ᵐ q ∂μ, ∀ x ∈ uIcc l r, ‖F ((x : ℂ) + H * I) q‖ ≤ M) :
    ‖parameterBox μ F r H - parameterBox μ F l H‖ ≤
      2 * M * |r - l| * μ.real univ := by
  rw [parameter_rectangle_identity μ F l r H hH hl hr hF]
  apply MeasureTheory.norm_integral_le_of_norm_le_const
  filter_upwards [hF, hminus, hplus] with q hq hm hp
  rw [← finite_rectangle_identity (fun s => F s q) l r H hq]
  exact finite_rectangle_bound (fun s => F s q) l r H M hq hm hp

/-- Two bounded height coordinates, using the same closed box as the project. -/
def twoHeightMeasure (H : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))

instance (H : ℝ) : IsFiniteMeasure (twoHeightMeasure H) := by
  unfold twoHeightMeasure
  infer_instance

/-- The exact finite-box mass; no asymptotic counting is used. -/
theorem twoHeightMeasure_mass (H : ℝ) (hH : 0 ≤ H) :
    (twoHeightMeasure H).real univ = 4 * H ^ 2 := by
  unfold twoHeightMeasure
  rw [← Set.univ_prod_univ, measureReal_prod_prod]
  simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (show 0 ≤ H - -H by linarith)]
  ring

/-- Fubini identification with the project's three nested closed-box integrals.
The time coordinate is still outermost; no moving row selector is introduced. -/
theorem parameterBox_eq_nested_Icc
    (F : ℂ → ℝ × ℝ → ℂ) (σ H : ℝ) (hH : 0 ≤ H)
    (hF : Integrable (fun p : ℝ × (ℝ × ℝ) => F ((σ : ℂ) + p.1 * I) p.2)
      ((volume.restrict (Icc (-H) H)).prod (twoHeightMeasure H))) :
    parameterBox (twoHeightMeasure H) F σ H =
      ∫ ts in Icc (-H) H, ∫ tw in Icc (-H) H, ∫ tz in Icc (-H) H,
        F ((σ : ℂ) + ts * I) (tw, tz) := by
  unfold parameterBox
  rw [intervalIntegral.integral_of_le (show -H ≤ H by linarith),
    ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [hF.prod_right_ae] with ts hts
  exact integral_prod _ hts

/-- A single z-profile seminorm and the coupled Gaussian give a
uniform bound on either horizontal s-face, including the bad corner z=-s. -/
theorem coupled_face_bound (F : ℂ → ℝ × ℝ → ℂ) (g : ℝ → ℂ)
    (n : ℕ) (M D H σ x : ℝ) (q : ℝ × ℝ)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hx : |x| = H)
    (hg : ∀ y : ℝ, (1 + |y|) ^ n * ‖g y‖ ≤ D)
    (hF : ‖F ((σ : ℂ) + x * I) q‖ ≤
      M * (Real.exp (-((x + q.2) ^ 2)) * ‖g q.2‖)) :
    ‖F ((σ : ℂ) + x * I) q‖ ≤ M * gaussianMoment n * D / (1 + H) ^ n := by
  have hpos : 0 < (1 + H) ^ n := by positivity
  apply (le_div_iff₀ hpos).mpr
  have hh := coupled_gaussian_profile_bound g n D hg x q.2
  rw [hx] at hh
  calc
    _ ≤ (M * (Real.exp (-((x + q.2) ^ 2)) * ‖g q.2‖)) * (1 + H) ^ n :=
      mul_le_mul_of_nonneg_right hF hpos.le
    _ = M * ((1 + H) ^ n * (Real.exp (-((x + q.2) ^ 2)) * ‖g q.2‖)) := by ring
    _ ≤ M * (gaussianMoment n * D) := mul_le_mul_of_nonneg_left hh hM
    _ = _ := by ring

/-- The coupled Gaussian/profile input gives arbitrary power decay of the
actual three-variable finite-box difference. The two free height integrals
cost precisely H^2; two additional profile derivatives absorb that cost. -/
theorem coupled_box_boundary_bound
    (F : ℂ → ℝ × ℝ → ℂ) (g : ℝ → ℂ) (n : ℕ)
    (l r H M D : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hl : Integrable (fun p : ℝ × (ℝ × ℝ) => F ((l : ℂ) + p.1 * I) p.2)
      ((volume.restrict (Ioc (-H) H)).prod (twoHeightMeasure H)))
    (hr : Integrable (fun p : ℝ × (ℝ × ℝ) => F ((r : ℂ) + p.1 * I) p.2)
      ((volume.restrict (Ioc (-H) H)).prod (twoHeightMeasure H)))
    (hF : ∀ᵐ q ∂twoHeightMeasure H, DifferentiableOn ℂ (fun s => F s q)
      (uIcc l r ×ℂ uIcc (-H) H))
    (hg : ∀ y : ℝ, (1 + |y|) ^ n * ‖g y‖ ≤ D)
    (hkernel : ∀ᵐ q ∂twoHeightMeasure H, ∀ σ ∈ uIcc l r, ∀ x : ℝ, |x| = H →
      ‖F ((σ : ℂ) + x * I) q‖ ≤
        M * (Real.exp (-((x + q.2) ^ 2)) * ‖g q.2‖)) :
    ‖parameterBox (twoHeightMeasure H) F r H -
      parameterBox (twoHeightMeasure H) F l H‖ ≤
        8 * M * gaussianMoment n * D * |r - l| * H ^ 2 / (1 + H) ^ n := by
  have hm : ∀ᵐ q ∂twoHeightMeasure H, ∀ σ ∈ uIcc l r,
      ‖F ((σ : ℂ) + (-H) * I) q‖ ≤ M * gaussianMoment n * D / (1 + H) ^ n := by
    filter_upwards [hkernel] with q hq σ hσ
    simpa only [Complex.ofReal_neg] using
      coupled_face_bound F g n M D H σ (-H) q hM hH
        (by simp [abs_of_nonneg hH]) hg (hq σ hσ (-H) (by simp [abs_of_nonneg hH]))
  have hp : ∀ᵐ q ∂twoHeightMeasure H, ∀ σ ∈ uIcc l r,
      ‖F ((σ : ℂ) + H * I) q‖ ≤ M * gaussianMoment n * D / (1 + H) ^ n := by
    filter_upwards [hkernel] with q hq σ hσ
    exact coupled_face_bound F g n M D H σ H q hM hH
      (abs_of_nonneg hH) hg (hq σ hσ H (abs_of_nonneg hH))
  apply (parameter_rectangle_bound (twoHeightMeasure H) F l r H
    (M * gaussianMoment n * D / (1 + H) ^ n) hH hl hr hF hm hp).trans_eq
  rw [twoHeightMeasure_mass H hH]
  ring

#print axioms parameter_rectangle_identity
#print axioms parameter_rectangle_bound
#print axioms coupled_box_boundary_bound
#print axioms parameterBox_eq_nested_Icc

end HighBinBoundary
