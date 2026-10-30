import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic

/-!
Genuine absolute local moments for every positive
small Mellin exponent. The singularity at zero is proved locally integrable
by the actual real dimension. Outside the unit ball the negative power is
at most one, so ordinary Schwartz integrability suffices.

For the real and complex local fields this gives the additive density
norm^(d*(sigma-1)) with d=1 and d=2 respectively. The general Euclidean
statement is only a weighted-integrability lemma; it asserts no field
structure or modulus on an arbitrary vector space.
-/

noncomputable section

namespace HeckeGeneral.Analysis.SmallPositiveArchimedeanMomentDraft

open MeasureTheory Set Metric
open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every Schwartz function has the actual positive-small-exponent absolute
moment for the local multiplicative density in real dimension d. -/
theorem integrable_schwartz_norm_small_positive_moment
    (hd : 1 ≤ Module.finrank ℝ E) (φ : SchwartzMap E ℂ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Integrable (fun x : E => ‖φ x‖ * ‖x‖ ^ ((Module.finrank ℝ E : ℝ) * (σ - 1))) := by
  let p : ℝ := (Module.finrank ℝ E : ℝ) * (σ - 1)
  let α : ℝ := (Module.finrank ℝ E : ℝ) * (1 - σ)
  have hdpos : 0 < (Module.finrank ℝ E : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hd
  have hα : α < Module.finrank ℝ E := by
    dsimp only [α]; nlinarith [mul_pos hdpos hσ]
  have hp : p ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos hdpos.le (sub_nonpos.mpr hσ1)
  have hpα : p = -α := by dsimp only [p, α]; ring
  have hwmeas : AEStronglyMeasurable (fun x : E => ‖x‖ ^ p) volume :=
    (measurable_norm.pow_const p).aestronglyMeasurable
  have hw : IntegrableOn (fun x : E => ‖x‖ ^ p) (ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow hd hα (C := 1)
    · exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
          one_mul, hpα]
    · exact hwmeas
  let C : ℝ := SchwartzMap.seminorm ℝ 0 0 φ
  have hC : 0 ≤ C := apply_nonneg _ _
  have hmeas : AEStronglyMeasurable (fun x : E => ‖φ x‖ * ‖x‖ ^ p) volume :=
    (φ.continuous.measurable.norm.mul (measurable_norm.pow_const p)).aestronglyMeasurable
  have hnear : IntegrableOn (fun x : E => ‖φ x‖ * ‖x‖ ^ p) (ball 0 1) := by
    apply (hw.const_mul C).mono' hmeas.restrict
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
      exact mul_le_mul_of_nonneg_right (φ.norm_le_seminorm ℝ x)
        (Real.rpow_nonneg (norm_nonneg _) _)
  have hφ : Integrable (fun x : E => ‖φ x‖) volume := φ.integrable.norm
  have hfar : IntegrableOn (fun x : E => ‖φ x‖ * ‖x‖ ^ p) (ball 0 1)ᶜ := by
    apply hφ.integrableOn.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet.compl] with x hx
    have hxnorm : 1 ≤ ‖x‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hxnorm hp)
  change Integrable (fun x : E => ‖φ x‖ * ‖x‖ ^ p)
  rw [← integrableOn_univ, ← union_compl_self (ball (0 : E) 1), integrableOn_union]
  exact ⟨hnear, hfar⟩

/-- The complex density is |z|^(2 sigma-2), including its integrable
singularity for every sigma in (0,1]. -/
theorem integrable_complex_schwartz_small_positive_moment
    (φ : SchwartzMap ℂ ℂ) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Integrable (fun z : ℂ => ‖φ z‖ * ‖z‖ ^ (2 * σ - 2)) := by
  simpa only [Complex.finrank_real_complex, Nat.cast_ofNat, mul_sub, mul_one] using
    integrable_schwartz_norm_small_positive_moment
      (E := ℂ) (by norm_num [Complex.finrank_real_complex]) φ σ hσ hσ1

/-- The real density is |x|^(sigma-1). -/
theorem integrable_real_schwartz_small_positive_moment
    (φ : SchwartzMap ℝ ℂ) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Integrable (fun x : ℝ => ‖φ x‖ * ‖x‖ ^ (σ - 1)) := by
  simpa only [Module.finrank_self, Nat.cast_one, one_mul] using
    integrable_schwartz_norm_small_positive_moment
      (E := ℝ) (by simp) φ σ hσ hσ1

end HeckeGeneral.Analysis.SmallPositiveArchimedeanMomentDraft
