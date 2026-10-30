import HeckeSkeleton.SmallRadius.SmallPositiveArchimedeanMoment
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
A uniform local positive-Mellin absolute integral
bound by finitely many original Schwartz seminorms. The positive constant
and the seminorm indices are chosen before the Schwartz input.

This is a local Euclidean statement. It does not identify a norm-one Haar
orbital integral with the local-product integral, and does not yet close the
multi-place joint-profile estimate.
-/

noncomputable section

namespace HeckeGeneral.Analysis.SmallPositiveArchimedeanMomentDraft

open MeasureTheory Set Metric
open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A fixed integrable local envelope, including the singularity at zero. -/
theorem integrable_small_positive_moment_envelope
    (hd : 1 ≤ Module.finrank ℝ E) (N : ℕ)
    (hN : (Module.finrank ℝ E : ℝ) < N)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Integrable (fun x : E =>
      (1 + ‖x‖) ^ (-(N : ℝ)) *
        ‖x‖ ^ ((Module.finrank ℝ E : ℝ) * (σ - 1))) := by
  let p : ℝ := (Module.finrank ℝ E : ℝ) * (σ - 1)
  let α : ℝ := (Module.finrank ℝ E : ℝ) * (1 - σ)
  have hdpos : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hd
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
  let k : E → ℝ := fun x => (1 + ‖x‖) ^ (-(N : ℝ)) * ‖x‖ ^ p
  have hkmeas : AEStronglyMeasurable k volume := by
    dsimp only [k]
    exact (((measurable_const.add measurable_norm).pow_const _).mul
      (measurable_norm.pow_const p)).aestronglyMeasurable
  have hkpos (x : E) : 0 ≤ k x := by dsimp only [k]; positivity
  have hnear : IntegrableOn k (ball 0 1) := by
    apply hw.mono' hkmeas.restrict
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hkpos x)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (norm_nonneg _) _)
        (Real.rpow_le_one_of_one_le_of_nonpos
          (le_add_of_nonneg_right (norm_nonneg x)) (neg_nonpos.mpr (Nat.cast_nonneg N)))
  have htail : Integrable (fun x : E => (1 + ‖x‖) ^ (-(N : ℝ))) :=
    integrable_one_add_norm hN
  have hfar : IntegrableOn k (ball 0 1)ᶜ := by
    apply htail.integrableOn.mono' hkmeas.restrict
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet.compl] with x hx
    have hxnorm : 1 ≤ ‖x‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hkpos x)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_le_one_of_one_le_of_nonpos hxnorm hp)
  change Integrable k
  rw [← integrableOn_univ, ← union_compl_self (ball (0 : E) 1), integrableOn_union]
  exact ⟨hnear, hfar⟩

/-- The actual local moment is a bounded seminorm on Schwartz space, with
the constant selected before the input. No local zeta bound is assumed. -/
theorem exists_small_positive_moment_seminorm_bound
    (hd : 1 ≤ Module.finrank ℝ E)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ φ : SchwartzMap E ℂ,
        (∫ x : E, ‖φ x‖ * ‖x‖ ^ ((Module.finrank ℝ E : ℝ) * (σ - 1))) ≤
          C * s.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ := by
  let N : ℕ := Module.finrank ℝ E + 1
  have hN : (Module.finrank ℝ E : ℝ) < N := by
    dsimp only [N]
    push_cast
    exact lt_add_one _
  let p : ℝ := (Module.finrank ℝ E : ℝ) * (σ - 1)
  let k : E → ℝ := fun x => (1 + ‖x‖) ^ (-(N : ℝ)) * ‖x‖ ^ p
  have hk : Integrable k := integrable_small_positive_moment_envelope hd N hN σ hσ hσ1
  have hkpos (x : E) : 0 ≤ k x := by dsimp only [k]; positivity
  have hi : 0 ≤ ∫ x : E, k x := integral_nonneg hkpos
  refine ⟨Finset.Iic (N, 0), 2 ^ N * ((∫ x : E, k x) + 1), by positivity, ?_⟩
  intro φ
  let B : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hdecay (x : E) : ‖φ x‖ ≤ (1 + ‖x‖) ^ (-(N : ℝ)) * B := by
    rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul,
      le_div_iff₀' (by positivity), Real.rpow_natCast]
    simpa [B] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl φ x)
  have hmoment : Integrable (fun x : E => ‖φ x‖ * ‖x‖ ^ p) :=
    integrable_schwartz_norm_small_positive_moment hd φ σ hσ hσ1
  have hbound := integral_mono hmoment (hk.const_mul B) (fun x => by
    calc
      ‖φ x‖ * ‖x‖ ^ p ≤ ((1 + ‖x‖) ^ (-(N : ℝ)) * B) * ‖x‖ ^ p :=
        mul_le_mul_of_nonneg_right (hdecay x) (Real.rpow_nonneg (norm_nonneg _) _)
      _ = B * k x := by dsimp only [k]; ring)
  rw [integral_const_mul] at hbound
  change (∫ x : E, ‖φ x‖ * ‖x‖ ^ p) ≤ _
  calc
    _ ≤ B * ∫ x : E, k x := hbound
    _ ≤ B * ((∫ x : E, k x) + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hB
    _ = _ := by dsimp only [B]; ring

end HeckeGeneral.Analysis.SmallPositiveArchimedeanMomentDraft
