import HeckeGeneral.Analysis.HeckeDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Quantitative control in the far right half-plane

Every nonunit integral ideal has norm at least two. After removing the
unit-ideal term, this gives an explicit factor 2^{-(Re(s)-σ)} times a
fixed, genuinely summable logarithmic majorant at any σ>1. This controls
the ideal series and all of its derivatives uniformly in the imaginary
direction; the constants are actual sums, not assumed estimates.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField Ideal HeckeGeneral.Characters Filter
open scoped Topology Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

theorem two_le_idealNorm_of_ne_one (I : NonzeroIdeal K) (hI : I ≠ 1) :
    2 ≤ idealNorm K I := by
  have hn : absNorm I.val ≠ 1 := by
    intro h
    apply hI
    apply Subtype.ext
    simpa only [Submonoid.coe_one, Ideal.one_eq_top] using Ideal.absNorm_eq_one_iff.mp h
  have hp := Ideal.absNorm_pos_of_nonZeroDivisors I
  have htwo : 2 ≤ absNorm I.val := by omega
  change (2 : ℝ) ≤ (absNorm I.val : ℝ)
  exact_mod_cast htwo

/-- The coefficient-independent majorant with the unit ideal removed. -/
def idealLogTailMajorant (k : ℕ) (σ : ℝ) : ℝ :=
  ∑' I : NonzeroIdeal K, if I = 1 then 0 else
    Real.log (idealNorm K I) ^ k * idealNorm K I ^ (-σ)

theorem summable_idealLogTailMajorant_terms (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : NonzeroIdeal K => if I = 1 then 0 else
      Real.log (idealNorm K I) ^ k * idealNorm K I ^ (-σ)) := by
  apply Summable.of_nonneg_of_le ?_ ?_ (summable_ideal_logPower_rpow K k hσ)
  · intro I
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (pow_nonneg (Real.log_nonneg (one_le_idealNorm K I)) k)
        (Real.rpow_nonneg (idealNorm_pos K I).le _)
  · intro I
    split_ifs
    · exact mul_nonneg (pow_nonneg (Real.log_nonneg (one_le_idealNorm K I)) k)
        (Real.rpow_nonneg (idealNorm_pos K I).le _)
    · exact le_rfl

theorem idealLogTailMajorant_nonneg (k : ℕ) (σ : ℝ) :
    0 ≤ idealLogTailMajorant K k σ := by
  apply tsum_nonneg
  intro I
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (pow_nonneg (Real.log_nonneg (one_le_idealNorm K I)) k)
      (Real.rpow_nonneg (idealNorm_pos K I).le _)

@[simp] theorem idealLogTerm_one (a : NonzeroIdeal K → ℂ) (k : ℕ) (s : ℂ) :
    idealLogTerm K a k s 1 = if k = 0 then a 1 else 0 := by
  cases k <;> simp [idealLogTerm, dirichletTerm, idealNorm]

theorem idealLogSeries_sub_unit_eq_tail (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    idealLogSeries K a k s - idealLogTerm K a k s 1 =
      ∑' I, if I = 1 then 0 else idealLogTerm K a k s I := by
  rw [idealLogSeries,
    (absolutelySummable_idealLogTerm K a ha k hs).of_norm.tsum_eq_add_tsum_ite 1,
    add_sub_cancel_left]

theorem norm_idealLogTerm_tail_bound (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re)
    (I : NonzeroIdeal K) :
    ‖if I = 1 then 0 else idealLogTerm K a k s I‖ ≤
      (2 : ℝ) ^ (-(s.re - σ)) *
        (if I = 1 then 0 else Real.log (idealNorm K I) ^ k * idealNorm K I ^ (-σ)) := by
  split_ifs with hI
  · simp
  have hq : 0 < idealNorm K I := idealNorm_pos K I
  have hdecay : idealNorm K I ^ (-(s.re - σ)) ≤ (2 : ℝ) ^ (-(s.re - σ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (two_le_idealNorm_of_ne_one K I hI)
      (neg_nonpos.mpr (sub_nonneg.mpr hs))
  calc
    _ ≤ Real.log (idealNorm K I) ^ k * idealNorm K I ^ (-s.re) :=
      norm_idealLogTerm_le K a ha k s I
    _ = (Real.log (idealNorm K I) ^ k * idealNorm K I ^ (-σ)) *
        idealNorm K I ^ (-(s.re - σ)) := by
      rw [show -s.re = -σ + -(s.re - σ) by ring, Real.rpow_add hq]
      ring
    _ ≤ (Real.log (idealNorm K I) ^ k * idealNorm K I ^ (-σ)) *
        (2 : ℝ) ^ (-(s.re - σ)) :=
      mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg (pow_nonneg (Real.log_nonneg (one_le_idealNorm K I)) k)
          (Real.rpow_nonneg hq.le _))
    _ = _ := mul_comm _ _

/-- All logarithmic moments have an explicit, imaginary-part independent decay bound. -/
theorem norm_idealLogSeries_sub_unit_le (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) :
    ‖idealLogSeries K a k s - idealLogTerm K a k s 1‖ ≤
      (2 : ℝ) ^ (-(s.re - σ)) * idealLogTailMajorant K k σ := by
  have hsone : 1 < s.re := lt_of_lt_of_le hσ hs
  have habs : Summable (fun I : NonzeroIdeal K =>
      ‖if I = 1 then 0 else idealLogTerm K a k s I‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
      (absolutelySummable_idealLogTerm K a ha k hsone)
    intro I
    split_ifs
    · simp
    · exact le_rfl
  have hmajor := (summable_idealLogTailMajorant_terms K k hσ).mul_left
    ((2 : ℝ) ^ (-(s.re - σ)))
  rw [idealLogSeries_sub_unit_eq_tail K a ha k hsone]
  calc
    _ ≤ ∑' I : NonzeroIdeal K, ‖if I = 1 then 0 else idealLogTerm K a k s I‖ :=
      norm_tsum_le_tsum_norm habs
    _ ≤ ∑' I : NonzeroIdeal K, (2 : ℝ) ^ (-(s.re - σ)) *
        (if I = 1 then 0 else Real.log (idealNorm K I) ^ k * idealNorm K I ^ (-σ)) :=
      habs.tsum_le_tsum (norm_idealLogTerm_tail_bound K a ha k hs) hmajor
    _ = _ := by rw [tsum_mul_left]; rfl

theorem norm_heckeLSeries_sub_one_le (χ : HeckeCharacter K)
    {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖heckeLSeries K χ s - 1‖ ≤
      (2 : ℝ) ^ (-(s.re - σ)) * idealLogTailMajorant K 0 σ := by
  have h := norm_idealLogSeries_sub_unit_le K (heckeIdealCoefficient K χ)
    (norm_heckeIdealCoefficient_le_one K χ) 0 hσ hs
  have hone : heckeIdealCoefficient K χ 1 = 1 := by
    simpa only [heckeIdealCoefficient, HeckeGeneral.Arithmetic.nonzeroIdealCoefficient,
      Submonoid.coe_one] using HeckeGeneral.Arithmetic.idealCoefficient_one (primeCoefficient K χ)
  simpa [hone, heckeLSeries] using h

theorem norm_iteratedDeriv_heckeLSeries_le (χ : HeckeCharacter K) (k : ℕ)
    {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖iteratedDeriv (k + 1) (heckeLSeries K χ) s‖ ≤
      (2 : ℝ) ^ (-(s.re - σ)) * idealLogTailMajorant K (k + 1) σ := by
  rw [iteratedDeriv_heckeLSeries K χ (k + 1) (lt_of_lt_of_le hσ hs)]
  have h := norm_idealLogSeries_sub_unit_le K (heckeIdealCoefficient K χ)
    (norm_heckeIdealCoefficient_le_one K χ) (k + 1) hσ hs
  simpa [heckeDerivativeSeries] using h

/-- The convergence to one is uniform with respect to arbitrary imaginary directions. -/
theorem tendsto_heckeLSeries_of_re_atTop {α : Type*} {l : Filter α}
    (χ : HeckeCharacter K) (z : α → ℂ)
    (hz : Tendsto (fun u => (z u).re) l atTop) :
    Tendsto (fun u => heckeLSeries K χ (z u)) l (𝓝 1) := by
  have hdecay : Tendsto (fun u => (2 : ℝ) ^ (-((z u).re - 2))) l (𝓝 0) :=
    (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp
      (tendsto_neg_atTop_atBot.comp (by
        simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-2 : ℝ) hz))
  have hbound : Tendsto (fun u => (2 : ℝ) ^ (-((z u).re - 2)) *
      idealLogTailMajorant K 0 2) l (𝓝 0) := by
    simpa only [zero_mul] using hdecay.mul_const (idealLogTailMajorant K 0 2)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hbound.eventually (gt_mem_nhds hε), hz.eventually (eventually_ge_atTop 2)]
    with u hu hzu
  rw [dist_eq_norm]
  exact (norm_heckeLSeries_sub_one_le K χ (by norm_num : (1 : ℝ) < 2) hzu).trans_lt hu

/-- Every positive-order derivative tends to zero as the real part tends to infinity. -/
theorem tendsto_iteratedDeriv_heckeLSeries_of_re_atTop {α : Type*} {l : Filter α}
    (χ : HeckeCharacter K) (k : ℕ) (z : α → ℂ)
    (hz : Tendsto (fun u => (z u).re) l atTop) :
    Tendsto (fun u => iteratedDeriv (k + 1) (heckeLSeries K χ) (z u)) l (𝓝 0) := by
  have hdecay : Tendsto (fun u => (2 : ℝ) ^ (-((z u).re - 2))) l (𝓝 0) :=
    (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp
      (tendsto_neg_atTop_atBot.comp (by
        simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-2 : ℝ) hz))
  have hbound : Tendsto (fun u => (2 : ℝ) ^ (-((z u).re - 2)) *
      idealLogTailMajorant K (k + 1) 2) l (𝓝 0) := by
    simpa only [zero_mul] using hdecay.mul_const (idealLogTailMajorant K (k + 1) 2)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hbound.eventually (gt_mem_nhds hε), hz.eventually (eventually_ge_atTop 2)]
    with u hu hzu
  rw [dist_zero_right]
  exact (norm_iteratedDeriv_heckeLSeries_le K χ k (by norm_num : (1 : ℝ) < 2) hzu).trans_lt hu

end HeckeGeneral.Analysis
