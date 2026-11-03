/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The weighted Fubini and inversion proofs adapt the generic part of
openai/math, commit fd4aeeb2,
OAI/NumberTheory/DirichletL/Eisenstein/SourceMellinInversion.lean.
No OAI or number-field project module is imported.
-/
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Compactly supported Mellin inversion for weighted Dirichlet series

This file proves convergence, holomorphy, vertical integrability, and weighted
Mellin inversion from smoothness and support in a positive compact interval.
The index type is arbitrary and countable.  In particular, the proofs are
independent of any unconstructed `MomentData` or Hecke-character model.
-/

noncomputable section

open Filter Asymptotics MeasureTheory Set Complex
open scoped Topology BigOperators ContDiff FourierTransform SchwartzMap

namespace PrimeCancellation.Mellin

/-- A positive compact support gives arbitrary power decay at both endpoints. -/
theorem compact_endpoint_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (p q : ℝ) :
    V =O[atTop] (fun x : ℝ => x ^ (-p)) ∧
      V =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-q)) := by
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (b + 1)] with x hx
    by_contra hV
    have hxb := (hsupp hV).2
    linarith
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with x hx
    by_contra hV
    have hxa := (hsupp hV).1
    linarith [hx.2]
  exact ⟨htopzero.isBigO.trans (isBigO_zero _ _),
    hbotzero.isBigO.trans (isBigO_zero _ _)⟩

theorem compact_mellin_convergent (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (hV : Continuous V) (s : ℂ) :
    MellinConvergent V s := by
  have hd := compact_endpoint_decay V a b ha hsupp (s.re + 1) (s.re - 1)
  exact mellinConvergent_of_isBigO_rpow
    (hV.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    hd.1 (by linarith) hd.2 (by linarith)

theorem compact_mellin_differentiable (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (hV : Continuous V) :
    Differentiable ℂ (mellin V) := by
  intro s
  have hd := compact_endpoint_decay V a b ha hsupp (s.re + 1) (s.re - 1)
  exact mellin_differentiableAt_of_isBigO_rpow
    (hV.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    hd.1 (by linarith) hd.2 (by linarith)

/-- The logarithmic coordinate used by Mathlib's Fourier/Mellin identity. -/
def logProfile (V : ℝ → ℂ) (σ : ℝ) (u : ℝ) : ℂ :=
  Real.exp (-σ * u) • V (Real.exp (-u))

theorem logProfile_support (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (σ : ℝ) :
    Function.support (logProfile V σ) ⊆ Icc (-Real.log b) (-Real.log a) := by
  intro u hu
  have hVu : V (Real.exp (-u)) ≠ 0 := by
    intro h
    exact hu (by simp [logProfile, h])
  have hx := hsupp hVu
  have hl := Real.log_le_log ha hx.1
  have hr := Real.log_le_log (Real.exp_pos (-u)) hx.2
  rw [Real.log_exp] at hl hr
  constructor <;> linarith

theorem logProfile_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (σ : ℝ) :
    ContDiff ℝ ∞ (logProfile V σ) := by
  unfold logProfile
  exact (by fun_prop : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-σ * u))).smul
    (hV.comp (by fun_prop))

theorem mellin_eq_logProfile_fourier (V : ℝ → ℂ) (σ t : ℝ) :
    mellin V ((σ : ℂ) + t * I) =
      𝓕 (logProfile V σ) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * I).im = t := by simp
  rw [hre, him]
  rfl

theorem compact_mellin_vertical_integrable (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin V) σ := by
  have hc : HasCompactSupport (logProfile V σ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (logProfile_support V a b ha hsupp σ)
  let f : 𝓢(ℝ, ℂ) := hc.toSchwartzMap (logProfile_smooth V hV σ)
  have hf : Integrable (fun t : ℝ => (𝓕 f) (t / (2 * Real.pi))) := by
    simpa only [div_eq_mul_inv] using
      (𝓕 f).integrable.comp_mul_right'
        (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  change Integrable (fun t : ℝ => mellin V ((σ : ℂ) + t * I))
  have hfcoe : (f : ℝ → ℂ) = logProfile V σ := rfl
  simpa only [mellin_eq_logProfile_fourier, SchwartzMap.fourier_coe, hfcoe] using hf

theorem compact_mellin_inversion (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (σ x : ℝ) (hx : 0 < x) :
    V x = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ (-((σ : ℂ) + t * I)) * mellin V ((σ : ℂ) + t * I) := by
  have hm := mellinInv_mellin_eq σ V hx
    (compact_mellin_convergent V a b ha hsupp hV.continuous σ)
    (compact_mellin_vertical_integrable V a b ha hsupp hV σ)
    hV.continuous.continuousAt
  simpa only [mellinInv, smul_eq_mul, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat] using hm.symm

theorem positive_cpow_vertical_norm (r σ t : ℝ) (hr : 0 < r) :
    ‖(r : ℂ) ^ ((σ : ℂ) + t * I)‖ = r ^ σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

theorem positive_cpow_negative_vertical_norm (r σ t : ℝ) (hr : 0 < r) :
    ‖(r : ℂ) ^ (-((σ : ℂ) + t * I))‖ = r ^ (-σ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

theorem positive_cpow_vertical_continuous (r σ : ℝ) (hr : 0 < r) :
    Continuous (fun t : ℝ => (r : ℂ) ^ ((σ : ℂ) + t * I)) := by
  let : NeZero (r : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r : ℂ)).comp (by fun_prop)

theorem positive_cpow_negative_vertical_continuous (r σ : ℝ) (hr : 0 < r) :
    Continuous (fun t : ℝ => (r : ℂ) ^ (-((σ : ℂ) + t * I))) := by
  let : NeZero (r : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r : ℂ)).comp (by fun_prop)

theorem vertical_power_mul_integrable (M : ℝ → ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0 < r) :
    Integrable (fun t : ℝ => (r : ℂ) ^ ((σ : ℂ) + t * I) * M t) := by
  apply (hM.norm.const_mul (r ^ σ)).mono'
    ((positive_cpow_vertical_continuous r σ hr).aestronglyMeasurable.mul
      hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t => by
    simp only [Pi.mul_apply, norm_mul, positive_cpow_vertical_norm r σ t hr, le_refl])

theorem weighted_vertical_power_integrable (M : ℝ → ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0 < r) (c : ℂ) :
    Integrable (fun t : ℝ => c * (r : ℂ) ^ (-((σ : ℂ) + t * I)) * M t) := by
  apply (hM.norm.const_mul (‖c‖ * r ^ (-σ))).mono'
    ((continuous_const.mul (positive_cpow_negative_vertical_continuous r σ hr)).aestronglyMeasurable.mul
      hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t => by
    simp only [Pi.mul_apply, norm_mul, positive_cpow_negative_vertical_norm r σ t hr,
      le_refl])

theorem weighted_vertical_power_integral_norm (M : ℝ → ℂ)
    (r σ : ℝ) (hr : 0 < r) (c : ℂ) :
    (∫ t : ℝ, ‖c * (r : ℂ) ^ (-((σ : ℂ) + t * I)) * M t‖) =
      (‖c‖ * r ^ (-σ)) * (∫ t : ℝ, ‖M t‖) := by
  simp only [norm_mul, positive_cpow_negative_vertical_norm r σ _ hr, integral_const_mul]

theorem weighted_vertical_sum_integral {α : Type*} [Countable α]
    (r : α → ℝ) (hr : ∀ i, 0 < r i) (c : α → ℂ) (σ : ℝ)
    (hc : Summable (fun i => ‖c i‖ * (r i) ^ (-σ)))
    (M : ℝ → ℂ) (hM : Integrable M) :
    (∑' i, ∫ t : ℝ, c i * (r i : ℂ) ^ (-((σ : ℂ) + t * I)) * M t) =
      ∫ t : ℝ, (∑' i, c i * (r i : ℂ) ^ (-((σ : ℂ) + t * I))) * M t := by
  have hi (i : α) := weighted_vertical_power_integrable M hM (r i) σ (hr i) (c i)
  have hs : Summable
      (fun i => ∫ t : ℝ, ‖c i * (r i : ℂ) ^ (-((σ : ℂ) + t * I)) * M t‖) := by
    simp only [weighted_vertical_power_integral_norm M _ σ (hr _) _]
    exact hc.mul_right _
  rw [integral_tsum_of_summable_integral_norm hi hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => tsum_mul_right)

theorem positive_quotient_cpow_neg (r X : ℝ) (hr : 0 < r) (hX : 0 < X) (s : ℂ) :
    ((r / X : ℝ) : ℂ) ^ (-s) = (r : ℂ) ^ (-s) * (X : ℂ) ^ s := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hr.le hX.le,
    Complex.cpow_neg, Complex.cpow_neg, div_inv_eq_mul]

/-- Absolute Dirichlet convergence suffices to interchange Mellin inversion and
the countable sum.  No prime-sum estimate is an input. -/
theorem weighted_mellin_inversion {α : Type*} [Countable α]
    (r : α → ℝ) (hr : ∀ i, 0 < r i) (c : α → ℂ) (σ : ℝ)
    (hc : Summable (fun i => ‖c i‖ * (r i) ^ (-σ)))
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (∑' i, c i * V (r i / X)) = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      mellin V ((σ : ℂ) + t * I) * (X : ℂ) ^ ((σ : ℂ) + t * I) *
        (∑' i, c i * (r i : ℂ) ^ (-((σ : ℂ) + t * I))) := by
  let M : ℝ → ℂ := fun t =>
    (X : ℂ) ^ ((σ : ℂ) + t * I) * mellin V ((σ : ℂ) + t * I)
  have hM : Integrable M := vertical_power_mul_integrable _
    (compact_mellin_vertical_integrable V a b ha hsupp hV σ) X σ hX
  have hi (i : α) : c i * V (r i / X) = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, c i * (r i : ℂ) ^ (-((σ : ℂ) + t * I)) * M t := by
    rw [compact_mellin_inversion V a b ha hsupp hV σ _ (div_pos (hr i) hX)]
    rw [← mul_assoc, mul_comm (c i), mul_assoc, ← integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by
      dsimp only
      rw [positive_quotient_cpow_neg _ _ (hr i) hX]
      dsimp only [M]
      ring)
  simp_rw [hi]
  rw [tsum_mul_left, weighted_vertical_sum_integral r hr c σ hc M hM]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by dsimp only [M]; ring)

end PrimeCancellation.Mellin

#print axioms PrimeCancellation.Mellin.compact_endpoint_decay
#print axioms PrimeCancellation.Mellin.compact_mellin_convergent
#print axioms PrimeCancellation.Mellin.compact_mellin_differentiable
#print axioms PrimeCancellation.Mellin.logProfile_support
#print axioms PrimeCancellation.Mellin.logProfile_smooth
#print axioms PrimeCancellation.Mellin.mellin_eq_logProfile_fourier
#print axioms PrimeCancellation.Mellin.compact_mellin_vertical_integrable
#print axioms PrimeCancellation.Mellin.compact_mellin_inversion
#print axioms PrimeCancellation.Mellin.positive_cpow_vertical_norm
#print axioms PrimeCancellation.Mellin.positive_cpow_negative_vertical_norm
#print axioms PrimeCancellation.Mellin.positive_cpow_vertical_continuous
#print axioms PrimeCancellation.Mellin.positive_cpow_negative_vertical_continuous
#print axioms PrimeCancellation.Mellin.vertical_power_mul_integrable
#print axioms PrimeCancellation.Mellin.weighted_vertical_power_integrable
#print axioms PrimeCancellation.Mellin.weighted_vertical_power_integral_norm
#print axioms PrimeCancellation.Mellin.weighted_vertical_sum_integral
#print axioms PrimeCancellation.Mellin.positive_quotient_cpow_neg
#print axioms PrimeCancellation.Mellin.weighted_mellin_inversion
