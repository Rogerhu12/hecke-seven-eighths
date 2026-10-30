/-
Copyright (c) 2026 OpenAI. Released under the Apache 2.0 license.

Adapted from the generic parts of OpenAI/math fd4aeeb2:
lean/OAI/NumberTheory/DirichletL/Mellin/InverseContour.lean and
lean/OAI/NumberTheory/DirichletL/Mellin/UniformKernelBounds.lean.
All arithmetic imports have been removed. The continuous-linear-map
seminorm bound is proved directly from mathlib, and the final normalized
log-window family is new.
-/
import PrimeCancellationLogProfile
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Tactic.Choose
import Mathlib.Tactic.GCongr

set_option autoImplicit false
noncomputable section

namespace PrimeCancellation.SchwartzControl

open scoped Classical FourierTransform SchwartzMap ContDiff Topology BigOperators
open MeasureTheory Filter Set
open PrimeCancellationCompactFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def logRadius (a b : ℝ) : ℝ := |Real.log a| + |Real.log b| + 1

theorem logRadius_pos (a b : ℝ) : 0 < logRadius a b := by unfold logRadius; positivity

def logCutoff (a b : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := logRadius a b
  rOut := logRadius a b + 1
  rIn_pos := logRadius_pos a b
  rIn_lt_rOut := by linarith

def logOuterCutoff (a b : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := logRadius a b + 1
  rOut := logRadius a b + 2
  rIn_pos := by have := logRadius_pos a b; linarith
  rIn_lt_rOut := by linarith

def expCorrection (a b u : ℝ) : ℝ := logOuterCutoff a b u * (Real.exp u - u)
def patchedExp (a b u : ℝ) : ℝ := u + expCorrection a b u

theorem expCorrection_compact (a b : ℝ) : HasCompactSupport (expCorrection a b) :=
  (logOuterCutoff a b).hasCompactSupport.mul_right

theorem expCorrection_smooth (a b : ℝ) : ContDiff ℝ ∞ (expCorrection a b) :=
  (logOuterCutoff a b).contDiff.mul (Real.contDiff_exp.sub contDiff_id)

theorem patchedExp_temperate (a b : ℝ) : Function.HasTemperateGrowth (patchedExp a b) :=
  Function.HasTemperateGrowth.id'.add ((expCorrection_compact a b).hasTemperateGrowth
    (expCorrection_smooth a b))

theorem patchedExp_proper (a b : ℝ) :
    ∃ (k : ℕ) (C : ℝ), ∀ u : ℝ, ‖u‖ ≤ C * (1 + ‖patchedExp a b u‖) ^ k := by
  obtain ⟨u₀, hu₀⟩ := (expCorrection_smooth a b).continuous.norm.exists_forall_ge_of_hasCompactSupport
    (expCorrection_compact a b).norm
  refine ⟨1, ‖expCorrection a b u₀‖ + 1, ?_⟩
  intro u
  have htriangle : ‖u‖ ≤ ‖patchedExp a b u‖ + ‖expCorrection a b u‖ := by
    simpa only [patchedExp, add_sub_cancel_right] using
      norm_sub_le (patchedExp a b u) (expCorrection a b u)
  have hbound := hu₀ u
  simp only [pow_one]
  nlinarith [norm_nonneg (patchedExp a b u), norm_nonneg (expCorrection a b u₀)]

def logPullbackCLM (a b : ℝ) : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (logCutoff a b)).comp
    (SchwartzMap.compCLM ℝ (patchedExp_temperate a b) (patchedExp_proper a b))

theorem logPullbackCLM_apply (a b : ℝ) (W : SchwartzMap ℝ ℂ) (u : ℝ) :
    logPullbackCLM a b W u = logCutoff a b u • W (patchedExp a b u) := by
  rw [logPullbackCLM, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply
    ((logCutoff a b).hasCompactSupport.hasTemperateGrowth (logCutoff a b).contDiff)]
  rfl

theorem logCutoff_eq_one_of_source (a b : ℝ) (ha : 0 < a) (u : ℝ)
    (hu : Real.exp u ∈ Set.Icc a b) : logCutoff a b u = 1 := by
  apply (logCutoff a b).one_of_mem_closedBall
  have hl := Real.log_le_log ha hu.1
  have hr := Real.log_le_log (Real.exp_pos u) hu.2
  simp only [Real.log_exp] at hl hr
  change dist u 0 ≤ logRadius a b
  rw [Real.dist_eq, sub_zero]
  apply abs_le.mpr
  constructor <;> dsimp [logRadius] <;>
    linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b), abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem patchedExp_eq_exp_of_cutoff_ne_zero (a b u : ℝ) (hu : logCutoff a b u ≠ 0) :
    patchedExp a b u = Real.exp u := by
  have hmem : u ∈ Function.support (logCutoff a b) := hu
  rw [(logCutoff a b).support_eq] at hmem
  have heta : logOuterCutoff a b u = 1 := by
    apply (logOuterCutoff a b).one_of_mem_closedBall
    change dist u 0 ≤ logRadius a b + 1
    change dist u 0 < logRadius a b + 1 at hmem
    exact le_of_lt hmem
  simp [patchedExp, expCorrection, heta]

theorem logPullbackCLM_eq_actual (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (u : ℝ) :
    logPullbackCLM a b W u = W (Real.exp u) := by
  rw [logPullbackCLM_apply]
  by_cases hW : W (Real.exp u) = 0
  · by_cases hcut : logCutoff a b u = 0
    · simp [hcut, hW]
    · rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u hcut, hW, smul_zero]
  · have hcut := logCutoff_eq_one_of_source a b ha u (hsupp hW)
    rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u (by rw [hcut]; norm_num), hcut, one_smul]


theorem compact_family_deriv_sup_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ u : ℝ, ‖iteratedFDeriv ℝ j (F σ) u‖ ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro σ hσ u
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hu : u ∈ K
  · exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans
      (by linarith [le_abs_self M])
  · have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
      (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
        (closure_minimal (hsupp σ) hK.isClosed))
    have hz : iteratedDeriv j (F σ) u = 0 := by by_contra hn; exact hu (hs hn)
    simp only [hz, norm_zero]
    positivity

theorem compact_family_mul_deriv_L1_source_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J,
      (∫ u : ℝ, ‖iteratedDeriv j (fun u => F σ u * W u) u‖) ≤
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  choose c hc hcb using fun i : Fin (j + 1) => compact_family_deriv_sup_bound F hF K hK hsupp J hJ i.val
  let D := (∑ i : Fin (j + 1), c i) + 1
  have hD : 0 < D := by
    have : 0 ≤ ∑ i : Fin (j + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp [D]
    linarith
  have hder (i : ℕ) (hi : i ≤ j) (σ : E) (hσ : σ ∈ J) (u : ℝ) :
      ‖iteratedFDeriv ℝ i (F σ) u‖ ≤ D := by
    let k : Fin (j + 1) := ⟨i, by omega⟩
    have hsum : c k ≤ ∑ l : Fin (j + 1), c l :=
      Finset.single_le_sum (fun l _ => (hc l).le) (Finset.mem_univ k)
    exact (hcb k σ hσ u).trans (by dsimp [D]; linarith)
  let B : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(B + 1) * (volume.real K + 1), by positivity, ?_⟩
  intro W σ hσ
  let S : ℝ := (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hWder (k : ℕ) (hk : k ≤ j) (u : ℝ) : ‖iteratedFDeriv ℝ k W u‖ ≤ S := by
    have hle : schwartzSeminormFamily ℝ ℝ ℂ (0, k) ≤
        (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [hk])
    exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ W k u).trans (Seminorm.le_def.mp hle W)
  have hb (u : ℝ) : ‖iteratedDeriv j (fun u => F σ u * W u) u‖ ≤ (B + 1) * S := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hfσ : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
    apply (norm_iteratedFDeriv_mul_le hfσ (W.smooth ⊤) u (n := j) (by simp)).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D * S := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hder i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) σ hσ u) (by positivity))
          (hWder (j - i) (Nat.sub_le _ _) u) (norm_nonneg _) (by positivity)
      _ = B * S := by rw [← Finset.sum_mul]
      _ ≤ (B + 1) * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hmul : Function.support (fun u => F σ u * W u) ⊆ K := by
    intro u hu
    exact hsupp σ (mul_ne_zero_iff.mp hu).1
  have hs : Function.support (iteratedDeriv j (fun u => F σ u * W u)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset _ j).trans
      (closure_minimal hmul hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (fun u => F σ u * W u) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (fun u => F σ u * W u) u = 0 := by by_contra hn; exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume)
    (f := fun u => ‖iteratedDeriv j (fun u => F σ u * W u) u‖) hK.measure_lt_top
    (C := (B + 1) * S) (fun u _ => by simpa using hb u)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  calc
    _ ≤ ((B + 1) * S) * volume.real K := hi
    _ ≤ ((B + 1) * S) * (volume.real K + 1) := by gcongr; linarith
    _ = _ := by dsimp [S]; ring


theorem compact_family_mul_fourier_power_source_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C, hC, hb⟩ := compact_family_mul_deriv_L1_source_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro W σ hσ w
  have hFW : ContDiff ℝ ∞ (Function.uncurry (fun σ u => F σ u * W u)) :=
    hF.mul ((W.smooth ⊤).comp contDiff_snd)
  have hsupport : ∀ σ, Function.support (fun u => F σ u * W u) ⊆ K := by
    intro σ u hu
    exact hsupp σ (mul_ne_zero_iff.mp hu).1
  have hs : ContDiff ℝ ∞ (fun u => F σ u * W u) :=
    hFW.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable (fun σ u => F σ u * W u) hFW K hK hsupport σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) =
      ‖𝓕 (iteratedDeriv j (fun u => F σ u * W u)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (fun u => F σ u * W u)) w‖ ≤
      C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (fun u => F σ u * W u)) w).trans
    exact hb W σ hσ
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) := mul_comm _ _
    _ ≤ _ := hn

theorem compact_family_mul_fourier_weighted_source_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_mul_fourier_power_source_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_mul_fourier_power_source_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro W σ hσ w
  let S := (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hsubset : Finset.Iic (0, 0) ⊆ Finset.Iic (0, j) := by
    intro p hp
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hp).trans (by simp))
  have hseminorm : (Finset.Iic (0, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono hsubset) W
  have hbase : ‖𝓕 (fun u => F σ u * W u) w‖ ≤ C₀ * S := by
    have hh : ‖𝓕 (fun u => F σ u * W u) w‖ ≤ C₀ * (Finset.Iic (0, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
      simpa using h0 W σ hσ w
    exact hh.trans (mul_le_mul_of_nonneg_left hseminorm hC₀.le)
  have hpower : |w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤ Cj * S := hj W σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * (C₀ * S) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ 2 ^ j * ((C₀ + Cj) * S) := by gcongr; linarith
      _ = _ := by dsimp [S]; ring
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * (Cj * S) := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ 2 ^ j * ((C₀ + Cj) * S) := by gcongr; linarith
      _ = _ := by dsimp [S]; ring


def negativeLogPullbackCLM (a b : ℝ) : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv).comp (logPullbackCLM a b)

theorem negativeLogPullbackCLM_eq_actual (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (u : ℝ) :
    negativeLogPullbackCLM a b W u = W (Real.exp (-u)) := by
  change logPullbackCLM a b W (-u) = _
  exact logPullbackCLM_eq_actual a b ha W hsupp (-u)

def logWeight (a b σ u : ℝ) : ℂ := (Real.exp (-σ * u) * logCutoff a b (-u) : ℝ)

theorem logWeight_smooth (a b : ℝ) : ContDiff ℝ ∞ (Function.uncurry (logWeight a b)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((Real.exp (-p.1 * p.2) * logCutoff a b (-p.2) : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp
    ((Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).mul
      ((logCutoff a b).contDiff.comp contDiff_snd.neg))

theorem logWeight_support (a b σ : ℝ) :
    Function.support (logWeight a b σ) ⊆ Metric.closedBall 0 (logRadius a b + 1) := by
  intro u hu
  have hc : logCutoff a b (-u) ≠ 0 := by
    intro hc
    exact hu (by simp [logWeight, hc])
  have hm : -u ∈ Function.support (logCutoff a b) := hc
  rw [(logCutoff a b).support_eq] at hm
  change dist (-u) 0 < logRadius a b + 1 at hm
  change dist u 0 ≤ logRadius a b + 1
  simpa only [dist_zero_right, norm_neg] using hm.le

theorem logWeight_mul_pullback (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (σ u : ℝ) :
    logWeight a b σ u * negativeLogPullbackCLM a b W u = mellinLogFamily W σ u := by
  rw [negativeLogPullbackCLM_eq_actual a b ha W hsupp]
  by_cases hW : W (Real.exp (-u)) = 0
  · simp [logWeight, mellinLogFamily, hW]
  · have hc := logCutoff_eq_one_of_source a b ha (-u) (hsupp hW)
    simp [logWeight, mellinLogFamily, hc]

/-- Continuity of a linear map between Schwartz spaces gives control by
finitely many source seminorms. This is an application of mathlib's general
locally convex bound, with no arithmetic input. -/
theorem schwartzCLM_finite_seminorm_control
    (T : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ) (s : Finset (ℕ × ℕ)) :
    ∃ (q : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ,
        s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (T W) ≤
          C * q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let p : Seminorm ℝ (SchwartzMap ℝ ℂ) :=
    (s.sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp T.toLinearMap
  have hs : Continuous (⇑(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) :
      Seminorm ℝ (SchwartzMap ℝ ℂ))) :=
    Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)
  have hp : Continuous p := hs.comp T.continuous
  obtain ⟨q, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) p hp
  have hCpos : 0 < (C : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  refine ⟨q, C, hCpos, ?_⟩
  intro W
  have h := Seminorm.le_def.mp hbound W
  simpa only [p, Seminorm.comp_apply, smul_apply, NNReal.smul_def, smul_eq_mul,
    ContinuousLinearMap.coe_coe] using h

/-- A smooth compactly supported multiplier in logarithmic coordinates.
Its parameters A and σ will range over a fixed compact rectangle. -/
def normalizedLogWeight (a b : ℝ) (p : ℝ × ℝ) (u : ℝ) : ℂ :=
  logWeight a b p.2 u * (p.1 : ℂ) *
    PrimeCancellationLogProfile.safeInverse (1 - p.1 * u)

theorem normalizedLogWeight_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (normalizedLogWeight a b)) := by
  change ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ =>
    logWeight a b p.1.2 p.2 * (p.1.1 : ℂ) *
      PrimeCancellationLogProfile.safeInverse (1 - p.1.1 * p.2))
  exact (((logWeight_smooth a b).comp (contDiff_fst.snd.prodMk contDiff_snd)).mul
    (Complex.ofRealCLM.contDiff.comp contDiff_fst.fst)).mul
    (PrimeCancellationLogProfile.safeInverse_smooth.comp
      (contDiff_const.sub (contDiff_fst.fst.mul contDiff_snd)))

theorem normalizedLogWeight_support (a b : ℝ) (p : ℝ × ℝ) :
    Function.support (normalizedLogWeight a b p) ⊆
      Metric.closedBall 0 (logRadius a b + 1) := by
  intro u hu
  exact logWeight_support a b p.2 ((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hu).1).1)

theorem normalizedLogWeight_mul_pullback (a b : ℝ) (ha : 0 < a)
    (W : SchwartzMap ℝ ℂ) (hsupp : Function.support (W : ℝ → ℂ) ⊆ Icc a b)
    (A σ u : ℝ) :
    normalizedLogWeight a b (A, σ) u * negativeLogPullbackCLM a b W u =
      mellinLogFamily (PrimeCancellationLogProfile.profile W A) σ u := by
  calc
    _ = (logWeight a b σ u * negativeLogPullbackCLM a b W u) * (A : ℂ) *
        PrimeCancellationLogProfile.safeInverse (1 - A * u) := by
      unfold normalizedLogWeight
      ring
    _ = mellinLogFamily W σ u * (A : ℂ) *
        PrimeCancellationLogProfile.safeInverse (1 - A * u) := by
      rw [logWeight_mul_pullback a b ha W hsupp]
    _ = PrimeCancellationLogProfile.logFamily W (A, σ) u := by
      simp only [mellinLogFamily, PrimeCancellationLogProfile.logFamily]
      rw [smul_mul_assoc, smul_mul_assoc]
    _ = _ := PrimeCancellationLogProfile.logFamily_eq W A σ u

/-- A fixed finite family of standard Schwartz seminorms controls all
normalized profiles simultaneously for A in [0,1] and σ in a compact strip. -/
theorem uniform_profile_mellin_source_bound (a b : ℝ) (ha : 0 < a)
    (lo hi : ℝ) (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Icc a b →
      ∀ A ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
        (1 + |t|) ^ j *
          ‖mellin (PrimeCancellationLogProfile.profile W A) ((σ : ℂ) + t * Complex.I)‖ ≤
            C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C, hC, hb⟩ := compact_family_mul_fourier_weighted_source_bound
    (normalizedLogWeight a b) (normalizedLogWeight_smooth a b)
    (Metric.closedBall 0 (logRadius a b + 1)) (isCompact_closedBall _ _)
    (normalizedLogWeight_support a b) (Icc (0 : ℝ) 1 ×ˢ Icc lo hi)
    (isCompact_Icc.prod isCompact_Icc) j
  obtain ⟨s, D, hD, hDbd⟩ :=
    schwartzCLM_finite_seminorm_control (negativeLogPullbackCLM a b) (Finset.Iic (0, j))
  refine ⟨s, (1 + 2 * Real.pi) ^ j * C * D, by positivity, ?_⟩
  intro W hsupp A hA σ hσ t
  have hfun : (fun u => normalizedLogWeight a b (A, σ) u * negativeLogPullbackCLM a b W u) =
      mellinLogFamily (PrimeCancellationLogProfile.profile W A) σ :=
    funext (normalizedLogWeight_mul_pullback a b ha W hsupp A σ)
  have hfour := hb (negativeLogPullbackCLM a b W) (A, σ) ⟨hA, hσ⟩ (t / (2 * Real.pi))
  rw [hfun] at hfour
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  rw [mellin_eq_logFamily_fourier]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily (PrimeCancellationLogProfile.profile W A) σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily (PrimeCancellationLogProfile.profile W A) σ) (t / (2 * Real.pi))‖) := by
      rw [mul_pow, mul_assoc]
    _ ≤ (1 + 2 * Real.pi) ^ j *
        (C * (D * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)) :=
      mul_le_mul_of_nonneg_left
        (hfour.trans (mul_le_mul_of_nonneg_left (hDbd W) hC.le)) (by positivity)
    _ = _ := by ring

/-- The exact divided windows W(x)/log(Px) admit a cubic Mellin bound
controlled by one fixed finite family of standard Schwartz seminorms of W.
The finite family and constant are chosen before W, P, σ, and t. -/
theorem uniform_logWindow_mellin_source_bound :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Icc (1 : ℝ) 2 →
      ∀ P : ℝ, Real.exp 4 ≤ P → ∀ σ ∈ Icc (1 / 2 : ℝ) 2, ∀ t : ℝ,
        ‖mellin (PrimeCancellationLogWindow.logWindow P W)
          ((σ : ℂ) + t * Complex.I)‖ ≤
            (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + |t|) ^ 3 := by
  obtain ⟨s, C, hC, hb⟩ := uniform_profile_mellin_source_bound 1 2 (by norm_num)
    (1 / 2) 2 3
  refine ⟨s, C, hC, ?_⟩
  intro W hsupp P hP σ hσ t
  have hPpos : 0 < P := (Real.exp_pos 4).trans_le hP
  have hlog : 4 ≤ Real.log P := by
    have h := Real.log_le_log (Real.exp_pos 4) hP
    simpa only [Real.log_exp] using h
  have hlogpos : 0 < Real.log P := by linarith
  have hA : (1 / Real.log P : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact (one_div_pos.mpr hlogpos).le
    · exact (div_le_one₀ hlogpos).mpr (by linarith)
  have hlog2nonneg : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlarge : 2 * (|Real.log (1 : ℝ)| + |Real.log (2 : ℝ)|) + 1 ≤ Real.log P := by
    rw [Real.log_one, abs_zero, zero_add, abs_of_nonneg hlog2nonneg]
    linarith
  have heq : PrimeCancellationLogProfile.profile W (1 / Real.log P) =
      PrimeCancellationLogWindow.logWindow P W := by
    change PrimeCancellationLogProfile.profile W (1 / Real.log P) =
      (fun y => W y / (Real.log (P * y) : ℂ))
    exact PrimeCancellationLogProfile.profile_eq_log_division W 1 2 P
      (by norm_num) hsupp hPpos hlarge
  have h := hb W hsupp (1 / Real.log P) hA σ hσ t
  rw [heq] at h
  apply (le_div_iff₀ (show 0 < (1 + |t|) ^ 3 by positivity)).mpr
  simpa only [mul_comm] using h

/-- The same fixed finite seminorm family can control the window sup norm
as well as all logarithmically divided Mellin transforms. -/
theorem uniform_window_and_logWindow_source_bound :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ (0, 0) ∈ s ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Icc (1 : ℝ) 2 →
        (∀ x : ℝ, ‖W x‖ ≤ s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ∧
        (∀ P : ℝ, Real.exp 4 ≤ P → ∀ σ ∈ Icc (1 / 2 : ℝ) 2, ∀ t : ℝ,
          ‖mellin (PrimeCancellationLogWindow.logWindow P W)
            ((σ : ℂ) + t * Complex.I)‖ ≤
              (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + |t|) ^ 3) := by
  obtain ⟨s, C, hC, hb⟩ := uniform_logWindow_mellin_source_bound
  let q := insert (0, 0) s
  have hs : s ⊆ q := Finset.subset_insert _ _
  have hzero : (0, 0) ∈ q := Finset.mem_insert_self _ _
  refine ⟨q, C, hC, hzero, ?_⟩
  intro W hW
  constructor
  · intro x
    have hle : schwartzSeminormFamily ℝ ℝ ℂ (0, 0) ≤
        q.sup (schwartzSeminormFamily ℝ ℝ ℂ) := Finset.le_sup hzero
    exact (SchwartzMap.norm_le_seminorm ℝ W x).trans (Seminorm.le_def.mp hle W)
  · intro P hP σ hσ t
    refine (hb W hW P hP σ hσ t).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (Seminorm.le_def.mp (Finset.sup_mono hs) W) hC.le

#print axioms logRadius_pos
#print axioms expCorrection_compact
#print axioms expCorrection_smooth
#print axioms patchedExp_temperate
#print axioms patchedExp_proper
#print axioms logPullbackCLM_apply
#print axioms logCutoff_eq_one_of_source
#print axioms patchedExp_eq_exp_of_cutoff_ne_zero
#print axioms logPullbackCLM_eq_actual
#print axioms compact_family_deriv_sup_bound
#print axioms compact_family_mul_deriv_L1_source_bound
#print axioms compact_family_mul_fourier_power_source_bound
#print axioms compact_family_mul_fourier_weighted_source_bound
#print axioms negativeLogPullbackCLM_eq_actual
#print axioms logWeight_smooth
#print axioms logWeight_support
#print axioms logWeight_mul_pullback
#print axioms schwartzCLM_finite_seminorm_control
#print axioms normalizedLogWeight_smooth
#print axioms normalizedLogWeight_support
#print axioms normalizedLogWeight_mul_pullback
#print axioms uniform_profile_mellin_source_bound
#print axioms uniform_logWindow_mellin_source_bound
#print axioms uniform_window_and_logWindow_source_bound

end PrimeCancellation.SchwartzControl

