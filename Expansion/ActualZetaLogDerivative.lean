import Expansion.ActualPrimeLogSeries
import HeckeSkeleton.ExpansionModels.SmallRowNormReciprocal
import DedekindZetaZeroFree.Main
import PrimeCancellationDiskGeometry

/-!
# Actual zeta logarithmic derivative for the normalizer window

The previously proved Dedekind zero-free theorem is identified with the
literal Hecke continuation by holomorphic uniqueness off its pole. The pole
is removed using the actual entire norm numerator. Its regularization by s
has a bounded Euler logarithm on the initial line, so the proved disk estimate
supplies polynomial control on a fixed strip. No prime-window estimate is an
input to any declaration here.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain Set Filter Metric
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.Expansion.SmallRows
open PrimeCancellationDiskGeometry
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]

theorem heckeContinuation_trivial_eq_normNumerator :
    heckeContinuation K 1 = fun s => normPoleNumerator K 0 s / (s - 1) := by
  simpa only [heckeNormTwist, normTwist_zero, heckeNormPole, Complex.ofReal_zero,
    zero_mul, add_zero] using heckeContinuation_normTwist_eq K 0

theorem heckeContinuation_trivial_differentiableOffPole :
    DifferentiableOn ℂ (heckeContinuation K 1) ({1}ᶜ : Set ℂ) := by
  rw [heckeContinuation_trivial_eq_normNumerator]
  apply (normPoleNumerator_differentiable K 0).differentiableOn.div
    (differentiable_id.sub_const 1).differentiableOn
  intro s hs
  exact sub_ne_zero.mpr hs

/-- The fixed zero-free region is transferred to the actual chosen function. -/
theorem actualZeta_ne_zero {s : ℂ} (hs : 31 / 32 < s.re) (hs1 : s ≠ 1) :
    heckeContinuation K 1 s ≠ 0 := by
  obtain ⟨f, hf, hright, hzero⟩ := DedekindZetaZeroFree.dedekindZeta_ne_zero K
  have heq := DedekindZetaZeroFree.continuation_unique_off_one
    (heckeContinuation K 1) f (heckeContinuation_trivial_differentiableOffPole K) hf
    (fun z hz => by
      rw [heckeContinuation_eq_series K 1 hz, heckeLSeries_trivial_eq_dedekindZeta K hz,
        hright z hz])
  rw [heq hs1]
  exact hzero s hs hs1

/-- The pole-cleared numerator has no exceptional zero at the pole. -/
theorem actualZetaNumerator_ne_zero {s : ℂ} (hs : 31 / 32 < s.re) :
    normPoleNumerator K 0 s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    simpa only [heckeNormPole, Complex.ofReal_zero, zero_mul, add_zero] using
      normPoleNumerator_at_pole K 0
  · intro hzero
    have h := actualZeta_ne_zero K hs hs1
    rw [heckeContinuation_trivial_eq_normNumerator] at h
    change normPoleNumerator K 0 s / (s - 1) ≠ 0 at h
    exact h (by rw [hzero, zero_div])

theorem actualZetaLog_differentiableOn :
    DifferentiableOn ℂ (actualPrimeLogFunction K 1)
      ({s : ℂ | 31 / 32 < s.re} \ {1}) := by
  intro s hs
  have ha := ((heckeContinuation_trivial_differentiableOffPole K).analyticOnNhd
    isOpen_compl_singleton) s hs.2
  exact (ha.deriv.neg.div ha (actualZeta_ne_zero K hs.1 hs.2)).differentiableAt.differentiableWithinAt

/-- Explicit cancellation of the simple pole of the logarithmic derivative. -/
theorem actualZetaLog_eq {s : ℂ} (hs : 31 / 32 < s.re) (hs1 : s ≠ 1) :
    actualPrimeLogFunction K 1 s =
      (s - 1)⁻¹ - deriv (normPoleNumerator K 0) s / normPoleNumerator K 0 s := by
  have hd : HasDerivAt (fun z : ℂ => normPoleNumerator K 0 z / (z - 1))
      ((deriv (normPoleNumerator K 0) s * (s - 1) - normPoleNumerator K 0 s) /
        (s - 1) ^ 2) s := by
    simpa only [id_eq, mul_one] using!
      ((normPoleNumerator_differentiable K 0 s).hasDerivAt.fun_div
        ((hasDerivAt_id s).sub_const 1) (sub_ne_zero.mpr hs1))
  rw [actualPrimeLogFunction, heckeContinuation_trivial_eq_normNumerator, hd.deriv]
  field_simp [actualZetaNumerator_ne_zero K hs, sub_ne_zero.mpr hs1]
  <;> ring

theorem actualZetaLog_residue :
    Tendsto (fun s : ℂ => (s - 1) * actualPrimeLogFunction K 1 s)
      (𝓝[≠] 1) (𝓝 1) := by
  have hQ := (normPoleNumerator_differentiable K 0).analyticAt (1 : ℂ)
  have hQ1 : normPoleNumerator K 0 (1 : ℂ) ≠ 0 :=
    actualZetaNumerator_ne_zero K (by norm_num)
  have hc : ContinuousAt (fun s : ℂ =>
      1 - (s - 1) * (deriv (normPoleNumerator K 0) s / normPoleNumerator K 0 s)) 1 :=
    continuousAt_const.sub ((continuousAt_id.sub continuousAt_const).mul
      (hQ.deriv.continuousAt.div hQ.continuousAt hQ1))
  have hlim : Tendsto (fun s : ℂ =>
      1 - (s - 1) * (deriv (normPoleNumerator K 0) s / normPoleNumerator K 0 s))
      (𝓝[≠] 1) (𝓝 1) := by
    simpa only [sub_self, zero_mul, sub_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  have hstrip : {s : ℂ | 31 / 32 < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hstrip] with s hs1 hs
  rw [actualZetaLog_eq K hs hs1]
  field_simp [sub_ne_zero.mpr hs1]
  <;> ring

theorem actualZetaRegularization_ne_zero {s : ℂ} (hs : 31 / 32 < s.re) :
    normPoleRegularization K 0 s ≠ 0 := by
  apply div_ne_zero (actualZetaNumerator_ne_zero K hs)
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]
  exact Complex.ne_zero_of_re_pos (by linarith)

/-- The logarithmic derivative of Q/s has no pole in the fixed right strip. -/
theorem actualZetaLog_eq_regularized {s : ℂ} (hs : 31 / 32 < s.re) (hs1 : s ≠ 1) :
    actualPrimeLogFunction K 1 s =
      (s - 1)⁻¹ - s⁻¹ -
        deriv (normPoleRegularization K 0) s / normPoleRegularization K 0 s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have heq : normPoleRegularization K 0 = fun z => normPoleNumerator K 0 z / z := by
    funext z
    simp only [normPoleRegularization, Complex.ofReal_zero, zero_mul, sub_zero]
  have hd : HasDerivAt (fun z : ℂ => normPoleNumerator K 0 z / z)
      ((deriv (normPoleNumerator K 0) s * s - normPoleNumerator K 0 s) / s ^ 2) s := by
    simpa only [id_eq, mul_one] using!
      ((normPoleNumerator_differentiable K 0 s).hasDerivAt.fun_div
        (hasDerivAt_id s) hs0)
  rw [actualZetaLog_eq K hs hs1, heq, hd.deriv]
  field_simp [actualZetaNumerator_ne_zero K hs, hs0]
  <;> ring

/-- The field fixes every constant before the later smoothing scale. -/
theorem exists_actualZetaRegularized_logDeriv_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ σ t : ℝ, 63 / 64 ≤ σ → σ ≤ 2 →
      ‖deriv (normPoleRegularization K 0) (verticalPoint σ t) /
          normPoleRegularization K 0 (verticalPoint σ t)‖ ≤ C * (4 + |t|) ^ k := by
  obtain ⟨A, k, hA, hk, hpoly⟩ :=
    exists_normPoleRegularization_rightStrip_bound K hcomplex 0
  obtain ⟨L, hL, hlog⟩ := exists_normRegularizedEulerLog_bound K
  let D : ℝ := 48 / (1 / 64 : ℝ) ^ 2
  have hD : 0 < D := by norm_num [D]
  refine ⟨D * (1 + A + L), k, mul_pos hD (by linarith), hk, ?_⟩
  intro σ t hσ hσ2
  let M : ℝ := 1 + A * (4 + |t|) ^ k
  have hM : 0 < M := by dsimp [M]; positivity
  have hf : DifferentiableOn ℂ (normPoleRegularization K 0)
      (ball (verticalPoint 2 t) (2 - 31 / 32 - (1 / 64 : ℝ) / 2)) := by
    apply (normPoleRegularization_differentiableOn K 0).mono
    intro z hz
    have hre := outer_ball_re_lower hz
    change 0 < z.re
    linarith
  have hnz : ∀ z ∈ ball (verticalPoint 2 t) (2 - 31 / 32 - (1 / 64 : ℝ) / 2),
      normPoleRegularization K 0 z ≠ 0 := by
    intro z hz
    apply actualZetaRegularization_ne_zero K
    have hre := outer_ball_re_lower hz
    linarith
  have hb : ∀ z ∈ ball (verticalPoint 2 t) (2 - 31 / 32 - (1 / 64 : ℝ) / 2),
      ‖normPoleRegularization K 0 z‖ ≤ Real.exp M := by
    intro z hz
    have hre := outer_ball_re_lower hz
    have him := outer_ball_im_bound (by norm_num : (1 / 2 : ℝ) ≤ 31 / 32)
      (by norm_num : (0 : ℝ) < 1 / 64) hz
    have hp : (2 + |z.im|) ^ k ≤ (4 + |t|) ^ k :=
      Real.rpow_le_rpow (by positivity) (by linarith) hk
    have hh := (hpoly z (by linarith)).trans (mul_le_mul_of_nonneg_left hp hA.le)
    have hmexp := Real.add_one_le_exp M
    exact hh.trans (by dsimp [M] at hmexp ⊢; linarith)
  have hraw := PrimeCancellationLogDerivative.norm_logDeriv_le_on_bufferedDisk
    (by norm_num : (1 / 2 : ℝ) ≤ 31 / 32) (by norm_num : (31 / 32 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) < 1 / 64) (by norm_num : (1 / 64 : ℝ) ≤ 1 / 4)
    hM hf hnz (exp_normRegularizedEulerLog K 0 (verticalPoint 2 t) (by norm_num))
    (hlog 0 (verticalPoint 2 t) (by norm_num)) hb
    (verticalPoint_mem_inner (by linarith : (31 / 32 : ℝ) + 1 / 64 ≤ σ) hσ2)
  have hy : 1 ≤ (4 + |t|) ^ k := Real.one_le_rpow (by linarith [abs_nonneg t]) hk
  apply hraw.trans
  change 48 * (M + L) / (1 / 64 : ℝ) ^ 2 ≤ _
  have hscalar : M + L ≤ (1 + A + L) * (4 + |t|) ^ k := by
    dsimp [M]
    nlinarith
  calc
    _ = D * (M + L) := by dsimp [D]; ring
    _ ≤ D * ((1 + A + L) * (4 + |t|) ^ k) :=
      mul_le_mul_of_nonneg_left hscalar hD.le
    _ = _ := by ring

/-- A polynomial bound includes the literal total-division value at one.
The bound is on the pole-cleared logarithmic derivative, not on a fictitious
entire zeta function. -/
theorem exists_actualZetaLog_poleCleared_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) :
    ∃ C : ℝ, 0 < C ∧ ∃ m : ℕ, ∀ σ ∈ Icc (63 / 64 : ℝ) 2, ∀ t : ℝ,
      ‖(ExpansionInterfaces.Mellin.vertical σ t - 1) *
          actualPrimeLogFunction K 1 (ExpansionInterfaces.Mellin.vertical σ t)‖ ≤
        C * (1 + |t|) ^ m := by
  obtain ⟨D, k, hD, hk, hbound⟩ := exists_actualZetaRegularized_logDeriv_bound K hcomplex
  let C : ℝ := D * (4 : ℝ) ^ k + 2
  let m : ℕ := ⌈k + 1⌉₊
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, m, ?_⟩
  intro σ hσ t
  let s := ExpansionInterfaces.Mellin.vertical σ t
  have hre : 31 / 32 < s.re := by simp only [s, ExpansionInterfaces.Mellin.vertical_re]; linarith [hσ.1]
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  by_cases hs1 : s = 1
  · simp only [s] at hs1
    rw [hs1, sub_self, zero_mul, norm_zero]
    exact mul_nonneg hC.le (pow_nonneg (by positivity) m)
  have hn : ‖s - 1‖ ≤ 1 + |t| := by
    have hh := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hr : |σ - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hh' : ‖s - 1‖ ≤ |σ - 1| + |t| := by
      simpa only [s, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
        sub_zero, ExpansionInterfaces.Mellin.vertical_re,
        ExpansionInterfaces.Mellin.vertical_im] using hh
    linarith
  have hratio : ‖(s - 1) * s⁻¹‖ ≤ 1 := by
    simpa only [normPoleRatio, heckeNormPole, Complex.ofReal_zero, zero_mul,
      add_zero, sub_zero, div_eq_mul_inv] using
      normPoleRatio_norm_le_one 0 s (by linarith)
  have hlog : ‖deriv (normPoleRegularization K 0) s / normPoleRegularization K 0 s‖ ≤
      D * (4 + |t|) ^ k := hbound σ t hσ.1 hσ.2
  have heq : (s - 1) * actualPrimeLogFunction K 1 s =
      1 - (s - 1) * s⁻¹ - (s - 1) *
        (deriv (normPoleRegularization K 0) s / normPoleRegularization K 0 s) := by
    rw [actualZetaLog_eq_regularized K hre hs1]
    field_simp [sub_ne_zero.mpr hs1]
    <;> ring
  have hraw : ‖(s - 1) * actualPrimeLogFunction K 1 s‖ ≤
      2 + (1 + |t|) * (D * (4 + |t|) ^ k) := by
    rw [heq]
    apply (norm_sub_le _ _).trans
    have hfirst : ‖1 - (s - 1) * s⁻¹‖ ≤ 2 := by
      have hh := norm_sub_le (1 : ℂ) ((s - 1) * s⁻¹)
      rw [norm_one] at hh
      linarith
    rw [norm_mul]
    exact add_le_add hfirst (mul_le_mul hn hlog (norm_nonneg _) (by positivity))
  have hy : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hy0 : 0 < 1 + |t| := by positivity
  have hpow : (4 + |t|) ^ k ≤ (4 : ℝ) ^ k * (1 + |t|) ^ k := by
    rw [← Real.mul_rpow (by norm_num) hy0.le]
    exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hk
  have hpow1 : 1 ≤ (1 + |t|) ^ (k + 1) := Real.one_le_rpow hy (by linarith)
  have hsum : 2 + (1 + |t|) * (D * (4 + |t|) ^ k) ≤
      C * (1 + |t|) ^ (k + 1) := by
    have hm := mul_le_mul_of_nonneg_left hpow (mul_nonneg hy0.le hD.le)
    rw [Real.rpow_add_one hy0.ne']
    dsimp [C]
    rw [Real.rpow_add_one hy0.ne'] at hpow1
    nlinarith
  have hkm : k + 1 ≤ (m : ℝ) := Nat.le_ceil (k + 1)
  have hfinal : (1 + |t|) ^ (k + 1) ≤ (1 + |t|) ^ m := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hy hkm
  exact hraw.trans (hsum.trans (mul_le_mul_of_nonneg_left hfinal hC.le))

end Expansion.Project

#print axioms Expansion.Project.actualZeta_ne_zero
#print axioms Expansion.Project.actualZetaLog_residue
#print axioms Expansion.Project.exists_actualZetaLog_poleCleared_bound
