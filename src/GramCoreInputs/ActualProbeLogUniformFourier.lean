import ActualProbeLogProfile
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded

/-!
UNCOMPILED candidate. Uniform rapid Fourier decay of the literal logarithmic
probe profiles, before any row/base point is selected. The finite factors
are bounded using their actual continuous compact support. Repeated Euler
derivatives control the infinite-place dilation at every point. The fixed
denominator cutoff then controls every input Schwartz seminorm, and the
actual Schwartz Fourier CLM transports those bounds. No uniform estimate,
summability or Fourier identity is supplied as a mathematical hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators FourierTransform ContDiff NNReal

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "G" => sLocalMultiplicativeGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "D" => (Module.finrank ℚ K : ℝ)

/-- The original finite tensor has a bound independent of its unit arguments,
including the empty finite-place set. -/
theorem exists_probeFiniteTensor_uniform_bound (P : ProbeData K S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : G,
      ‖∏ p : S, P.additive.finiteTest p ((x.2 p).val)‖ ≤ B := by
  have hlocal (p : S) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ z : p.val.adicCompletion K, ‖P.additive.finiteTest p z‖ ≤ B := by
    have hc := (P.additive.finite_locallyConstant p).continuous
    obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support
      (P.additive.finite_compactSupport p)
    refine ⟨max B 0, le_max_right _ _, fun z => ?_⟩
    exact (hB z).trans (le_max_left _ _)
  choose B hB hb using hlocal
  refine ⟨∏ p : S, B p, Finset.prod_nonneg (fun p _ => hB p), fun x => ?_⟩
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
    (fun p _ => hb p ((x.2 p).val))

/-- Exact repeated derivatives of the positive log-norm dilation. -/
theorem iteratedDeriv_traceSchwartz_normDilation (φ : SchwartzMap V ℂ)
    (y : V) (n : ℕ) :
    iteratedDeriv n (fun v : ℝ => φ (Real.exp (v / D) • y)) =
      fun v => traceSchwartzEulerIterCLM K n φ (Real.exp (v / D) • y) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, traceSchwartzEulerIterCLM_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext v
      simpa only [traceSchwartzEulerIterCLM_succ] using
        deriv_traceSchwartz_normDilation K (traceSchwartzEulerIterCLM K n φ) y v

/-- Every derivative of the actual raw profile is uniformly bounded in both
the base point and the real log-radius. -/
theorem exists_probeRawLogProfile_iteratedDeriv_uniform_bound
    (P : ProbeData K S) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (x : G) (v : ℝ),
      ‖iteratedDeriv n (probeRawLogProfile K S P x) v‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_probeFiniteTensor_uniform_bound K S P
  let φ := traceSchwartzEulerIterCLM K n P.additive.infiniteTest
  refine ⟨SchwartzMap.seminorm ℝ 0 0 φ * B,
    mul_nonneg (apply_nonneg _ _) hB, fun x v => ?_⟩
  let y : V := (traceToMixed K).symm (x.1 : mixedEmbedding.mixedSpace K)
  let f : ℝ → ℂ := fun u => P.additive.infiniteTest (Real.exp (u / D) • y)
  have he : probeRawLogProfile K S P x = fun u : ℝ =>
      f (-u) * ∏ p : S, P.additive.finiteTest p ((x.2 p).val) := by
    funext u
    exact probeRawLogProfile_eq K S P x u
  have hn : iteratedDeriv n (fun u : ℝ => f (-u)) v =
      (-1 : ℝ) ^ n • φ (Real.exp ((-v) / D) • y) := by
    rw [iteratedDeriv_comp_neg]
    exact congrArg (fun z : ℂ => (-1 : ℝ) ^ n • z)
      (congrFun (iteratedDeriv_traceSchwartz_normDilation K
        P.additive.infiniteTest y n) (-v))
  calc
    _ = ‖φ (Real.exp ((-v) / D) • y)‖ *
        ‖∏ p : S, P.additive.finiteTest p ((x.2 p).val)‖ := by
      rw [he, iteratedDeriv_mul_const_field, hn, norm_mul, norm_smul]
      simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ ≤ SchwartzMap.seminorm ℝ 0 0 φ * B :=
      mul_le_mul (SchwartzMap.norm_le_seminorm ℝ φ _) (hb x)
        (norm_nonneg _) (apply_nonneg _ _)

/-- The fixed denominator cutoff, as a genuine complex Schwartz function. -/
def probeComplexLogCutoff (P : ProbeData K S) : SchwartzMap ℝ ℂ := by
  let a := denominatorLogCutoff P.denominator.toSmoothAnnularTest
  have hc : HasCompactSupport (fun v : ℝ => a v • (1 : ℂ)) :=
    a.hasCompactSupport.smul_right
  exact hc.toSchwartzMap (a.contDiff.smul contDiff_const)

@[simp] theorem probeComplexLogCutoff_apply (P : ProbeData K S) (v : ℝ) :
    probeComplexLogCutoff K S P v =
      (denominatorLogCutoff P.denominator.toSmoothAnnularTest v : ℂ) := by
  change denominatorLogCutoff P.denominator.toSmoothAnnularTest v • (1 : ℂ) = _
  simp only [Complex.real_smul, mul_one]

/-- A literal product identity, so the scalar cutoff is retained in every
Leibniz term rather than estimated by an assumed profile bound. -/
theorem probeLogSchwartz_eq_cutoff_mul_raw (P : ProbeData K S) (x : G) :
    (probeLogSchwartz K S P x : ℝ → ℂ) =
      fun v => probeComplexLogCutoff K S P v * probeRawLogProfile K S P x v := by
  funext v
  simp only [probeLogSchwartz_apply, probeCutLogProfile,
    probeComplexLogCutoff_apply, Complex.real_smul]

/-- Every input Schwartz seminorm of the log profile has an actual uniform
bound before the base point is chosen. -/
theorem exists_probeLogSchwartz_seminorm_uniform_bound
    (P : ProbeData K S) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : G,
      SchwartzMap.seminorm ℝ k n (probeLogSchwartz K S P x) ≤ C := by
  choose B hB hb using exists_probeRawLogProfile_iteratedDeriv_uniform_bound K S P
  let a := probeComplexLogCutoff K S P
  let C : ℝ := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * SchwartzMap.seminorm ℝ k i a * B (n - i)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)) (hB _))
  refine ⟨C, hC, fun x => ?_⟩
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ hC
  intro v
  have he : iteratedDeriv n (probeLogSchwartz K S P x) v =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
        iteratedDeriv i a v * iteratedDeriv (n - i) (probeRawLogProfile K S P x) v := by
    rw [probeLogSchwartz_eq_cutoff_mul_raw]
    exact iteratedDeriv_fun_mul (a.smooth (n : ℕ∞)).contDiffAt
      ((contDiff_probeRawLogProfile K S P x).contDiffAt.of_le (by simp))
  rw [he]
  calc
    _ ≤ |v| ^ k * ∑ i ∈ Finset.range (n + 1),
        ‖(n.choose i : ℂ) * iteratedDeriv i a v *
          iteratedDeriv (n - i) (probeRawLogProfile K S P x) v‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (abs_nonneg _) _)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (|v| ^ k * ‖iteratedDeriv i a v‖) *
          ‖iteratedDeriv (n - i) (probeRawLogProfile K S P x) v‖ := by
      simp only [Finset.mul_sum, norm_mul, Complex.norm_natCast]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ C := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm' ℝ k i a v)
          (Nat.cast_nonneg _))
        (hb (n - i) x v) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))

/-- The standard Fourier CLM bound, without changing its 2*pi convention. -/
theorem probeRealFourier_seminorm_bound (k n : ℕ) :
    ∃ t : Finset (ℕ × ℕ), ∃ A : ℝ≥0, A ≠ 0 ∧
      ∀ f : SchwartzMap ℝ ℂ,
        SchwartzMap.seminorm ℝ k n (𝓕 f) ≤
          (A : ℝ) * t.sup (schwartzSeminormFamily ℝ ℝ ℂ) f := by
  let T : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
    SchwartzMap.fourierTransformCLM ℝ
  let q : Seminorm ℝ (SchwartzMap ℝ ℂ) :=
    (SchwartzMap.seminorm ℝ k n).comp T.toLinearMap
  have hp := schwartz_withSeminorms ℝ ℝ ℂ
  have hq : Continuous q := (hp.continuous_seminorm (k, n)).comp T.continuous
  obtain ⟨t, A, hA, hbound⟩ := Seminorm.bound_of_continuous hp q hq
  refine ⟨t, A, hA, fun f => ?_⟩
  have h := Seminorm.le_def.mp hbound f
  change SchwartzMap.seminorm ℝ k n (𝓕 f) ≤
    (A : ℝ) * t.sup (schwartzSeminormFamily ℝ ℝ ℂ) f at h
  exact h

/-- All Fourier seminorms are uniformly bounded for the original profiles. -/
theorem exists_probeLogFourier_seminorm_uniform_bound
    (P : ProbeData K S) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : G,
      SchwartzMap.seminorm ℝ k n (𝓕 (probeLogSchwartz K S P x)) ≤ C := by
  obtain ⟨t, A, hA, hFourier⟩ := probeRealFourier_seminorm_bound k n
  choose B hB hb using fun p : ℕ × ℕ =>
    exists_probeLogSchwartz_seminorm_uniform_bound K S P p.1 p.2
  let C0 : ℝ := ∑ p ∈ t, B p
  have hC0 : 0 ≤ C0 := Finset.sum_nonneg (fun p _ => hB p)
  have hBp (p : ℕ × ℕ) (hp : p ∈ t) : B p ≤ C0 :=
    Finset.single_le_sum (fun q _ => hB q) hp
  refine ⟨(A : ℝ) * C0, mul_nonneg (NNReal.coe_nonneg A) hC0, fun x => ?_⟩
  have hs : t.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (probeLogSchwartz K S P x) ≤ C0 :=
    Seminorm.finset_sup_apply_le hC0 (fun p hp => (hb p x).trans (hBp p hp))
  exact (hFourier _).trans (mul_le_mul_of_nonneg_left hs (NNReal.coe_nonneg A))

/-- Actual rapid Fourier decay, uniform over all rows and base points. The
constant is selected after P and N, before x, the Fourier frequency, or any
norm-section parameters subsequently used to form x. -/
theorem exists_probeLogFourier_uniform_rapid_decay (P : ProbeData K S) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : G) (ξ : ℝ),
      (1 + |ξ|) ^ N * ‖(𝓕 (probeLogSchwartz K S P x)) ξ‖ ≤ C := by
  choose B hB hb using fun p : ℕ × ℕ =>
    exists_probeLogFourier_seminorm_uniform_bound K S P p.1 p.2
  let t : Finset (ℕ × ℕ) := Finset.Iic (N, 0)
  let C0 : ℝ := ∑ p ∈ t, B p
  have hC0 : 0 ≤ C0 := Finset.sum_nonneg (fun p _ => hB p)
  refine ⟨2 ^ N * C0, mul_nonneg (pow_nonneg (by norm_num) _) hC0, fun x ξ => ?_⟩
  have hs : t.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (𝓕 (probeLogSchwartz K S P x)) ≤ C0 := by
    apply Seminorm.finset_sup_apply_le hC0
    intro p hp
    exact (hb p x).trans (Finset.single_le_sum (fun q _ => hB q) hp)
  have hpoint := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl
      (𝓕 (probeLogSchwartz K S P x)) ξ
  have hp : (1 + |ξ|) ^ N * ‖(𝓕 (probeLogSchwartz K S P x)) ξ‖ ≤
      2 ^ N * t.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (𝓕 (probeLogSchwartz K S P x)) := by
    change (1 + |ξ|) ^ N * ‖(𝓕 (probeLogSchwartz K S P x)) ξ‖ ≤
      2 ^ N * (Finset.Iic (N, 0)).sup
        (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2)
        (𝓕 (probeLogSchwartz K S P x))
    simpa only [Real.norm_eq_abs,
      norm_iteratedFDeriv_zero] using hpoint
  exact hp.trans (mul_le_mul_of_nonneg_left hs (pow_nonneg (by norm_num) _))

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft
