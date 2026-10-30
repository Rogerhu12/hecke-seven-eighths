/-
Copyright (c) 2026. Released under the Apache 2.0 license.
Adapted from OpenAI/math fd4aeeb2:
lean/OAI/NumberTheory/DirichletL/PrimeLogProfile.lean.
The extraction replaces the arithmetic sieve cutoff with an independent
mathlib smooth bump and removes all number-field dependencies.
-/
import PrimeCancellationCompactFamily
import PrimeCancellationLogWindow
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct


namespace PrimeCancellationLogProfile

noncomputable section
open scoped Classical ContDiff Topology FourierTransform
open Set Filter MeasureTheory

def cutoffBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoff (x : ℝ) : ℂ := (cutoffBump x : ℂ)

@[simp] theorem cutoff_apply (x : ℝ) : cutoff x = (cutoffBump x : ℂ) := rfl

theorem cutoff_smooth : ContDiff ℝ ∞ cutoff :=
  Complex.ofRealCLM.contDiff.comp cutoffBump.contDiff

def safeInverse (x : ℝ) : ℂ :=
  (1-cutoff (4*x))/(x : ℂ)

theorem safeInverse_eq (x : ℝ) (hx : 1/2≤|x|) : safeInverse x=(x : ℂ)⁻¹ := by
  have hz : cutoffBump (4*x)=0 := by
    apply cutoffBump.zero_of_le_dist
    change 2≤dist (4*x) 0
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul]
    norm_num
    linarith
  simp [safeInverse, cutoff_apply, hz]

theorem safeInverse_smooth : ContDiff ℝ ∞ safeInverse := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : safeInverse =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ)<1/4)] with y hy
      have hy' : |y|<1/4 := by simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hy
      have hone : cutoffBump (4*y)=1 := by
        apply cutoffBump.one_of_mem_closedBall
        change dist (4*y) 0≤1
        rw [dist_zero_right, Real.norm_eq_abs, abs_mul]
        norm_num
        linarith
      simp [safeInverse, cutoff_apply, hone]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hnum : ContDiff ℝ ∞ (fun y : ℝ => (1 : ℂ)-cutoff (4*y)) :=
      contDiff_const.sub ((cutoff_smooth).comp
        (contDiff_const.mul contDiff_id))
    change ContDiffAt ℝ ∞ (fun y : ℝ => (1-cutoff (4*y))/(y : ℂ)) x
    simpa only [div_eq_mul_inv, Pi.inv_apply, Complex.ofRealCLM_apply] using hnum.contDiffAt.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.inv (Complex.ofReal_ne_zero.mpr hx))

def profile (W : ℝ→ℂ) (A y : ℝ) : ℂ :=
  W y * (A : ℂ) * safeInverse (1+A*Real.log y)

theorem profile_support (W : ℝ→ℂ) (A : ℝ) :
    Function.support (profile W A) ⊆ Function.support W := by
  intro y hy hW
  exact hy (by simp [profile,hW])

theorem profile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (A : ℝ) :
    ContDiff ℝ ∞ (profile W A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y=0
  · subst y
    have he : profile W A =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [(isOpen_Iio.mem_nhds ha)] with y hy
      have hw : W y=0 := by
        by_contra hh
        exact (not_le_of_gt hy) (hWs hh).1
      simp [profile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact ((hW.contDiffAt.mul contDiffAt_const).mul
      (safeInverse_smooth.contDiffAt.comp y
        (contDiffAt_const.add (contDiffAt_const.mul (Real.contDiffAt_log.mpr hy)))))

def logFamily (W : ℝ→ℂ) (p : ℝ×ℝ) (u : ℝ) : ℂ :=
  Real.exp (-p.2*u) • (W (Real.exp (-u)) * (p.1 : ℂ) * safeInverse (1-p.1*u))

theorem logFamily_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (logFamily W)) := by
  change ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ =>
    Real.exp (-p.1.2*p.2) • (W (Real.exp (-p.2)) * (p.1.1 : ℂ) * safeInverse (1-p.1.1*p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.snd.neg.mul contDiff_snd)).smul
    (((hW.comp (Real.contDiff_exp.comp contDiff_snd.neg)).mul
      (Complex.ofRealCLM.contDiff.comp contDiff_fst.fst)).mul
      (safeInverse_smooth.comp (contDiff_const.sub (contDiff_fst.fst.mul contDiff_snd))))

theorem logFamily_eq (W : ℝ→ℂ) (A σ u : ℝ) :
    logFamily W (A,σ) u = PrimeCancellationCompactFamily.mellinLogFamily (profile W A) σ u := by
  simp only [logFamily, PrimeCancellationCompactFamily.mellinLogFamily, profile, Real.log_exp]
  congr 3
  ring

theorem logFamily_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (logFamily W p) ⊆ Icc (-Real.log b) (-Real.log a) := by
  have he : logFamily W p = PrimeCancellationCompactFamily.mellinLogFamily (profile W p.1) p.2 := by
    funext u
    exact logFamily_eq W p.1 p.2 u
  rw [he]
  exact PrimeCancellationCompactFamily.mellinLogFamily_support _ a b ha ((profile_support W p.1).trans hWs) _

theorem uniform_mellin_decay (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ A ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (profile W A) ((σ : ℂ)+t*Complex.I)‖≤C := by
  obtain ⟨C,hC,hb⟩ := PrimeCancellationCompactFamily.compact_family_fourier_weighted_bound
    (logFamily W) (logFamily_smooth W hW)
    (Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (logFamily_support W a b ha hWs)
    ((Icc (0 : ℝ) 1) ×ˢ (Icc lo hi)) (isCompact_Icc.prod isCompact_Icc) j
  refine ⟨(1+2*Real.pi)^j*C,by positivity,?_⟩
  intro A hA σ hσ t
  rw [PrimeCancellationCompactFamily.mellin_eq_logFamily_fourier]
  have he : PrimeCancellationCompactFamily.mellinLogFamily (profile W A) σ = logFamily W (A,σ) := by
    funext u
    exact (logFamily_eq W A σ u).symm
  rw [he]
  have ht : |t|=(2*Real.pi)*|t/(2*Real.pi)| := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*Real.pi)]
    field_simp
  have hbase : 1+|t|≤(1+2*Real.pi)*(1+|t/(2*Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos,abs_nonneg (t/(2*Real.pi))]
  calc
    _ ≤ ((1+2*Real.pi)*(1+|t/(2*Real.pi)|))^j *
        ‖𝓕 (logFamily W (A,σ)) (t/(2*Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1+2*Real.pi)^j*((1+|t/(2*Real.pi)|)^j *
        ‖𝓕 (logFamily W (A,σ)) (t/(2*Real.pi))‖) := by rw [mul_pow,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb (A,σ) ⟨hA,hσ⟩ _) (by positivity)

theorem profile_eq_log_division (W : ℝ→ℂ) (a b P : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hP : 0<P)
    (hlarge : 2*(|Real.log a|+|Real.log b|)+1≤Real.log P) :
    profile W (1/Real.log P) = fun y => W y / (Real.log (P*y) : ℂ) := by
  funext y
  by_cases hy : W y=0
  · simp [profile,hy]
  have hs := hWs hy
  have hyp : 0<y := ha.trans_le hs.1
  have hlogs : |Real.log y|≤|Real.log a|+|Real.log b| := by
    apply abs_le.mpr
    constructor
    · have h := Real.log_le_log ha hs.1
      linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
    · have h := Real.log_le_log hyp hs.2
      linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]
  have hp : 0<Real.log P := by linarith [abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
  have hhalf : 1/2≤1+(1/Real.log P)*Real.log y := by
    have he : 1+(1/Real.log P)*Real.log y = (Real.log P+Real.log y)/Real.log P := by field_simp
    rw [he]
    apply (le_div_iff₀ hp).mpr
    linarith [(abs_le.mp hlogs).1]
  have hi := safeInverse_eq (1+(1/Real.log P)*Real.log y)
    (hhalf.trans (le_abs_self _))
  rw [profile,hi,Real.log_mul (ne_of_gt hP) (ne_of_gt hyp)]
  push_cast
  have hn : (Real.log P : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hn' : (Real.log P : ℂ)+(Real.log y : ℂ)≠0 := by
    have : 0<Real.log P+Real.log y := by
      linarith [(abs_le.mp hlogs).1,abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
    exact_mod_cast this.ne'
  field_simp


/-- For a fixed smooth window supported in [1,2], its exact logarithmic
division windows have uniformly cubically decaying Mellin transforms once
P is large. The threshold is the explicit constant exp(4). No Mellin bound
or finite-prime-sum estimate is assumed. -/
theorem exists_uniform_logWindow_mellin_decay (W : ℝ → ℂ)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1 : ℝ) 2) :
    ∃ P₀ D : ℝ, 2 ≤ P₀ ∧ 0 ≤ D ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ σ ∈ Icc (1 / 2 : ℝ) 2, ∀ t : ℝ,
        ‖mellin (PrimeCancellationLogWindow.logWindow P W)
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D / (1 + |t|) ^ 3 := by
  obtain ⟨D, hD, hdecay⟩ := uniform_mellin_decay W 1 2 (by norm_num) hWs hW
    (1 / 2) 2 3
  refine ⟨Real.exp 4, D, ?_, hD.le, ?_⟩
  · have h := Real.add_one_le_exp (4 : ℝ)
    linarith
  · intro P hP σ hσ t
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
    have heq : profile W (1 / Real.log P) = PrimeCancellationLogWindow.logWindow P W := by
      change profile W (1 / Real.log P) = (fun y => W y / (Real.log (P * y) : ℂ))
      exact profile_eq_log_division W 1 2 P (by norm_num) hWs hPpos hlarge
    have hb := hdecay (1 / Real.log P) hA σ hσ t
    rw [heq] at hb
    apply (le_div_iff₀ (show 0 < (1 + |t|) ^ 3 by positivity)).mpr
    simpa only [mul_comm] using hb

#print axioms cutoff_apply
#print axioms cutoff_smooth
#print axioms safeInverse_eq
#print axioms safeInverse_smooth
#print axioms profile_support
#print axioms profile_smooth
#print axioms logFamily_smooth
#print axioms logFamily_eq
#print axioms logFamily_support
#print axioms uniform_mellin_decay
#print axioms profile_eq_log_division
#print axioms exists_uniform_logWindow_mellin_decay

end

end PrimeCancellationLogProfile
