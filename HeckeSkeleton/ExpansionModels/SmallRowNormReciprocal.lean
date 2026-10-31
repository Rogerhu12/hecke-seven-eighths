import HeckeSkeleton.ExpansionModels.SmallRowNormContinuation
import HeckeSkeleton.HeckeUniformStripGrowth
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The norm-twist reciprocal on the original common line

The actual pole-cleared norm branch has a polynomial bound throughout a
right strip.  Its Euler logarithm is the genuine Hecke Euler logarithm plus
the logarithm of (s-1-it)/(s-it); the latter is uniformly bounded to the right
of 151/100.  The original common zero boundary therefore gives the needed
reciprocal bound by the proved logarithmic-control theorem.

The endpoint includes every bounded exceptional row that becomes a pure
norm twist.  There is no high-row cutoff or non-norm restriction here.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.SmallRows

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.HeckeBufferedReciprocal HeckeSkeleton.HeckeUniformStripGrowth
open HeckeSkeleton.ActualEulerLogarithm
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]

theorem normPoleRatio_re_pos (t : ℝ) (s : ℂ) (hs : 1 < s.re) :
    0 < (normPoleRatio t s).re := by
  let z := s - (t : ℂ) * Complex.I
  have hzr : 1 < z.re := by simpa [z] using hs
  have hz : z ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have heq : normPoleRatio t s = (z - 1) / z := by
    dsimp only [normPoleRatio, z, heckeNormPole]
    congr 1
    ring
  rw [heq, Complex.div_re]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  apply div_pos _ (Complex.normSq_pos.mpr hz)
  have hp : 0 < (z.re - 1) * z.re := mul_pos (sub_pos.mpr hzr) (by linarith)
  nlinarith [sq_nonneg z.im]

theorem normPoleRatio_norm_lower (t : ℝ) (s : ℂ) (hs : 151 / 100 ≤ s.re) :
    1 / 3 ≤ ‖normPoleRatio t s‖ := by
  let z := s - (t : ℂ) * Complex.I
  have hzr : 151 / 100 ≤ z.re := by simpa [z] using hs
  have hz : z ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have hhalf : 1 / 2 ≤ ‖z - 1‖ := by
    have hh := (le_abs_self (z - 1).re).trans (Complex.abs_re_le_norm (z - 1))
    simp only [Complex.sub_re, Complex.one_re] at hh
    linarith
  have htriangle : ‖z‖ ≤ ‖z - 1‖ + 1 := by
    simpa only [sub_add_cancel, norm_one] using norm_add_le (z - 1) (1 : ℂ)
  have heq : normPoleRatio t s = (z - 1) / z := by
    dsimp only [normPoleRatio, z, heckeNormPole]
    congr 1
    ring
  rw [heq, norm_div]
  apply (le_div_iff₀ (norm_pos_iff.mpr hz)).mpr
  linarith

theorem norm_log_normPoleRatio_le (t : ℝ) (s : ℂ) (hs : 151 / 100 ≤ s.re) :
    ‖Complex.log (normPoleRatio t s)‖ ≤ Real.log 3 + Real.pi := by
  have hlo := normPoleRatio_norm_lower t s hs
  have hhi := normPoleRatio_norm_le_one t s (by linarith)
  have hpos : 0 < ‖normPoleRatio t s‖ := (by norm_num : (0 : ℝ) < 1 / 3).trans_le hlo
  have hloglo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 3) hlo
  have hloghi := Real.log_le_log hpos hhi
  have heq : Real.log (1 / 3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  rw [heq] at hloglo
  rw [Real.log_one] at hloghi
  have hlog : |Real.log ‖normPoleRatio t s‖| ≤ Real.log 3 := by
    apply abs_le.mpr
    exact ⟨hloglo, hloghi.trans (Real.log_nonneg (by norm_num))⟩
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
    rw [Complex.log_re, Complex.log_im]
    exact add_le_add hlog (Complex.abs_arg_le_pi _))

def normRegularizedEulerLog (t : ℝ) (s : ℂ) : ℂ :=
  heckeEulerLog K (heckeNormTwist K t) s + Complex.log (normPoleRatio t s)

theorem normRegularizedEulerLog_differentiableOn (t : ℝ) :
    DifferentiableOn ℂ (normRegularizedEulerLog K t) {s : ℂ | 1 < s.re} := by
  apply (heckeEulerLog_differentiableOn K (heckeNormTwist K t)).add
  intro s hs
  have hratio : DifferentiableAt ℂ (normPoleRatio t) s := by
    apply (differentiableAt_id.sub_const _).div (differentiableAt_id.sub_const _)
    exact Complex.ne_zero_of_re_pos (by simpa using (show 0 < s.re by linarith))
  exact ((Complex.differentiableAt_log
    (Complex.mem_slitPlane_iff.mpr (Or.inl (normPoleRatio_re_pos t s hs)))).comp s
      hratio).differentiableWithinAt

theorem exp_normRegularizedEulerLog (t : ℝ) (s : ℂ) (hs : 1 < s.re) :
    Complex.exp (normRegularizedEulerLog K t s) = normPoleRegularization K t s := by
  rw [normRegularizedEulerLog, Complex.exp_add,
    exp_heckeEulerLog_eq_continuation K (heckeNormTwist K t) s hs,
    Complex.exp_log (Complex.ne_zero_of_re_pos (normPoleRatio_re_pos t s hs)),
    normPoleRegularization_right K t s hs]
  exact mul_comm _ _

/-- Constants are selected before the norm parameter: only the polynomial
strip-growth constant later needs to depend on that fixed parameter. -/
theorem exists_normRegularizedEulerLog_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ t : ℝ, ∀ s : ℂ, 151 / 100 ≤ s.re →
      ‖normRegularizedEulerLog K t s‖ ≤ A := by
  obtain ⟨A, hA, hlog⟩ := exists_uniform_heckeEulerLog_bound K
  refine ⟨A + (Real.log 3 + Real.pi), ?_, ?_⟩
  · have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    linarith [Real.pi_pos]
  · intro t s hs
    exact (norm_add_le _ _).trans
      (add_le_add (hlog (heckeNormTwist K t) s hs) (norm_log_normPoleRatio_le t s hs))

/-- An actual polynomial bound for the regularized norm branch on the whole
right half-strip; its constants are independent of the later height. -/
theorem exists_normPoleRegularization_rightStrip_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (t : ℝ) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖normPoleRegularization K t s‖ ≤ C * (2 + |s.im|) ^ k := by
  obtain ⟨A, k, hA, hk, hstrip⟩ := exists_normPoleNumerator_strip_bound K hcomplex t
  obtain ⟨D, hD, hright⟩ := exists_uniform_rightHalfPlane_bound K 2 (by norm_num)
  refine ⟨2 * A + D, k, by positivity, hk, ?_⟩
  intro s hs
  have hheight : 1 ≤ (2 + |s.im|) ^ k := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hk
  by_cases hs4 : s.re ≤ 4
  · have hb := hstrip s hs hs4
    have hden : 1 / 2 ≤ ‖s - (t : ℂ) * Complex.I‖ := by
      have hh := (le_abs_self (s - (t : ℂ) * Complex.I).re).trans
        (Complex.abs_re_le_norm (s - (t : ℂ) * Complex.I))
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, sub_zero] at hh
      exact hs.trans hh
    have hdenpos : 0 < ‖s - (t : ℂ) * Complex.I‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hden
    rw [normPoleRegularization, norm_div]
    apply (div_le_iff₀ hdenpos).mpr
    have hcoef : A ≤ (2 * A + D) * ‖s - (t : ℂ) * Complex.I‖ := by nlinarith
    exact hb.trans ((mul_le_mul_of_nonneg_right hcoef (by positivity)).trans_eq (by ring))
  · rw [normPoleRegularization_right K t s (by linarith), norm_mul]
    have hh := mul_le_mul (normPoleRatio_norm_le_one t s hs)
      (hright (heckeNormTwist K t) s (by linarith)) (norm_nonneg _) zero_le_one
    have hcoef : D ≤ 2 * A + D := by linarith
    exact (by simpa only [one_mul] using hh).trans
      ((le_mul_of_one_le_right hD.le hheight).trans
        (mul_le_mul_of_nonneg_right hcoef (by positivity)))

/-- Every actual pure norm denominator is bounded on the common line under
the original packet zero upper bound.  No exceptional rows are discarded. -/
theorem exists_common_line_normTwist_reciprocal_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (t : ℝ)
    {B e : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hupper : ∀ H : ℝ, ZeroUpperBound K (heckeNormTwist K t) H B) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, s.re = B + e →
      ‖(heckeContinuation K (heckeNormTwist K t) s)⁻¹‖ ≤
        C * (4 + |s.im|) ^ k := by
  let kappa : ℝ := e / 8
  let a : ℝ := B - e / 4
  have hkappa : 0 < kappa := div_pos he (by norm_num)
  have hkappa1 : kappa < 1 / 1000 := by dsimp [kappa]; linarith
  have ha : 1 / 2 ≤ a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hab : a + 2 * kappa = B := by dsimp [a, kappa]; ring
  obtain ⟨A, k, hA, hk, hpoly⟩ := exists_normPoleRegularization_rightStrip_bound K hcomplex t
  obtain ⟨L, hL, hlog⟩ := exists_normRegularizedEulerLog_bound K
  obtain ⟨D, hD, hcontrol⟩ := HeckeSkeleton.BufferedReciprocal.buffered_value_and_reciprocal_of_rectangle
    (e := kappa) (A := L) (M := 1) (ε := 1) hkappa hkappa1 hL (by norm_num) (by norm_num)
  let A0 : ℝ := Real.exp 1 * max 1 A
  have hmax : 0 < max 1 A := zero_lt_one.trans_le (le_max_left _ _)
  have hA0 : 0 < A0 := mul_pos (Real.exp_pos _) hmax
  have hAA0 : A ≤ A0 := by
    apply (le_max_right 1 A).trans
    exact le_mul_of_one_le_left hmax.le (Real.one_le_exp (by norm_num))
  have hexp : Real.exp 1 ≤ A0 := le_mul_of_one_le_right (Real.exp_pos _).le (le_max_left _ _)
  refine ⟨D * A0, k, mul_pos hD hA0, hk, ?_⟩
  intro s hs
  let H : ℝ := |s.im|
  let HU : ℝ := |s.im| + 2
  let C : ℝ := A0 * (2 + HU) ^ k
  have hH : 0 ≤ H := abs_nonneg _
  have hHU : 0 ≤ HU := by dsimp [HU]; positivity
  have hheight : 1 ≤ (2 + HU) ^ k := Real.one_le_rpow (by linarith) hk
  have hAC : A0 ≤ C := le_mul_of_one_le_right hA0.le hheight
  have hC : Real.exp 1 ≤ C := hexp.trans hAC
  have hf := (normPoleRegularization_differentiableOn K t).mono
    (show {z : ℂ | a + 2 * kappa < z.re ∧ |z.im| ≤ HU} ⊆ {z : ℂ | 0 < z.re} from by
      intro z hz
      rw [hab] at hz
      linarith [hz.1])
  have hz : ∀ z : ℂ, a + 2 * kappa < z.re → |z.im| ≤ HU →
      normPoleRegularization K t z ≠ 0 := by
    intro z hz hh
    rw [hab] at hz
    exact normPoleRegularization_ne_zero_of_upper K t HU B (by linarith) (hupper HU) z hz hh
  have hp : ∀ z : ℂ, a + 2 * kappa < z.re → |z.im| ≤ HU →
      ‖normPoleRegularization K t z‖ ≤ C ^ (1 : ℝ) := by
    intro z hz hh
    rw [hab] at hz
    rw [Real.rpow_one]
    exact (hpoly z (by linarith)).trans
      (mul_le_mul hAA0 (Real.rpow_le_rpow (by positivity) (by linarith) hk)
        (by positivity) hA0.le)
  have hbound := hcontrol a C H HU (normPoleRegularization K t) (normRegularizedEulerLog K t)
    ha ha1 hC (by dsimp [H, HU]; linarith) hf hz hp
    (normRegularizedEulerLog_differentiableOn K t)
    (exp_normRegularizedEulerLog K t) (hlog t)
    s (by dsimp [a, kappa]; linarith) (by linarith) le_rfl
  have hrec := (normTwist_reciprocal_le_regularized K t s (by linarith)).trans
    ((le_add_of_nonneg_left (norm_nonneg (normPoleRegularization K t s))).trans hbound)
  rw [Real.rpow_one] at hrec
  have hheight_eq : 2 + HU = 4 + |s.im| := by dsimp only [HU]; ring
  dsimp only [C] at hrec
  rw [hheight_eq] at hrec
  exact hrec.trans_eq (by ring)

end HeckeSkeleton.Expansion.SmallRows

#print axioms HeckeSkeleton.Expansion.SmallRows.exists_normRegularizedEulerLog_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_normPoleRegularization_rightStrip_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_common_line_normTwist_reciprocal_bound
