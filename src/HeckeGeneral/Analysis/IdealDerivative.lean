import HeckeGeneral.Analysis.IdealLogWeights
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Termwise and higher derivatives of actual ideal Dirichlet series

The signed logarithmic moments are absolutely convergent on Re(s) > 1.
We use their summable bounds on smaller open half-planes to differentiate
the actual ideal sums. Higher derivatives follow by equality of germs on
the open half-plane, not by differentiating a merely pointwise equality.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField Ideal Filter
open scoped nonZeroDivisors Topology

variable (K : Type*) [Field K] [NumberField K]

theorem hasDerivAt_idealDirichletTerm (a : NonzeroIdeal K → ℂ)
    (I : NonzeroIdeal K) (s : ℂ) :
    HasDerivAt (fun z => dirichletTerm (idealNorm K) a z I)
      (idealLogTerm K a 1 s I) s := by
  have hbase := (hasDerivAt_neg' s).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr (idealNorm_pos K I).ne'))
  change HasDerivAt (fun z => a I * (idealNorm K I : ℂ) ^ (-z)) _ s
  apply (hbase.const_mul (a I)).congr_deriv
  rw [← Complex.ofReal_log (idealNorm_pos K I).le]
  simp only [idealLogTerm, pow_one, dirichletTerm]
  ring

theorem hasDerivAt_idealLogTerm (a : NonzeroIdeal K → ℂ) (k : ℕ)
    (I : NonzeroIdeal K) (s : ℂ) :
    HasDerivAt (fun z => idealLogTerm K a k z I)
      (idealLogTerm K a (k + 1) s I) s := by
  change HasDerivAt (fun z => (-(Real.log (idealNorm K I) : ℂ)) ^ k *
    dirichletTerm (idealNorm K) a z I) _ s
  apply ((hasDerivAt_idealDirichletTerm K a I s).const_mul
    ((-(Real.log (idealNorm K I) : ℂ)) ^ k)).congr_deriv
  simp only [idealLogTerm, pow_succ]
  ring

theorem differentiable_idealLogTerm (a : NonzeroIdeal K → ℂ) (k : ℕ)
    (I : NonzeroIdeal K) : Differentiable ℂ (fun s => idealLogTerm K a k s I) :=
  fun s => (hasDerivAt_idealLogTerm K a k I s).differentiableAt

theorem differentiableOn_idealLogSeries_above (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ (idealLogSeries K a k) {s : ℂ | σ < s.re} := by
  exact Complex.differentiableOn_tsum_of_summable_norm
    (summable_ideal_logPower_rpow K k hσ)
    (fun I => (differentiable_idealLogTerm K a k I).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)
    (fun I s hs => norm_idealLogTerm_le_on_halfPlane K a ha k hs.le I)

/-- The differentiated sum is a genuine absolutely convergent log-weighted series. -/
theorem hasDerivAt_idealLogSeries (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (idealLogSeries K a k) (idealLogSeries K a (k + 1) s) s := by
  let σ : ℝ := (1 + s.re) / 2
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hsσ : σ < s.re := by dsimp [σ]; linarith
  have hopen : IsOpen {z : ℂ | σ < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hsum := Complex.hasSum_deriv_of_summable_norm
    (summable_ideal_logPower_rpow K k hσ)
    (fun I => (differentiable_idealLogTerm K a k I).differentiableOn)
    hopen
    (fun I z hz => norm_idealLogTerm_le_on_halfPlane K a ha k hz.le I) hsσ
  simp_rw [(hasDerivAt_idealLogTerm K a k _ _).deriv] at hsum
  exact ((differentiableOn_idealLogSeries_above K a ha k hσ).differentiableAt
    (hopen.mem_nhds hsσ)).hasDerivAt.congr_deriv hsum.tsum_eq.symm

theorem deriv_idealLogSeries (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    deriv (idealLogSeries K a k) s = idealLogSeries K a (k + 1) s :=
  (hasDerivAt_idealLogSeries K a ha k hs).deriv

theorem hasDerivAt_idealDirichletSeries (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (idealDirichletSeries K a) (idealLogSeries K a 1 s) s := by
  have hzero : idealLogSeries K a 0 = idealDirichletSeries K a :=
    funext (idealLogSeries_zero K a)
  rw [← hzero]
  exact hasDerivAt_idealLogSeries K a ha 0 hs

theorem iteratedDeriv_idealDirichletSeries (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (idealDirichletSeries K a) s = idealLogSeries K a k s := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    have heq : iteratedDeriv k (idealDirichletSeries K a) =ᶠ[𝓝 s] idealLogSeries K a k := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
        with z hz
      exact ih hz
    rw [iteratedDeriv_succ, heq.deriv_eq, deriv_idealLogSeries K a ha k hs]

theorem analyticAt_idealLogSeries (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (idealLogSeries K a k) s := by
  have hd : DifferentiableOn ℂ (idealLogSeries K a k) {z : ℂ | 1 < z.re} :=
    fun z hz => (hasDerivAt_idealLogSeries K a ha k hz).differentiableAt.differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

/-- Log weights commute with the exact coefficient twist, preserving the sign s - it. -/
theorem idealLogTerm_normTwist (a : NonzeroIdeal K → ℂ) (k : ℕ) (t : ℝ)
    (s : ℂ) (I : NonzeroIdeal K) :
    idealLogTerm K (normTwistedCoefficients (idealNorm K) a t) k s I =
      idealLogTerm K a k (s - (t : ℂ) * Complex.I) I := by
  unfold idealLogTerm
  rw [dirichletTerm_normTwist (idealNorm K) a t s (idealNorm_pos K)]

theorem idealLogSeries_normTwist (a : NonzeroIdeal K → ℂ) (k : ℕ) (t : ℝ) (s : ℂ) :
    idealLogSeries K (normTwistedCoefficients (idealNorm K) a t) k s =
      idealLogSeries K a k (s - (t : ℂ) * Complex.I) :=
  tsum_congr (idealLogTerm_normTwist K a k t s)

/-- Actual higher derivatives of the twisted series agree with the shifted derivatives. -/
theorem iteratedDeriv_idealDirichletSeries_normTwist (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (idealDirichletSeries K (normTwistedCoefficients (idealNorm K) a t)) s =
      iteratedDeriv k (idealDirichletSeries K a) (s - (t : ℂ) * Complex.I) := by
  have hat : ∀ I, ‖normTwistedCoefficients (idealNorm K) a t I‖ ≤ 1 := by
    intro I
    rw [norm_normTwistedCoefficients (idealNorm K) a t I (idealNorm_pos K I)]
    exact ha I
  have hshift : 1 < (s - (t : ℂ) * Complex.I).re := by simpa using hs
  rw [iteratedDeriv_idealDirichletSeries K _ hat k hs,
    iteratedDeriv_idealDirichletSeries K a ha k hshift, idealLogSeries_normTwist]

end HeckeGeneral.Analysis
