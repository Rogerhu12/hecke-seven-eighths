import HeckeGeneral.Analysis.IdealDerivativeSmoothing
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Actual ideal-indexed Taylor expansions

The two-index exponential expansion is absolutely summable when the radius
does not reach Re(s)=1. Its norm sum is controlled by the actual ideal norm
majorant at Re(s)-‖h‖. This proves the exchange of ideal sums and exponential
coefficients directly, rather than inferring convergence from a formal Taylor
identity. The same calculation gives explicit factorial derivative bounds.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

/-- A factorial logarithmic bound, with an explicit loss ε in the real exponent. -/
theorem logPower_rpow_factorial_bound {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε)
    (k : ℕ) (σ : ℝ) :
    Real.log x ^ k * x ^ (-σ) ≤
      ((k.factorial : ℝ) / ε ^ k) * x ^ (ε - σ) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hfact : 0 < (k.factorial : ℝ) := Nat.cast_pos.mpr k.factorial_pos
  have hp := Real.pow_div_factorial_le_exp (ε * Real.log x)
    (mul_nonneg hε.le (Real.log_nonneg hx)) k
  rw [div_le_iff₀ hfact, mul_pow] at hp
  have hexp : Real.exp (ε * Real.log x) = x ^ ε := by
    rw [Real.rpow_def_of_pos hxpos, mul_comm]
  rw [hexp] at hp
  have hlog : Real.log x ^ k ≤ ((k.factorial : ℝ) / ε ^ k) * x ^ ε := by
    apply (mul_le_mul_iff_right₀ (pow_pos hε k)).mp
    calc
      ε ^ k * Real.log x ^ k ≤ x ^ ε * (k.factorial : ℝ) := hp
      _ = ε ^ k * (((k.factorial : ℝ) / ε ^ k) * x ^ ε) := by
        field_simp
  calc
    _ ≤ (((k.factorial : ℝ) / ε ^ k) * x ^ ε) * x ^ (-σ) :=
      mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hxpos.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hxpos]
      congr 2

theorem idealLogTerm_factorial_bound (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {s : ℂ} {τ ε : ℝ}
    (hε : 0 < ε) (hs : τ + ε ≤ s.re) (I : NonzeroIdeal K) :
    ‖idealLogTerm K a k s I‖ ≤
      ((k.factorial : ℝ) / ε ^ k) * idealNorm K I ^ (-τ) := by
  apply (norm_idealLogTerm_le K a ha k s I).trans
  apply (logPower_rpow_factorial_bound (one_le_idealNorm K I) hε k s.re).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (one_le_idealNorm K I) (by linarith))
    (by positivity)

/-- Quantitative bounds on all derivatives with a genuine ideal majorant constant. -/
theorem norm_idealLogSeries_factorial_le (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (k : ℕ) {s : ℂ} {τ ε : ℝ}
    (hτ : 1 < τ) (hε : 0 < ε) (hs : τ + ε ≤ s.re) :
    ‖idealLogSeries K a k s‖ ≤
      ((k.factorial : ℝ) / ε ^ k) * ∑' I, idealNorm K I ^ (-τ) := by
  have hsr : 1 < s.re := by linarith
  apply (norm_tsum_le_tsum_norm (absolutelySummable_idealLogTerm K a ha k hsr)).trans
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (idealLogTerm_factorial_bound K a ha k hε hs)
    (absolutelySummable_idealLogTerm K a ha k hsr)
    ((summable_nonzeroIdeal_norm_rpow K hτ).mul_left _)

theorem norm_iteratedDeriv_heckeLSeries_factorial_le
    (χ : HeckeGeneral.Characters.HeckeCharacter K) (k : ℕ) {s : ℂ} {τ ε : ℝ}
    (hτ : 1 < τ) (hε : 0 < ε) (hs : τ + ε ≤ s.re) :
    ‖iteratedDeriv k (heckeLSeries K χ) s‖ ≤
      ((k.factorial : ℝ) / ε ^ k) * ∑' I, idealNorm K I ^ (-τ) := by
  rw [iteratedDeriv_heckeLSeries K χ k (by linarith)]
  exact norm_idealLogSeries_factorial_le K _ (norm_heckeIdealCoefficient_le_one K χ) k
    hτ hε hs

def idealTaylorTerm (a : NonzeroIdeal K → ℂ) (s h : ℂ)
    (I : NonzeroIdeal K) (k : ℕ) : ℂ :=
  ((-(Real.log (idealNorm K I) : ℂ)) * h) ^ k / (k.factorial : ℂ) *
    dirichletTerm (idealNorm K) a s I

theorem idealTaylorTerm_eq_moment (a : NonzeroIdeal K → ℂ)
    (s h : ℂ) (I : NonzeroIdeal K) (k : ℕ) :
    idealTaylorTerm K a s h I k =
      (h ^ k / (k.factorial : ℂ)) * idealLogTerm K a k s I := by
  simp only [idealTaylorTerm, idealLogTerm, mul_pow]
  ring

theorem norm_idealTaylorTerm (a : NonzeroIdeal K → ℂ)
    (s h : ℂ) (I : NonzeroIdeal K) (k : ℕ) :
    ‖idealTaylorTerm K a s h I k‖ =
      (Real.log (idealNorm K I) * ‖h‖) ^ k / (k.factorial : ℝ) *
        ‖dirichletTerm (idealNorm K) a s I‖ := by
  simp only [idealTaylorTerm, norm_mul, norm_div, norm_pow, norm_neg,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (one_le_idealNorm K I)), Complex.norm_natCast]

theorem hasSum_norm_idealTaylorTerm (a : NonzeroIdeal K → ℂ)
    (s h : ℂ) (I : NonzeroIdeal K) :
    HasSum (fun k => ‖idealTaylorTerm K a s h I k‖)
      (Real.exp (Real.log (idealNorm K I) * ‖h‖) *
        ‖dirichletTerm (idealNorm K) a s I‖) := by
  simp_rw [norm_idealTaylorTerm]
  rw [Real.exp_eq_exp_ℝ]
  exact (NormedSpace.expSeries_div_hasSum_exp
    (Real.log (idealNorm K I) * ‖h‖)).mul_right _

theorem norm_idealTaylorTerm_sum_le (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s h : ℂ) (I : NonzeroIdeal K) :
    (∑' k, ‖idealTaylorTerm K a s h I k‖) ≤
      idealNorm K I ^ (-(s.re - ‖h‖)) := by
  rw [(hasSum_norm_idealTaylorTerm K a s h I).tsum_eq,
    norm_dirichletTerm (idealNorm K) a s I (idealNorm_pos K I)]
  have hexp : Real.exp (Real.log (idealNorm K I) * ‖h‖) = idealNorm K I ^ ‖h‖ :=
    (Real.rpow_def_of_pos (idealNorm_pos K I) _).symm
  rw [hexp]
  calc
    _ ≤ idealNorm K I ^ ‖h‖ * (1 * idealNorm K I ^ (-s.re)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (ha I) (Real.rpow_nonneg (idealNorm_pos K I).le _))
        (Real.rpow_nonneg (idealNorm_pos K I).le _)
    _ = _ := by
      rw [one_mul, ← Real.rpow_add (idealNorm_pos K I)]
      congr 1
      ring

/-- Genuine absolute convergence over actual ideals and Taylor indices. -/
theorem absolutelySummable_idealTaylorTerm (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) {s h : ℂ} (hr : 1 < s.re - ‖h‖) :
    Summable (fun p : NonzeroIdeal K × ℕ => ‖idealTaylorTerm K a s h p.1 p.2‖) := by
  rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
  constructor
  · intro I
    exact (hasSum_norm_idealTaylorTerm K a s h I).summable
  · exact Summable.of_nonneg_of_le
      (fun I => tsum_nonneg (fun k => norm_nonneg _))
      (norm_idealTaylorTerm_sum_le K a ha s h)
      (summable_nonzeroIdeal_norm_rpow K hr)

theorem hasSum_idealTaylorTerm (a : NonzeroIdeal K → ℂ)
    (s h : ℂ) (I : NonzeroIdeal K) :
    HasSum (idealTaylorTerm K a s h I) (dirichletTerm (idealNorm K) a (s + h) I) := by
  have hexp := (NormedSpace.expSeries_div_hasSum_exp
    ((-(Real.log (idealNorm K I) : ℂ)) * h)).mul_right
      (dirichletTerm (idealNorm K) a s I)
  rw [← Complex.exp_eq_exp_ℂ] at hexp
  have hvalue : Complex.exp ((-(Real.log (idealNorm K I) : ℂ)) * h) *
      dirichletTerm (idealNorm K) a s I = dirichletTerm (idealNorm K) a (s + h) I := by
    unfold dirichletTerm
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (idealNorm_pos K I).ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (idealNorm_pos K I).ne'),
      ← Complex.ofReal_log (idealNorm_pos K I).le]
    rw [mul_comm _ (a I * _), mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hvalue] at hexp
  exact hexp

theorem summable_idealTaylorCoefficients (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) {s h : ℂ} (hr : 1 < s.re - ‖h‖) :
    Summable (fun k => (h ^ k / (k.factorial : ℂ)) * idealLogSeries K a k s) := by
  have habs := absolutelySummable_idealTaylorTerm K a ha hr
  have hsum := habs.of_norm.prod_symm.prod
  convert hsum using 1
  funext k
  simp only [Prod.swap, idealTaylorTerm_eq_moment, idealLogSeries, tsum_mul_left]

/-- The actual Taylor sum has the expected coefficients and value. -/
theorem hasSum_idealDirichletSeries_taylor (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) {s h : ℂ} (hr : 1 < s.re - ‖h‖) :
    HasSum (fun k => (h ^ k / (k.factorial : ℂ)) * idealLogSeries K a k s)
      (idealDirichletSeries K a (s + h)) := by
  have hsum := (absolutelySummable_idealTaylorTerm K a ha hr).of_norm
  have heq : (∑' k, ∑' I, idealTaylorTerm K a s h I k) =
      ∑' I, ∑' k, idealTaylorTerm K a s h I k := hsum.tsum_comm
  have hcoeff : (∑' k, (h ^ k / (k.factorial : ℂ)) * idealLogSeries K a k s) =
      ∑' k, ∑' I, idealTaylorTerm K a s h I k := by
    simp only [idealTaylorTerm_eq_moment, idealLogSeries, tsum_mul_left]
  have hvalue : (∑' k, (h ^ k / (k.factorial : ℂ)) * idealLogSeries K a k s) =
      idealDirichletSeries K a (s + h) := by
    rw [hcoeff, heq]
    exact tsum_congr (fun I => (hasSum_idealTaylorTerm K a s h I).tsum_eq)
  exact hvalue ▸ (summable_idealTaylorCoefficients K a ha hr).hasSum

/-- The derivatives are the actual coefficients, inside the explicit convergence radius. -/
theorem hasSum_iteratedDeriv_idealDirichletSeries_taylor (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) {s h : ℂ} (hr : 1 < s.re - ‖h‖) :
    HasSum (fun k => (h ^ k / (k.factorial : ℂ)) *
      iteratedDeriv k (idealDirichletSeries K a) s) (idealDirichletSeries K a (s + h)) := by
  have hs : 1 < s.re := by linarith [norm_nonneg h]
  simp_rw [iteratedDeriv_idealDirichletSeries K a ha _ hs]
  exact hasSum_idealDirichletSeries_taylor K a ha hr

end HeckeGeneral.Analysis
