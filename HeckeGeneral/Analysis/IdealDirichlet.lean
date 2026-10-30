import HeckeGeneral.Analysis.IdealSummability
import HeckeGeneral.Analysis.DirichletNormShift
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Dirichlet series over actual nonzero integral ideals

The convergence proof uses the actual number-field ideal-counting majorant.
The coefficients in this file are arbitrary bounded functions on ideals;
their identification with an idèle class character is a separate construction.
Holomorphy is proved only in the half-plane of absolute convergence.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField Ideal
open scoped nonZeroDivisors Topology

variable (K : Type*) [Field K] [NumberField K]

abbrev NonzeroIdeal := (Ideal (𝓞 K))⁰

def idealNorm (I : NonzeroIdeal K) : ℝ := absNorm I.val

theorem idealNorm_pos (I : NonzeroIdeal K) : 0 < idealNorm K I :=
  Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors I)

theorem one_le_idealNorm (I : NonzeroIdeal K) : 1 ≤ idealNorm K I := by
  change (1 : ℝ) ≤ (absNorm I.val : ℝ)
  exact_mod_cast Nat.succ_le_iff.mpr (Ideal.absNorm_pos_of_nonZeroDivisors I)

/-- The ideal-indexed Dirichlet series, with coefficients kept explicit. -/
def idealDirichletSeries (a : NonzeroIdeal K → ℂ) (s : ℂ) : ℂ :=
  dirichletSeries (idealNorm K) a s

theorem absolutelySummable_idealDirichlet (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I => ‖dirichletTerm (idealNorm K) a s I‖) :=
  absolutelySummable_dirichletTerm_of_unit_coefficients (idealNorm K) a s
    (idealNorm_pos K) ha (summable_nonzeroIdeal_norm_rpow K hs)

theorem summable_idealDirichlet (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (dirichletTerm (idealNorm K) a s) :=
  (absolutelySummable_idealDirichlet K a ha hs).of_norm

theorem hasSum_idealDirichlet (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (dirichletTerm (idealNorm K) a s) (idealDirichletSeries K a s) :=
  (summable_idealDirichlet K a ha hs).hasSum

theorem idealDirichletSeries_normTwist (a : NonzeroIdeal K → ℂ) (t : ℝ) (s : ℂ) :
    idealDirichletSeries K (normTwistedCoefficients (idealNorm K) a t) s =
      idealDirichletSeries K a (s - (t : ℂ) * Complex.I) :=
  dirichletSeries_normTwist (idealNorm K) a t s (idealNorm_pos K)

theorem differentiable_idealDirichletTerm (a : NonzeroIdeal K → ℂ) (I : NonzeroIdeal K) :
    Differentiable ℂ (fun s => dirichletTerm (idealNorm K) a s I) := by
  exact (differentiable_const (a I)).mul
    (differentiable_neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (idealNorm_pos K I).ne')))

theorem differentiableOn_idealDirichlet_above (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ (idealDirichletSeries K a) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun I : NonzeroIdeal K => idealNorm K I ^ (-σ))
    (summable_nonzeroIdeal_norm_rpow K hσ)
    (fun I => (differentiable_idealDirichletTerm K a I).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)
  intro I s hs
  rw [norm_dirichletTerm (idealNorm K) a s I (idealNorm_pos K I)]
  calc
    ‖a I‖ * idealNorm K I ^ (-s.re) ≤ 1 * idealNorm K I ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (ha I) (Real.rpow_nonneg (idealNorm_pos K I).le _)
    _ ≤ idealNorm K I ^ (-σ) := by
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_le (one_le_idealNorm K I) (neg_le_neg hs.le)

/-- Holomorphy on Re(s) > 1 follows from summable uniform bounds on smaller half-planes. -/
theorem differentiableAt_idealDirichlet (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (idealDirichletSeries K a) s := by
  have hopen : IsOpen {z : ℂ | (1 + s.re) / 2 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact (differentiableOn_idealDirichlet_above K a ha
    (show 1 < (1 + s.re) / 2 by linarith)).differentiableAt
      (hopen.mem_nhds (show (1 + s.re) / 2 < s.re by linarith))

theorem differentiableOn_idealDirichlet (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) :
    DifferentiableOn ℂ (idealDirichletSeries K a) {s : ℂ | 1 < s.re} :=
  fun _ hs => (differentiableAt_idealDirichlet K a ha hs).differentiableWithinAt

theorem analyticAt_idealDirichlet (a : NonzeroIdeal K → ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (idealDirichletSeries K a) s :=
  (differentiableOn_idealDirichlet K a ha).analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

end HeckeGeneral.Analysis
