/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeCancellationMellin
import PrimeCancellationContour
import PrimeCancellationDiskGeometry
import PrimeCancellationAux
import Mathlib.Tactic.GCongr

/-!
# Cancellation derived from zero-free analytic data

The central result is a weighted Dirichlet-sum estimate obtained by Mellin
inversion, a proved contour shift, and a proved logarithmic-derivative estimate.
It does not take a prime-sum estimate as a hypothesis.

The quantitative Mellin-window bound is an explicit input.  In the intended
application V(x)=W(x)/log(P*x); its *uniform finite-seminorm estimate* still has
to be supplied.  Smoothness alone is used here to justify inversion and
holomorphy, not silently substituted for a uniform family bound.
-/

noncomputable section
open Filter MeasureTheory Set Complex
open scoped Topology BigOperators ContDiff

namespace PrimeCancellation.Analytic

/-- Explicit analytic data for an entire function, independent of any moment model. -/
structure ZeroFreeData (F : ℂ → ℂ) (β : ℝ) where
  C : ℝ
  Q : ℝ
  p : ℝ
  k : ℕ
  A : ℝ
  C_one : 1 ≤ C
  Q_one : 1 ≤ Q
  p_nonneg : 0 ≤ p
  entire : Differentiable ℂ F
  zeroFree : ∀ w : ℂ, β < w.re → F w ≠ 0
  centerLog : ℝ → ℂ
  centerLog_exp : ∀ t : ℝ, exp (centerLog t) = F ((2 : ℂ) + t * I)
  centerLog_bound : ∀ t : ℝ, ‖centerLog t‖ ≤ A
  polynomial : ∀ w : ℂ, 1 / 2 ≤ w.re →
    ‖F w‖ ≤ C * Q ^ p * (2 + |w.im|) ^ k

variable {F : ℂ → ℂ} {β : ℝ}

def heightConstant (d : ZeroFreeData F β) : ℝ :=
  1 + Real.log d.C + d.p * Real.log d.Q + d.A

def heightWeight (d : ZeroFreeData F β) (t : ℝ) : ℝ :=
  heightConstant d + (d.k : ℝ) * Real.log (4 + |t|)

theorem heightConstant_nonneg (d : ZeroFreeData F β) : 0 ≤ heightConstant d := by
  have hA : 0 ≤ d.A := (norm_nonneg (d.centerLog 0)).trans (d.centerLog_bound 0)
  have hC := Real.log_nonneg d.C_one
  have hQ := Real.log_nonneg d.Q_one
  have hp := d.p_nonneg
  unfold heightConstant
  positivity

theorem heightWeight_nonneg (d : ZeroFreeData F β) (t : ℝ) : 0 ≤ heightWeight d t := by
  have h0 := heightConstant_nonneg d
  have hlog : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  unfold heightWeight
  positivity

theorem logDerivative_bound (d : ZeroFreeData F β) {δ σ t : ℝ}
    (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 1) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hσ : β + δ ≤ σ) (hσ' : σ ≤ 2) :
    ‖-deriv F ((σ : ℂ) + t * I) / F ((σ : ℂ) + t * I)‖ ≤
      48 * heightWeight d t / δ ^ 2 := by
  have h := PrimeCancellationDiskGeometry.norm_logDeriv_le_of_halfPlane_polynomial
    (F := F) (m := d.centerLog t) d.k hβ hβ' hδ hδ' hσ hσ'
    d.C_one d.Q_one d.p_nonneg d.entire d.zeroFree
    (d.centerLog_exp t) (d.centerLog_bound t) d.polynomial
  simpa only [PrimeCancellationDiskGeometry.verticalPoint, neg_div, norm_neg,
    heightWeight, heightConstant, add_assoc, add_left_comm, add_comm] using h

def integrand (V : ℝ → ℂ) (F : ℂ → ℂ) (P : ℝ) (s : ℂ) : ℂ :=
  mellin V s * (P : ℂ) ^ s * (-deriv F s / F s)

theorem integrand_differentiableAt (d : ZeroFreeData F β)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (hV : Continuous V)
    (P : ℝ) (hP : 0 < P) {s : ℂ} (hs : β < s.re) :
    DifferentiableAt ℂ (integrand V F P) s := by
  have hlog : DifferentiableAt ℂ (fun z => -deriv F z / F z) s :=
    ((d.entire.analyticAt s).deriv.neg.div (d.entire.analyticAt s)
      (d.zeroFree s hs)).differentiableAt
  exact ((Mellin.compact_mellin_differentiable V a b ha hsupp hV s).mul
    (differentiableAt_id.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hP.ne')))).mul hlog

theorem integrand_norm (V : ℝ → ℂ) (F : ℂ → ℂ) (P σ t : ℝ) (hP : 0 < P) :
    ‖integrand V F P ((σ : ℂ) + t * I)‖ =
      ‖mellin V ((σ : ℂ) + t * I)‖ * P ^ σ *
        ‖-deriv F ((σ : ℂ) + t * I) / F ((σ : ℂ) + t * I)‖ := by
  simp only [integrand, norm_mul, Mellin.positive_cpow_vertical_norm P σ t hP]

/-- A transparent quantitative window condition; it contains no arithmetic sum. -/
def WindowControl (d : ZeroFreeData F β) (V : ℝ → ℂ) (l Cw : ℝ) : Prop :=
  ∀ σ ∈ Icc l 2, ∀ t : ℝ,
    ‖mellin V ((σ : ℂ) + t * I)‖ * heightWeight d t ≤ Cw / (1 + t ^ 2)

theorem integrand_bound (d : ZeroFreeData F β)
    (V : ℝ → ℂ) (δ P Cw σ t : ℝ)
    (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 1) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hP : 0 < P) (hσ : σ ∈ Icc (β + δ) 2)
    (hwindow : WindowControl d V (β + δ) Cw) :
    ‖integrand V F P ((σ : ℂ) + t * I)‖ ≤
      (48 * Cw / δ ^ 2 * P ^ σ) / (1 + t ^ 2) := by
  rw [integrand_norm V F P σ t hP]
  calc
    _ ≤ (‖mellin V ((σ : ℂ) + t * I)‖ * P ^ σ) *
        (48 * heightWeight d t / δ ^ 2) :=
      mul_le_mul_of_nonneg_left (logDerivative_bound d hβ hβ' hδ hδ' hσ.1 hσ.2)
        (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hP.le _))
    _ = (48 / δ ^ 2 * P ^ σ) *
        (‖mellin V ((σ : ℂ) + t * I)‖ * heightWeight d t) := by ring
    _ ≤ (48 / δ ^ 2 * P ^ σ) * (Cw / (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left (hwindow σ hσ t) (by positivity)
    _ = _ := by ring

theorem integrand_strip_bound (d : ZeroFreeData F β)
    (V : ℝ → ℂ) (δ P Cw : ℝ)
    (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 1) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hP : 1 ≤ P) (hCw : 0 ≤ Cw)
    (hwindow : WindowControl d V (β + δ) Cw) :
    ∀ σ ∈ Icc (β + δ) 2, ∀ t : ℝ,
      ‖integrand V F P ((σ : ℂ) + t * I)‖ ≤
        (48 * Cw / δ ^ 2 * P ^ (2 : ℝ)) / (1 + t ^ 2) := by
  intro σ hσ t
  refine (integrand_bound d V δ P Cw σ t hβ hβ' hδ hδ'
    (zero_lt_one.trans_le hP) hσ hwindow).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hP hσ.2) (by positivity)

/-- Exact shifted Mellin formula for a general absolutely convergent Dirichlet
series which is the negative logarithmic derivative of F on Re(s)>1. -/
theorem weighted_sum_eq_shifted {ι : Type*} [Countable ι]
    (d : ZeroFreeData F β) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖ * (r i) ^ (-(2 : ℝ))))
    (heuler : ∀ s : ℂ, 1 < s.re →
      (∑' i, c i * (r i : ℂ) ^ (-s)) = -deriv F s / F s)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (δ P Cw : ℝ) (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 1)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hP : 1 ≤ P) (hCw : 0 ≤ Cw)
    (hwindow : WindowControl d V (β + δ) Cw) :
    (∑' i, c i * V (r i / P)) = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, integrand V F P (((β + δ : ℝ) : ℂ) + t * I) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hab : β + δ ≤ 2 := by linarith
  have hshift := Contour.integral_eq_of_strip_quadratic_decay
    (integrand V F P) (β + δ) 2 (48 * Cw / δ ^ 2 * P ^ (2 : ℝ)) hab
    (fun z hz _ => integrand_differentiableAt d V a b ha hsupp hV.continuous
      P hPpos (by linarith))
    (integrand_strip_bound d V δ P Cw hβ hβ' hδ hδ' hP hCw hwindow)
  rw [Mellin.weighted_mellin_inversion r hr c 2 hc V a b ha hsupp hV P hPpos]
  rw [hshift]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [heuler _ (by norm_num)]
  rfl

/-- A genuine cancellation estimate, obtained from zero-free data and a
quantitative Mellin-window bound. The constant 24 is 48*pi/(2*pi). -/
theorem norm_weighted_sum_le {ι : Type*} [Countable ι]
    (d : ZeroFreeData F β) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖ * (r i) ^ (-(2 : ℝ))))
    (heuler : ∀ s : ℂ, 1 < s.re →
      (∑' i, c i * (r i : ℂ) ^ (-s)) = -deriv F s / F s)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (δ P Cw : ℝ) (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 1)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hP : 1 ≤ P) (hCw : 0 ≤ Cw)
    (hwindow : WindowControl d V (β + δ) Cw) :
    ‖∑' i, c i * V (r i / P)‖ ≤ 24 * Cw / δ ^ 2 * P ^ (β + δ) := by
  rw [weighted_sum_eq_shifted d r hr c hc heuler V a b ha hsupp hV
    δ P Cw hβ hβ' hδ hδ' hP hCw hwindow, norm_mul]
  have hfac : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    simp [abs_of_pos Real.pi_pos]
  rw [hfac]
  have hbound := Contour.norm_vertical_integral_le (integrand V F P) (β + δ)
    (48 * Cw / δ ^ 2 * P ^ (β + δ))
    (fun t => integrand_bound d V δ P Cw (β + δ) t hβ hβ' hδ hδ'
      (zero_lt_one.trans_le hP) ⟨le_rfl, by linarith⟩ hwindow)
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((48 * Cw / δ ^ 2 * P ^ (β + δ)) * Real.pi) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by field_simp; ring

end PrimeCancellation.Analytic

#print axioms PrimeCancellation.Analytic.heightConstant_nonneg
#print axioms PrimeCancellation.Analytic.heightWeight_nonneg
#print axioms PrimeCancellation.Analytic.logDerivative_bound
#print axioms PrimeCancellation.Analytic.integrand_differentiableAt
#print axioms PrimeCancellation.Analytic.integrand_norm
#print axioms PrimeCancellation.Analytic.integrand_bound
#print axioms PrimeCancellation.Analytic.integrand_strip_bound
#print axioms PrimeCancellation.Analytic.weighted_sum_eq_shifted
#print axioms PrimeCancellation.Analytic.norm_weighted_sum_le
