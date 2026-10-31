import HeckeSkeleton.HighBinSupport.EulerSweptTube
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp
/-!
# Actual phase-shaped regular Euler factors on the swept tube

The four monomials have the same formula as `localRowCorrection` in the
supplied project.  The three coefficients are only assumed to have norm at
most one.  In the arithmetic application they are chi(p), psi(p)conj(chi(p)),
and theta(p)^6.  There is no Fourier-to-Euler identification premise here.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinContinuation

open HeckeGeneral.ThetaSkeleton.Physical
open Set Filter
open scoped Topology BigOperators

/-- The original regular rational factor with its three bounded phases. -/
def phaseRowEuler (q : ℝ) (cW cD cE : ℂ) (s w z : ℂ) : ℂ :=
  rowEulerRationalValue (q : ℂ) (q : ℂ)⁻¹
    ((q : ℂ) ^ (-6 * z)) (cW * (q : ℂ) ^ (-w))
    (cD * (q : ℂ) ^ (-s))
    (cE * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ) ^ (-6 * z))

/-- An open neighbourhood of every vertical and horizontal face in the
high-bin s-move.  In particular its w half-plane contains the negative
line Re(w) = -6e when a = 1. -/
def sweptTube (a e : ℝ) : Set (ℂ × ℂ × ℂ) :=
  {v | a + 15 * e < v.1.re ∧ 1 - a - 7 * e < v.2.1.re ∧
    17 / 50 - e < v.2.2.re}

theorem sweptTube_isOpen (a e : ℝ) : IsOpen (sweptTube a e) := by
  unfold sweptTube
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
  · apply IsOpen.inter
    · exact isOpen_lt continuous_const
        (Complex.continuous_re.comp (continuous_fst.comp continuous_snd))
    · exact isOpen_lt continuous_const
        (Complex.continuous_re.comp (continuous_snd.comp continuous_snd))

theorem swept_contour_mem_tube {a e σ : ℝ} (he : 0 < e)
    (hs : a + 16 * e ≤ σ) (s w z : ℂ)
    (hσ : s.re = σ) (hw : w.re = 1 - a - 6 * e)
    (hz : z.re = 17 / 50) : (s, w, z) ∈ sweptTube a e := by
  change a + 15 * e < s.re ∧ 1 - a - 7 * e < w.re ∧ 17 / 50 - e < z.re
  rw [hσ, hw, hz]
  exact ⟨by linarith, by linarith, by linarith⟩

theorem initial_contour_mem_tube {a B e : ℝ} (haB : a ≤ B) (he : 0 < e)
    (s w z : ℂ) (hs : s.re = B + 20 * e)
    (hw : w.re = 1 - a - 6 * e) (hz : z.re = 17 / 50) :
    (s, w, z) ∈ sweptTube a e :=
  swept_contour_mem_tube he (by linarith) s w z hs hw hz

theorem phase_coordinate_bounds {q a e : ℝ} (hq : 2 ≤ q)
    (cW cD cE s w z : ℂ) (hW : ‖cW‖ ≤ 1) (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1)
    (hs : a + 15 * e ≤ s.re) (hw : 1 - a - 7 * e ≤ w.re)
    (hz : 17 / 50 - e ≤ z.re) :
    ‖(q : ℂ) ^ (-6 * z)‖ ≤ q ^ (-(51 / 25 : ℝ) + 6 * e) ∧
    ‖cW * (q : ℂ) ^ (-w)‖ ≤ q ^ (a - 1 + 7 * e) ∧
    ‖cD * (q : ℂ) ^ (-s)‖ ≤ q ^ (-a - 15 * e) ∧
    ‖cE * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ) ^ (-6 * z)‖ ≤
      q ^ (49 / 25 - 6 * a - 84 * e) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hp (v : ℂ) : ‖(q : ℂ) ^ v‖ = q ^ v.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hq0 v
  have hv : (-6 * z).re = -6 * z.re := by simp [Complex.mul_re]
  have heq : (4 - 6 * s).re = 4 - 6 * s.re := by simp [Complex.mul_re]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp, hv]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  · rw [norm_mul, hp, Complex.neg_re]
    calc
      ‖cW‖ * q ^ (-w.re) ≤ 1 * q ^ (-w.re) :=
        mul_le_mul_of_nonneg_right hW (Real.rpow_nonneg hq0.le _)
      _ ≤ q ^ (a - 1 + 7 * e) := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  · rw [norm_mul, hp, Complex.neg_re]
    calc
      ‖cD‖ * q ^ (-s.re) ≤ 1 * q ^ (-s.re) :=
        mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hq0.le _)
      _ ≤ q ^ (-a - 15 * e) := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  · rw [norm_mul, norm_mul, hp, hp, hv, heq]
    calc
      _ ≤ 1 * q ^ (4 - 6 * s.re) * q ^ (-6 * z.re) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hE (Real.rpow_nonneg hq0.le _))
          (Real.rpow_nonneg hq0.le _)
      _ = q ^ ((4 - 6 * s.re) + (-6 * z.re)) := by
        rw [one_mul, ← Real.rpow_add hq0]
      _ ≤ q ^ (49 / 25 - 6 * a - 84 * e) :=
        Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)

/-- The regular factor is controlled on the entire open tube, with a
strictly positive summability margin when e > 0. -/
theorem phaseRowEuler_sweptTube_bound {q a e : ℝ} (hq : 2 ≤ q)
    (ha : 51 / 100 ≤ a) (ha' : a ≤ 1) (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (cW cD cE : ℂ) (hW : ‖cW‖ ≤ 1) (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    ‖phaseRowEuler q cW cD cE v.1 v.2.1 v.2.2 - 1‖ ≤
      (11 / sweptTubeEulerMargin) * q ^ (-1 - 8 * e) := by
  obtain ⟨hV, hW', hD', hE'⟩ := phase_coordinate_bounds hq cW cD cE
    v.1 v.2.1 v.2.2 hW hD hE hv.1.le hv.2.1.le hv.2.2.le
  exact rowEulerRationalValue_sweptTube_bound hq ha ha' he he' _ _ _ _ hV hW' hD' hE'

/-- The two genuine rational denominators are nonzero throughout the tube. -/
theorem phaseRowEuler_denominators_ne_zero {q a e : ℝ} (hq : 2 ≤ q)
    (ha : 51 / 100 ≤ a) (he : 0 ≤ e)
    (cD cE s z : ℂ) (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1)
    (hs : a + 15 * e ≤ s.re) (hz : 17 / 50 - e ≤ z.re) :
    1 - cD * (q : ℂ) ^ (-s) ≠ 0 ∧
    1 - cE * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ) ^ (-6 * z) ≠ 0 := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 < q := by linarith
  have hp (v : ℂ) : ‖(q : ℂ) ^ v‖ = q ^ v.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hq0 v
  have hDs : ‖cD * (q : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, hp, Complex.neg_re]
    calc
      _ ≤ 1 * q ^ (-s.re) :=
        mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hq0.le _)
      _ < 1 := by
        rw [one_mul]
        exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have hEs : ‖cE * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ) ^ (-6 * z)‖ < 1 := by
    rw [norm_mul, norm_mul, hp, hp]
    calc
      _ ≤ 1 * q ^ (4 - 6 * s).re * q ^ (-6 * z).re :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hE (Real.rpow_nonneg hq0.le _))
          (Real.rpow_nonneg hq0.le _)
      _ = q ^ ((4 - 6 * s).re + (-6 * z).re) := by
        rw [one_mul, ← Real.rpow_add hq0]
      _ < 1 := by
        apply Real.rpow_lt_one_of_one_lt_of_neg hq1
        norm_num [Complex.mul_re]
        linarith
  constructor
  · intro hz0
    have hh : cD * (q : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hz0).symm
    rw [hh, norm_one] at hDs
    exact (lt_irrefl 1 hDs)
  · intro hz0
    have hh : cE * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ) ^ (-6 * z) = 1 :=
      (sub_eq_zero.mp hz0).symm
    rw [hh, norm_one] at hEs
    exact (lt_irrefl 1 hEs)

#print axioms phaseRowEuler_sweptTube_bound
#print axioms phaseRowEuler_denominators_ne_zero

end HeckeSkeleton.HighBinContinuation
