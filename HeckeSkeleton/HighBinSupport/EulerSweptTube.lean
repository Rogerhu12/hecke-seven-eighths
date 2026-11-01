import HeckeGeneral.Analysis.RowEulerRational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Regular Euler bounds on an open tube surrounding the entire high-bin move

The rational function is imported verbatim from the supplied project.
The proof below adapts its eleven-monomial estimate to an OPEN neighbourhood
of the swept strip, allowing negative Re(w) at a = 1.
No arithmetic Fourier calibration is assumed or asserted here.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinContinuation

open HeckeGeneral.ThetaSkeleton.Physical

private theorem sweptTube_norm_mul {q x y : ℝ} {X Y : ℂ}
    (hq : 0 < q) (hX : ‖X‖ ≤ q ^ x) (hY : ‖Y‖ ≤ q ^ y) :
    ‖X * Y‖ ≤ q ^ (x + y) := by
  rw [norm_mul, Real.rpow_add hq]
  exact mul_le_mul hX hY (norm_nonneg _) (Real.rpow_nonneg hq.le _)

private theorem sweptTube_norm_add {X Y : ℂ} {x y : ℝ}
    (hX : ‖X‖ ≤ x) (hY : ‖Y‖ ≤ y) : ‖X + Y‖ ≤ x + y :=
  (norm_add_le _ _).trans (add_le_add hX hY)

/-- A fixed, strictly positive denominator margin, independent of the bin,
the small parameter, the prime, and all imaginary parts. -/
def sweptTubeEulerMargin : ℝ :=
  (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) * (1 - (1 / 2 : ℝ))

theorem sweptTubeEulerMargin_pos : 0 < sweptTubeEulerMargin := by
  unfold sweptTubeEulerMargin
  have h : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact mul_pos (by linarith) (by norm_num)

/-- The eleven actual error monomials are bounded uniformly on the entire
bin range.  In particular, there is no hypothesis `‖W‖ ≤ 1`. -/
theorem rowEulerRationalValue_sweptTube_bound
    {q a e : ℝ} (hq : 2 ≤ q) (ha : 51 / 100 ≤ a) (ha' : a ≤ 1)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000) (V W D E : ℂ)
    (hV : ‖V‖ ≤ q ^ (-(51 / 25 : ℝ) + 6 * e))
    (hW : ‖W‖ ≤ q ^ (a - 1 + 7 * e))
    (hD : ‖D‖ ≤ q ^ (-a - 15 * e))
    (hE : ‖E‖ ≤ q ^ (49 / 25 - 6 * a - 84 * e)) :
    ‖rowEulerRationalValue (q : ℂ) (q : ℂ)⁻¹ V W D E - 1‖ ≤
      (11 / sweptTubeEulerMargin) * q ^ (-1 - 8 * e) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hqN : ‖(q : ℂ)‖ ≤ q ^ (1 : ℝ) := by
    simp [Complex.norm_real, Real.norm_of_nonneg hq0.le]
  have hqmN : ‖(q : ℂ) - 1‖ ≤ q ^ (1 : ℝ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : 0 ≤ q - 1), Real.rpow_one]
    linarith
  have hqiN : ‖(q : ℂ)⁻¹‖ ≤ q ^ (0 : ℝ) := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hq0.le, Real.rpow_zero]
    exact inv_le_one_of_one_le₀ hq1
  have hDd : ‖D‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖D‖ ≤ q ^ (-a - 15 * e) := hD
      _ ≤ q ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      _ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
  have hEe : ‖E‖ ≤ (1 / 2 : ℝ) := by
    have hpow : q ^ (49 / 25 - 6 * a - 84 * e) ≤ q ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    refine hE.trans (hpow.trans ?_)
    have hi := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2)
      hq (by norm_num : (-1 : ℝ) ≤ 0)
    simpa only [Real.rpow_neg_one, one_div] using hi
  have hdlt : ‖D‖ < 1 := hDd.trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have helt : ‖E‖ < 1 := lt_of_le_of_lt hEe (by norm_num)
  have h1D : 1 - D ≠ 0 := by
    intro h
    have hD1 : D = 1 := (sub_eq_zero.mp h).symm
    simpa [hD1] using hdlt
  have h1E : 1 - E ≠ 0 := by
    intro h
    have hE1 : E = 1 := (sub_eq_zero.mp h).symm
    simpa [hE1] using helt
  have hden : sweptTubeEulerMargin ≤ ‖1 - E‖ * ‖1 - D‖ := by
    have hEL : 1 - (1 / 2 : ℝ) ≤ ‖1 - E‖ := by
      have h := norm_sub_norm_le (1 : ℂ) E
      rw [norm_one] at h
      linarith
    have hDL : 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ‖1 - D‖ := by
      have h := norm_sub_norm_le (1 : ℂ) D
      rw [norm_one] at h
      linarith
    unfold sweptTubeEulerMargin
    rw [mul_comm]
    have hgap : 0 ≤ 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hsmall : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
      linarith
    exact mul_le_mul hEL hDL hgap (norm_nonneg _)
  let B : ℝ := q ^ (-1 - 8 * e)
  have lower {X : ℂ} {b : ℝ} (hX : ‖X‖ ≤ q ^ b)
      (hb : b ≤ -1 - 8 * e) : ‖X‖ ≤ B :=
    hX.trans (Real.rpow_le_rpow_of_exponent_le hq1 hb)
  have hWV := sweptTube_norm_mul hq0 hW hV
  have hEq := sweptTube_norm_mul hq0 hE hqiN
  have hEqW := sweptTube_norm_mul hq0 hEq hW
  have hEW := sweptTube_norm_mul hq0 hE hW
  have hEWW := sweptTube_norm_mul hq0 hEW hW
  have hEWWV := sweptTube_norm_mul hq0 hEWW hV
  have hDV := sweptTube_norm_mul hq0 hD hV
  have hDW := sweptTube_norm_mul hq0 hD hW
  have hDq := sweptTube_norm_mul hq0 hD hqN
  have hDqW := sweptTube_norm_mul hq0 hDq hW
  have hDqWV := sweptTube_norm_mul hq0 hDqW hV
  have hDqm := sweptTube_norm_mul hq0 hD hqmN
  have hDqmW := sweptTube_norm_mul hq0 hDqm hW
  have hDqmWW := sweptTube_norm_mul hq0 hDqmW hW
  have hDqmWWV := sweptTube_norm_mul hq0 hDqmWW hV
  have hDE := sweptTube_norm_mul hq0 hD hE
  have h1 : ‖-(W * V)‖ ≤ B := by
    rw [norm_neg]
    exact lower hWV (by linarith)
  have h2 : ‖E‖ ≤ B := lower hE (by linarith)
  have h3 : ‖-(E * (q : ℂ)⁻¹)‖ ≤ B := by
    rw [norm_neg]
    exact lower hEq (by linarith)
  have h4 : ‖E * (q : ℂ)⁻¹ * W‖ ≤ B := lower hEqW (by linarith)
  have h5 : ‖-(E * W * W)‖ ≤ B := by
    rw [norm_neg]
    exact lower hEWW (by linarith)
  have h6 : ‖E * W * W * V‖ ≤ B := lower hEWWV (by linarith)
  have h7 : ‖D * V‖ ≤ B := lower hDV (by linarith)
  have h8 : ‖D * W‖ ≤ B := lower hDW (by linarith)
  have h9 : ‖-(D * (q : ℂ) * W * V)‖ ≤ B := by
    rw [norm_neg]
    exact lower hDqWV (by linarith)
  have h10 : ‖D * ((q : ℂ) - 1) * W * W * V‖ ≤ B :=
    lower hDqmWWV (by linarith)
  have h11 : ‖-(D * E)‖ ≤ B := by
    rw [norm_neg]
    exact lower hDE (by linarith)
  have hsum := sweptTube_norm_add
    (sweptTube_norm_add
    (sweptTube_norm_add
    (sweptTube_norm_add
    (sweptTube_norm_add
    (sweptTube_norm_add
    (sweptTube_norm_add
    (sweptTube_norm_add
    (sweptTube_norm_add
    (sweptTube_norm_add h1 h2) h3) h4) h5) h6) h7) h8) h9) h10) h11
  have hnum :
      ‖-W * V + E * (1 - (q : ℂ)⁻¹ + (q : ℂ)⁻¹ * W - W ^ 2 + W ^ 2 * V) +
        D * (V + W - (q : ℂ) * W * V + ((q : ℂ) - 1) * W ^ 2 * V - E)‖ ≤
        11 * B := by
    convert hsum using 1
    · congr 1
      ring
    · ring
  rw [rowEulerRationalValue_sub_one _ _ _ _ _ _ h1E h1D, norm_div, norm_mul]
  exact (div_le_div₀ (by positivity) hnum sweptTubeEulerMargin_pos hden).trans
    (le_of_eq (by dsimp [B]; ring))


#print axioms sweptTubeEulerMargin_pos
#print axioms rowEulerRationalValue_sweptTube_bound
end HeckeSkeleton.HighBinContinuation
