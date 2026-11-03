import HeckeGeneral.Analysis.PhysicalProbeContours
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Uniform regular-prime Euler error on the full high-bin contour.  The bound
uses the cancelled rational correction, and allows both W = 1 and ‖W‖ > 1.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped ComplexConjugate

private theorem negativeStrip_norm_mul {q x y : ℝ} {X Y : ℂ}
    (hq : 0 < q) (hX : ‖X‖ ≤ q ^ x) (hY : ‖Y‖ ≤ q ^ y) :
    ‖X * Y‖ ≤ q ^ (x + y) := by
  rw [norm_mul, Real.rpow_add hq]
  exact mul_le_mul hX hY (norm_nonneg _) (Real.rpow_nonneg hq.le _)

private theorem negativeStrip_norm_add {X Y : ℂ} {x y : ℝ}
    (hX : ‖X‖ ≤ x) (hY : ‖Y‖ ≤ y) : ‖X + Y‖ ≤ x + y :=
  (norm_add_le _ _).trans (add_le_add hX hY)

/-- A fixed, strictly positive denominator margin, independent of the bin,
the small parameter, the prime, and all imaginary parts. -/
def negativeStripEulerMargin : ℝ :=
  (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) * (1 - (1 / 2 : ℝ))

theorem negativeStripEulerMargin_pos : 0 < negativeStripEulerMargin := by
  unfold negativeStripEulerMargin
  have h : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact mul_pos (by linarith) (by norm_num)

/-- The eleven actual error monomials are bounded uniformly on the entire
bin range.  In particular, there is no hypothesis `‖W‖ ≤ 1`. -/
theorem rowEulerRationalValue_negativeStrip_bound
    {q a e : ℝ} (hq : 2 ≤ q) (ha : 51 / 100 ≤ a) (ha' : a ≤ 1)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000) (V W D E : ℂ)
    (hV : ‖V‖ ≤ q ^ (-(51 / 25 : ℝ)))
    (hW : ‖W‖ ≤ q ^ (a - 1 + 6 * e))
    (hD : ‖D‖ ≤ q ^ (-a - 16 * e))
    (hE : ‖E‖ ≤ q ^ (49 / 25 - 6 * a - 96 * e)) :
    ‖rowEulerRationalValue (q : ℂ) (q : ℂ)⁻¹ V W D E - 1‖ ≤
      (11 / negativeStripEulerMargin) * q ^ (-1 - 10 * e) := by
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
      ‖D‖ ≤ q ^ (-a - 16 * e) := hD
      _ ≤ q ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      _ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
  have hEe : ‖E‖ ≤ (1 / 2 : ℝ) := by
    have hpow : q ^ (49 / 25 - 6 * a - 96 * e) ≤ q ^ (-1 : ℝ) :=
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
  have hden : negativeStripEulerMargin ≤ ‖1 - E‖ * ‖1 - D‖ := by
    have hEL : 1 - (1 / 2 : ℝ) ≤ ‖1 - E‖ := by
      have h := norm_sub_norm_le (1 : ℂ) E
      rw [norm_one] at h
      linarith
    have hDL : 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ‖1 - D‖ := by
      have h := norm_sub_norm_le (1 : ℂ) D
      rw [norm_one] at h
      linarith
    unfold negativeStripEulerMargin
    rw [mul_comm]
    have hgap : 0 ≤ 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hsmall : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
      linarith
    exact mul_le_mul hEL hDL hgap (norm_nonneg _)
  let B : ℝ := q ^ (-1 - 10 * e)
  have lower {X : ℂ} {b : ℝ} (hX : ‖X‖ ≤ q ^ b)
      (hb : b ≤ -1 - 10 * e) : ‖X‖ ≤ B :=
    hX.trans (Real.rpow_le_rpow_of_exponent_le hq1 hb)
  have hWV := negativeStrip_norm_mul hq0 hW hV
  have hEq := negativeStrip_norm_mul hq0 hE hqiN
  have hEqW := negativeStrip_norm_mul hq0 hEq hW
  have hEW := negativeStrip_norm_mul hq0 hE hW
  have hEWW := negativeStrip_norm_mul hq0 hEW hW
  have hEWWV := negativeStrip_norm_mul hq0 hEWW hV
  have hDV := negativeStrip_norm_mul hq0 hD hV
  have hDW := negativeStrip_norm_mul hq0 hD hW
  have hDq := negativeStrip_norm_mul hq0 hD hqN
  have hDqW := negativeStrip_norm_mul hq0 hDq hW
  have hDqWV := negativeStrip_norm_mul hq0 hDqW hV
  have hDqm := negativeStrip_norm_mul hq0 hD hqmN
  have hDqmW := negativeStrip_norm_mul hq0 hDqm hW
  have hDqmWW := negativeStrip_norm_mul hq0 hDqmW hW
  have hDqmWWV := negativeStrip_norm_mul hq0 hDqmWW hV
  have hDE := negativeStrip_norm_mul hq0 hD hE
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
  have hsum := negativeStrip_norm_add
    (negativeStrip_norm_add
    (negativeStrip_norm_add
    (negativeStrip_norm_add
    (negativeStrip_norm_add
    (negativeStrip_norm_add
    (negativeStrip_norm_add
    (negativeStrip_norm_add
    (negativeStrip_norm_add
    (negativeStrip_norm_add h1 h2) h3) h4) h5) h6) h7) h8) h9) h10) h11
  have hnum :
      ‖-W * V + E * (1 - (q : ℂ)⁻¹ + (q : ℂ)⁻¹ * W - W ^ 2 + W ^ 2 * V) +
        D * (V + W - (q : ℂ) * W * V + ((q : ℂ) - 1) * W ^ 2 * V - E)‖ ≤
        11 * B := by
    convert hsum using 1
    · congr 1
      ring
    · ring
  rw [rowEulerRationalValue_sub_one _ _ _ _ _ _ h1E h1D, norm_div, norm_mul]
  exact (div_le_div₀ (by positivity) hnum negativeStripEulerMargin_pos hden).trans
    (le_of_eq (by dsimp [B]; ring))

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Actual regular-prime correction on Re s=a+16e, Re w=1-a-6e,
Re z=17/50.  All characters are allowed, and no avoidance of w=0 is used. -/
theorem localRowCorrection_negativeStrip_bound (P : ProbeData K S)
    (ψ χ : HeckeCharacter K) (p : ExteriorPrime K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha' : a ≤ 1)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000) (s w z : ℂ)
    (hs : s.re = a + 16 * e) (hw : w.re = 1 - a - 6 * e)
    (hz : z.re = 17 / 50) :
    ‖localRowCorrection K S P ψ χ p s w z - 1‖ ≤
      (11 / negativeStripEulerMargin) *
        (p.val.asIdeal.absNorm : ℝ) ^ (-1 - 10 * e) := by
  let q : ℝ := (p.val.asIdeal.absNorm : ℝ)
  have hq : 2 ≤ q := by
    have h : 2 ≤ p.val.asIdeal.absNorm := one_lt_primeIdeal_absNorm K p.val
    change (2 : ℝ) ≤ (p.val.asIdeal.absNorm : ℝ)
    exact_mod_cast h
  have hq0 : 0 < q := by linarith
  have hcast : (q : ℂ) = (p.val.asIdeal.absNorm : ℂ) := by simp [q]
  have hpow (v : ℂ) : ‖(p.val.asIdeal.absNorm : ℂ) ^ v‖ = q ^ v.re := by
    rw [← hcast, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  have hV : ‖(p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)‖ ≤
      q ^ (-(51 / 25 : ℝ)) := by
    rw [hpow]
    have hx : (-6 * z).re = -(51 / 25 : ℝ) := by
      simp [Complex.mul_re, hz]
      <;> norm_num
    rw [hx]
  have hW : ‖primeCoefficient K χ p.val *
      (p.val.asIdeal.absNorm : ℂ) ^ (-w)‖ ≤ q ^ (a - 1 + 6 * e) := by
    rw [norm_mul, hpow]
    have hx : (-w).re = a - 1 + 6 * e := by
      simp only [Complex.neg_re, hw]
      ring
    rw [hx]
    simpa using mul_le_mul_of_nonneg_right (norm_primeCoefficient_le_one K χ p.val)
      (Real.rpow_nonneg hq0.le (a - 1 + 6 * e))
  have hD : ‖primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) *
      (p.val.asIdeal.absNorm : ℂ) ^ (-s)‖ ≤ q ^ (-a - 16 * e) := by
    rw [norm_mul, norm_mul, Complex.norm_conj, hpow]
    have hc : ‖primeCoefficient K ψ p.val‖ * ‖primeCoefficient K χ p.val‖ ≤ 1 := by
      exact mul_le_one₀ (norm_primeCoefficient_le_one K ψ p.val)
        (norm_nonneg _) (norm_primeCoefficient_le_one K χ p.val)
    have hx : (-s).re = -a - 16 * e := by
      simp only [Complex.neg_re, hs]
      ring
    rw [hx]
    simpa using mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hq0.le _)
  have hE : ‖primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6 *
      (p.val.asIdeal.absNorm : ℂ) ^ (4 - 6 * s) *
      (p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)‖ ≤
      q ^ (49 / 25 - 6 * a - 96 * e) := by
    rw [norm_mul, norm_mul, norm_pow, hpow, hpow]
    have hc : ‖primeCoefficient K (thetaPeriod K S P ψ) p.val‖ ^ 6 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_primeCoefficient_le_one K _ p.val)
    calc
      _ ≤ 1 * q ^ (4 - 6 * s).re * q ^ (-6 * z).re :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hq0.le _))
          (Real.rpow_nonneg hq0.le _)
      _ = q ^ ((4 - 6 * s).re + (-6 * z).re) := by
        rw [one_mul, ← Real.rpow_add hq0]
      _ = q ^ (49 / 25 - 6 * a - 96 * e) := by
        congr 1
        simp [Complex.mul_re, hs, hz]
        <;> ring
  unfold localRowCorrection
  dsimp only
  simpa only [hcast] using
    (rowEulerRationalValue_negativeStrip_bound hq ha ha' he he' _ _ _ _ hV hW hD hE)

end HeckeGeneral.ThetaSkeleton.Physical
