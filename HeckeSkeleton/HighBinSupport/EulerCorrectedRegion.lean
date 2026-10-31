import HeckeSkeleton.HighBinSupport.EulerSweptTube
/-!
# Corrected positive-w Euler region

The two mixed inequalities omitted from the original interface are made
explicit. The eleven actual monomials give a uniform positive summability
margin at each point of this region.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinContinuation
open HeckeGeneral.ThetaSkeleton.Physical

private theorem correctedRegion_norm_mul {q x y : ℝ} {X Y : ℂ}
    (hq : 0 < q) (hX : ‖X‖ ≤ q ^ x) (hY : ‖Y‖ ≤ q ^ y) :
    ‖X * Y‖ ≤ q ^ (x + y) := by
  rw [norm_mul, Real.rpow_add hq]
  exact mul_le_mul hX hY (norm_nonneg _) (Real.rpow_nonneg hq.le _)

private theorem correctedRegion_norm_add {X Y : ℂ} {x y : ℝ}
    (hX : ‖X‖ ≤ x) (hY : ‖Y‖ ≤ y) : ‖X + Y‖ ≤ x + y :=
  (norm_add_le _ _).trans (add_le_add hX hY)

/-- A regular-prime bound throughout every closed subregion with a fixed
positive distance from all five summability faces. -/
theorem rowEulerRationalValue_correctedRegion_bound
    {q σ ν ζ δ : ℝ} (hq : 2 ≤ q) (hσ : 1 / 2 ≤ σ)
    (hν : 0 ≤ ν) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    (hfaceWV : 1 + δ ≤ ν + 6 * ζ)
    (hfaceE : 5 + δ ≤ 6 * σ + 6 * ζ)
    (hfaceDV : 1 + δ ≤ σ + 6 * ζ)
    (hfaceDW : 1 + δ ≤ σ + ν)
    (hfaceDqWV : 2 + δ ≤ σ + ν + 6 * ζ)
    (V W D E : ℂ)
    (hV : ‖V‖ ≤ q ^ (-6 * ζ))
    (hW : ‖W‖ ≤ q ^ (-ν))
    (hD : ‖D‖ ≤ q ^ (-σ))
    (hEE : ‖E‖ ≤ q ^ (4 - 6 * σ - 6 * ζ)) :
    ‖rowEulerRationalValue (q : ℂ) (q : ℂ)⁻¹ V W D E - 1‖ ≤
      (11 / sweptTubeEulerMargin) * q ^ (-1 - δ) := by
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
      ‖D‖ ≤ q ^ (-σ) := hD
      _ ≤ q ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      _ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
  have hEe : ‖E‖ ≤ (1 / 2 : ℝ) := by
    have hpow : q ^ (4 - 6 * σ - 6 * ζ) ≤ q ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    refine hEE.trans (hpow.trans ?_)
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
  let B : ℝ := q ^ (-1 - δ)
  have lower {X : ℂ} {b : ℝ} (hX : ‖X‖ ≤ q ^ b)
      (hb : b ≤ -1 - δ) : ‖X‖ ≤ B :=
    hX.trans (Real.rpow_le_rpow_of_exponent_le hq1 hb)
  have hWV := correctedRegion_norm_mul hq0 hW hV
  have hEq := correctedRegion_norm_mul hq0 hEE hqiN
  have hEqW := correctedRegion_norm_mul hq0 hEq hW
  have hEW := correctedRegion_norm_mul hq0 hEE hW
  have hEWW := correctedRegion_norm_mul hq0 hEW hW
  have hEWWV := correctedRegion_norm_mul hq0 hEWW hV
  have hDV := correctedRegion_norm_mul hq0 hD hV
  have hDW := correctedRegion_norm_mul hq0 hD hW
  have hDq := correctedRegion_norm_mul hq0 hD hqN
  have hDqW := correctedRegion_norm_mul hq0 hDq hW
  have hDqWV := correctedRegion_norm_mul hq0 hDqW hV
  have hDqm := correctedRegion_norm_mul hq0 hD hqmN
  have hDqmW := correctedRegion_norm_mul hq0 hDqm hW
  have hDqmWW := correctedRegion_norm_mul hq0 hDqmW hW
  have hDqmWWV := correctedRegion_norm_mul hq0 hDqmWW hV
  have hDE := correctedRegion_norm_mul hq0 hD hEE
  have h1 : ‖-(W * V)‖ ≤ B := by
    rw [norm_neg]
    exact lower hWV (by linarith)
  have h2 : ‖E‖ ≤ B := lower hEE (by linarith)
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
  have hsum := correctedRegion_norm_add
    (correctedRegion_norm_add
    (correctedRegion_norm_add
    (correctedRegion_norm_add
    (correctedRegion_norm_add
    (correctedRegion_norm_add
    (correctedRegion_norm_add
    (correctedRegion_norm_add
    (correctedRegion_norm_add
    (correctedRegion_norm_add h1 h2) h3) h4) h5) h6) h7) h8) h9) h10) h11
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



#print axioms rowEulerRationalValue_correctedRegion_bound
end HeckeSkeleton.HighBinContinuation
