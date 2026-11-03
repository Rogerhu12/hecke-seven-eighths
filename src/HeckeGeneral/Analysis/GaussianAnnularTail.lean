import HeckeGeneral.Analysis.GaussianAnnuli

/-!+# Arbitrarily small Gaussian annular tails

Summability with every exponential weight gives an explicit tail estimate.
At the moving threshold `κ log Z-C₀`, choosing the exponential weight before
`Z` yields a bound by `Z^(-M)` after multiplication by any prescribed `Z^B`.
This is the quantitative truncation required for the Gaussian-to-annuli step.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open scoped BigOperators Classical

def gaussianAnnularTail (n : ℕ) (C A T : ℝ) : ℝ :=
  ∑' k : ℤ, if T < |(k : ℝ)| then Real.exp (A * |(k : ℝ)|) * gaussianAnnulusMajorant n C k else 0

def gaussianAnnularWeightedMass (n : ℕ) (C A : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (A * |(k : ℝ)|) * gaussianAnnulusMajorant n C k

theorem summable_gaussianAnnularTail_terms (n : ℕ) (C A T : ℝ) (hC : 0 ≤ C) :
    Summable (fun k : ℤ => if T < |(k : ℝ)| then
      Real.exp (A * |(k : ℝ)|) * gaussianAnnulusMajorant n C k else 0) := by
  apply (summable_gaussianAnnulusMajorant n C A hC).of_nonneg_of_le
  · intro k
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (gaussianAnnulusMajorant_nonneg n C hC k)
    · exact le_refl _
  · intro k
    split_ifs
    · exact le_refl _
    · exact mul_nonneg (Real.exp_pos _).le (gaussianAnnulusMajorant_nonneg n C hC k)

theorem gaussianAnnularTail_nonneg (n : ℕ) (C A T : ℝ) (hC : 0 ≤ C) :
    0 ≤ gaussianAnnularTail n C A T := by
  apply tsum_nonneg
  intro k
  split_ifs
  · exact mul_nonneg (Real.exp_pos _).le (gaussianAnnulusMajorant_nonneg n C hC k)
  · exact le_refl _

theorem gaussianAnnularWeightedMass_nonneg (n : ℕ) (C A : ℝ) (hC : 0 ≤ C) :
    0 ≤ gaussianAnnularWeightedMass n C A :=
  tsum_nonneg fun k => mul_nonneg (Real.exp_pos _).le (gaussianAnnulusMajorant_nonneg n C hC k)

/-- Markov's exponential-weight bound, with the actual finite Gaussian mass as constant. -/
theorem gaussianAnnularTail_le_exp (n : ℕ) (C A T r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) :
    gaussianAnnularTail n C A T ≤
      Real.exp (-r * T) * gaussianAnnularWeightedMass n C (A + r) := by
  unfold gaussianAnnularTail gaussianAnnularWeightedMass
  rw [← tsum_mul_left]
  apply (summable_gaussianAnnularTail_terms n C A T hC).tsum_le_tsum _
    ((summable_gaussianAnnulusMajorant n C (A + r) hC).mul_left _)
  intro k
  split_ifs with hk
  · have hexp : Real.exp (A * |(k : ℝ)|) ≤
        Real.exp (-r * T) * Real.exp ((A + r) * |(k : ℝ)|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      _ ≤ (Real.exp (-r * T) * Real.exp ((A + r) * |(k : ℝ)|)) *
          gaussianAnnulusMajorant n C k :=
        mul_le_mul_of_nonneg_right hexp (gaussianAnnulusMajorant_nonneg n C hC k)
      _ = _ := mul_assoc _ _ _
  · exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le (gaussianAnnulusMajorant_nonneg n C hC k))

theorem gaussianAnnularTail_antitone (n : ℕ) (C A : ℝ) (hC : 0 ≤ C) :
    Antitone (gaussianAnnularTail n C A) := by
  intro T U hTU
  apply (summable_gaussianAnnularTail_terms n C A U hC).tsum_le_tsum _
    (summable_gaussianAnnularTail_terms n C A T hC)
  intro k
  by_cases hU : U < |(k : ℝ)|
  · rw [ite_eq_left hU, ite_eq_left (hTU.trans_lt hU)]
  · rw [ite_eq_right hU]
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (gaussianAnnulusMajorant_nonneg n C hC k)
    · exact le_refl _

/-- Explicit super-polynomial loss at a logarithmically moving annulus threshold. -/
theorem gaussianAnnularTail_logarithmic_bound (n : ℕ) (C A C₀ B M κ Z : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hM : 0 ≤ M) (hκ : 0 < κ) (hZ : 0 < Z) :
    Z ^ B * gaussianAnnularTail n C A (κ * Real.log Z - C₀) ≤
      (Real.exp (((B + M) / κ) * C₀) *
        gaussianAnnularWeightedMass n C (A + (B + M) / κ)) * Z ^ (-M) := by
  let r : ℝ := (B + M) / κ
  have hr : 0 ≤ r := div_nonneg (add_nonneg hB hM) hκ.le
  have htail := gaussianAnnularTail_le_exp n C A (κ * Real.log Z - C₀) r hC hr
  have hscale : Z ^ B * Real.exp (-r * (κ * Real.log Z - C₀)) =
      Real.exp (r * C₀) * Z ^ (-M) := by
    rw [Real.rpow_def_of_pos hZ, Real.rpow_def_of_pos hZ, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [r]
    field_simp
    ring
  calc
    _ ≤ Z ^ B * (Real.exp (-r * (κ * Real.log Z - C₀)) *
        gaussianAnnularWeightedMass n C (A + r)) :=
      mul_le_mul_of_nonneg_left htail (Real.rpow_pos_of_pos hZ B).le
    _ = _ := by rw [← mul_assoc, hscale]; ring

end HeckeGeneral.Analysis
