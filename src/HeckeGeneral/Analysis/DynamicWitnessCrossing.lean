import HeckeGeneral.Analysis.EndpointClosure

/-!
The exact short/long witness crossing, including the closed endpoints.
This consumes witness-count exponents. Deriving those counts from the
actual detector and canonical moments remains separate. The resulting
exponent is literally the one in OpenAI's checked endpoint certificate.
-/

noncomputable section
namespace HeckeGeneral.Analysis

open OAI.SevenEighths.Endpoint

def shortWitnessCount (δ y t : ℝ) : ℝ :=
  1 - δ + δ * primeWeight y / denominator y * (3 / 2 - t)

def longWitnessCount (δ t : ℝ) : ℝ :=
  1 - δ + (5 / 6 - δ) * (t - 1)

theorem witnessDenominator_coordinate (x : ℝ) :
    denominator (1 / 2 - x) = 3 - 17 * x / 9 := by
  unfold denominator
  ring

theorem witnessPrimeWeight_coordinate (x : ℝ) :
    primeWeight (1 / 2 - x) = (2 - 8 * x / 9) * (1 - x) := by
  unfold primeWeight
  ring

theorem balancedCutoff_mem_Icc {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    1 ≤ balancedCutoff δ y ∧ balancedCutoff δ y ≤ 3 / 2 := by
  obtain ⟨hD, _⟩ := denominator_bounds hy0 hy1
  obtain ⟨hP, _⟩ := primeWeight_bounds hy0 hy1
  obtain ⟨hJ, _⟩ := balanceDenominator_bounds hδ0 hδ1 hy0 hy1
  have hJpos : 0 < balanceDenominator δ y := by linarith
  have hnum : 0 ≤ δ * primeWeight y := mul_nonneg hδ0 (by linarith)
  have hnumJ : δ * primeWeight y ≤ balanceDenominator δ y := by
    have h := mul_nonneg (sub_nonneg.mpr hδ1) (by linarith : 0 ≤ denominator y)
    unfold balanceDenominator
    linarith
  have hlo := div_nonneg hnum (mul_pos (by norm_num : (0 : ℝ) < 2) hJpos).le
  have hhi : δ * primeWeight y / (2 * balanceDenominator δ y) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hJpos)).mpr
    linarith
  unfold balancedCutoff
  constructor <;> linarith

theorem longWitnessCount_balanced (δ y : ℝ) :
    longWitnessCount δ (balancedCutoff δ y) = balancedRowCount δ y := by
  unfold longWitnessCount balancedRowCount
  ring

theorem shortWitnessCount_balanced {δ y : ℝ}
    (hD : denominator y ≠ 0) (hJ : balanceDenominator δ y ≠ 0) :
    shortWitnessCount δ y (balancedCutoff δ y) = balancedRowCount δ y := by
  unfold shortWitnessCount balancedRowCount balancedCutoff
  field_simp [hD, hJ]
  unfold balanceDenominator
  ring

/-- The chosen t depends only on the real bin parameters. The bound
assumed here must still be proved from the actual witnesses and moments. -/
theorem row_count_of_short_long_envelope {δ y Δ ε R : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hR : ∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 →
      R ≤ max (shortWitnessCount δ y t) (longWitnessCount δ t) + Δ / 4 + ε) :
    R ≤ balancedRowCount δ y + Δ / 4 + ε := by
  obtain ⟨ht0, ht1⟩ := balancedCutoff_mem_Icc hδ0 hδ1 hy0 hy1
  obtain ⟨hD, _⟩ := denominator_bounds hy0 hy1
  obtain ⟨hJ, _⟩ := balanceDenominator_bounds hδ0 hδ1 hy0 hy1
  have h := hR (balancedCutoff δ y) ht0 ht1
  rw [shortWitnessCount_balanced (by linarith) (by linarith),
    longWitnessCount_balanced, max_self] at h
  exact h

/-- The remaining moment/rounding loss is displayed, not hidden in O(eps). -/
theorem dynamic_endpoint_saving_with_loss {δ y Δ ε R : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hR : R ≤ balancedRowCount δ y + Δ / 4 + ε) :
    moderateExponent (13 / 16) δ (δ * (1 / 2 - y)) R - Δ ≤
      -(49 / 440640) - (51 / 64) * Δ + (13 / 16) * ε := by
  have hR' : R - ε ≤ balancedRowCount δ y + Δ / 4 := by linarith
  have h := dynamic_endpoint_saving hδ0 hδ1 hy0 hy1 hR'
  unfold moderateExponent at *
  linarith

end HeckeGeneral.Analysis
