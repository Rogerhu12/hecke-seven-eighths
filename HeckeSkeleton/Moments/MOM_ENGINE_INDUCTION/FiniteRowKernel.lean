import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FiniteBranchMeasure

/-!
# Assemble actual row integrals across all finite reflection branches

Cauchy over the dyadic and fixed-contour branches costs their finite
cardinality. Weighted Cauchy within each branch was already proved for
the original finite row set. The full positive measure is then assembled
on one fixed branch-frequency space. Its mass includes both Cauchy costs.
There is never a factor equal to the number of arithmetic rows.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory
open scoped BigOperators Classical NNReal

universe u v w
variable {B : Type u} {Ω : Type v} [MeasurableSpace Ω] {ι : Type w}

theorem finite_branch_sum_norm_sq_le (branches : Finset B) (f : B → ℂ) :
    ‖∑ b ∈ branches, f b‖ ^ 2 ≤
      (branches.card : ℝ) * ∑ b ∈ branches, ‖f b‖ ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq branches
    (fun _ => (1 : ℝ)) (fun b => ‖f b‖)
  have hs := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le branches f) 2
  exact hs.trans (by simpa using hc)

/-- The actual tail remains separate, and every original branch integral
is evaluated before the common positive row-energy estimate is used. -/
theorem finite_rows_branch_integrals_energy_le
    (branches : Finset B) (μ : B → Measure Ω) (rows : Finset ι)
    (weight : B → Ω → ℝ)
    (hm : ∀ b ∈ branches, Measurable (weight b))
    (hw : ∀ b ∈ branches, ∀ ξ, 0 ≤ weight b ξ)
    (hi : ∀ b ∈ branches, Integrable (weight b) (μ b))
    (coefficient f : B → ι → Ω → ℂ)
    (hf : ∀ b ∈ branches, ∀ u ∈ rows,
      MemLp (f b u) 2 (kernelWeightedMeasure (μ b) (weight b)))
    (hint : ∀ b ∈ branches, ∀ u ∈ rows,
      Integrable (fun ξ => coefficient b u ξ * f b u ξ) (μ b))
    (hcoeff : ∀ b ∈ branches, ∀ u ∈ rows,
      ∀ᵐ ξ ∂μ b, ‖coefficient b u ξ‖ ≤ weight b ξ)
    (parent tail : ι → ℂ)
    (hparent : ∀ u ∈ rows, parent u = tail u +
      ∑ b ∈ branches, ∫ ξ, coefficient b u ξ * f b u ξ ∂μ b) :
    (∑ u ∈ rows, ‖parent u‖ ^ 2) ≤ 2 * (∑ u ∈ rows, ‖tail u‖ ^ 2) +
      2 * (branches.card : ℝ) * ∑ b ∈ branches,
        ∫ ξ, ∑ u ∈ rows, ‖f b u ξ‖ ^ 2 ∂rowEnergyKernel (μ b) (weight b) := by
  have hrow (u : ι) (hu : u ∈ rows) :
      ‖parent u‖ ^ 2 ≤ 2 * ‖tail u‖ ^ 2 + 2 * (branches.card : ℝ) *
        ∑ b ∈ branches, ‖∫ ξ, coefficient b u ξ * f b u ξ ∂μ b‖ ^ 2 := by
    rw [hparent u hu]
    have hn := norm_add_le (tail u)
      (∑ b ∈ branches, ∫ ξ, coefficient b u ξ * f b u ξ ∂μ b)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hc := finite_branch_sum_norm_sq_le branches
      (fun b => ∫ ξ, coefficient b u ξ * f b u ξ ∂μ b)
    nlinarith [sq_nonneg (‖tail u‖ -
      ‖∑ b ∈ branches, ∫ ξ, coefficient b u ξ * f b u ξ ∂μ b‖)]
  have hs := Finset.sum_le_sum hrow
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_comm] at hs
  have hk :
      (∑ b ∈ branches, ∑ u ∈ rows,
        ‖∫ ξ, coefficient b u ξ * f b u ξ ∂μ b‖ ^ 2) ≤
      ∑ b ∈ branches,
        ∫ ξ, ∑ u ∈ rows, ‖f b u ξ‖ ^ 2 ∂rowEnergyKernel (μ b) (weight b) := by
    apply Finset.sum_le_sum
    intro b hb
    exact finite_rows_energy_le_rowEnergyKernel (μ b) rows (hm b hb) (hw b hb)
      (hi b hb) (coefficient b) (f b) (hf b hb) (hint b hb) (hcoeff b hb)
  have hscaled := mul_le_mul_of_nonneg_left hk
    (show 0 ≤ 2 * (branches.card : ℝ) by positivity)
  linarith

/-- Both the tail split and finite branch Cauchy are charged to each
actual branch measure, before assembling it with the other branches. -/
def finiteRowBranchKernel (branches : Finset B) (μ : B → Measure Ω)
    (weight : B → Ω → ℝ) (b : B) : Measure Ω :=
  (2 * (branches.card : ℝ≥0)) • rowEnergyKernel (μ b) (weight b)

theorem finiteRowBranchKernel_finite (branches : Finset B) (μ : B → Measure Ω)
    (weight : B → Ω → ℝ) (b : B)
    (hw : ∀ ξ, 0 ≤ weight b ξ) (hi : Integrable (weight b) (μ b)) :
    IsFiniteMeasure (finiteRowBranchKernel branches μ weight b) := by
  letI := rowEnergyKernel_finite (μ b) hw hi
  unfold finiteRowBranchKernel
  infer_instance

theorem finiteRowBranchKernel_mass (branches : Finset B) (μ : B → Measure Ω)
    (weight : B → Ω → ℝ) (b : B)
    (hm : Measurable (weight b)) (hw : ∀ ξ, 0 ≤ weight b ξ) :
    (finiteRowBranchKernel branches μ weight b).real Set.univ =
      2 * (branches.card : ℝ) * (∫ ξ, weight b ξ ∂μ b) ^ 2 := by
  rw [finiteRowBranchKernel, measureReal_nnreal_smul_apply,
    rowEnergyKernel_mass (μ b) hm hw]
  simp

theorem integral_finiteRowBranchKernel (branches : Finset B) (μ : B → Measure Ω)
    (weight : B → Ω → ℝ) (b : B) (value : Ω → ℝ) :
    (∫ ξ, value ξ ∂finiteRowBranchKernel branches μ weight b) =
      2 * (branches.card : ℝ) * ∫ ξ, value ξ ∂rowEnergyKernel (μ b) (weight b) := by
  rw [finiteRowBranchKernel, integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

/-- The full branch sum costs the square of its count, after the true
common L1 mass of each envelope is bounded. -/
theorem finiteRowBranchKernel_mass_sum_le
    (branches : Finset B) (μ : B → Measure Ω) (weight : B → Ω → ℝ)
    (hm : ∀ b ∈ branches, Measurable (weight b))
    (hw : ∀ b ∈ branches, ∀ ξ, 0 ≤ weight b ξ)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hL1 : ∀ b ∈ branches, (∫ ξ, weight b ξ ∂μ b) ≤ bound) :
    (∑ b ∈ branches, (finiteRowBranchKernel branches μ weight b).real Set.univ) ≤
      2 * (branches.card : ℝ) ^ 2 * bound ^ 2 := by
  calc
    _ ≤ ∑ _b ∈ branches, 2 * (branches.card : ℝ) * bound ^ 2 := by
      apply Finset.sum_le_sum
      intro b hb
      rw [finiteRowBranchKernel_mass branches μ weight b (hm b hb) (hw b hb)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (integral_nonneg (hw b hb)) (hL1 b hb) 2
    _ = _ := by simp [pow_two]; ring

end HeckeSkeleton.Moments.EngineInduction
