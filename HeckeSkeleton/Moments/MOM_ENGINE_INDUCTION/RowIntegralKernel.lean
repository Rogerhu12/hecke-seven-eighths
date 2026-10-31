import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.KernelReduction
import Mathlib.MeasureTheory.Function.L2Space

/-!
# A common positive kernel from literal rowwise integral identities

Each original row has its own complex coefficient, dominated by the same
nonnegative integrable envelope. Weighted Cauchy is applied row by row,
then the finite original row sum is interchanged with that same integral.
The resulting positive kernel has exactly the square of the envelope's
L1 mass. There is no row-cardinality factor, supremum over rows, or product
of row-dependent measures. Only numerical column L2 and genuine termwise
integral identities are used; no child moment estimate is an input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory
open scoped BigOperators Classical ENNReal

universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v}

/-- Weighted Cauchy in a finite positive measure, retaining its real mass. -/
theorem integral_norm_sq_le_mass (ν : Measure Ω) [IsFiniteMeasure ν]
    {f : Ω → ℂ} (hf : MemLp f 2 ν) :
    (∫ ξ, ‖f ξ‖ ∂ν) ^ 2 ≤ ν.real Set.univ * ∫ ξ, ‖f ξ‖ ^ 2 ∂ν := by
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ν)
    Real.HolderConjugate.two_two
    (f := fun _ : Ω => (1 : ℝ)) (g := fun ξ => ‖f ξ‖)
    (Filter.Eventually.of_forall (fun _ => zero_le_one))
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (memLp_const 1) hf.norm
  have hbound : (∫ ξ, ‖f ξ‖ ∂ν) ≤
      Real.sqrt (ν.real Set.univ) * Real.sqrt (∫ ξ, ‖f ξ‖ ^ 2 ∂ν) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa [Real.rpow_two, integral_const, measureReal_def] using hCS
  have hs := pow_le_pow_left₀ (integral_nonneg fun ξ => norm_nonneg (f ξ)) hbound 2
  rw [mul_pow, Real.sq_sqrt measureReal_nonneg,
    Real.sq_sqrt (integral_nonneg fun ξ => sq_nonneg ‖f ξ‖)] at hs
  exact hs

/-- The original weighted column norm is L1 because the actual column
is L2 in the finite envelope measure. -/
theorem integrable_weight_mul_norm (μ : Measure Ω) {weight : Ω → ℝ}
    (hm : Measurable weight) (hw : ∀ ξ, 0 ≤ weight ξ)
    (hi : Integrable weight μ) {f : Ω → ℂ}
    (hf : MemLp f 2 (kernelWeightedMeasure μ weight)) :
    Integrable (fun ξ => weight ξ * ‖f ξ‖) μ := by
  letI : IsFiniteMeasure (kernelWeightedMeasure μ weight) :=
    kernelWeightedMeasure_finite μ hw hi
  have hfn := (hf.integrable (by norm_num)).norm
  change Integrable (fun ξ => ‖f ξ‖)
    (μ.withDensity fun ξ => ENNReal.ofReal (weight ξ)) at hfn
  have ht := (integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).1 hfn
  convert ht using 1
  ext ξ
  rw [ENNReal.toReal_ofReal (hw ξ), smul_eq_mul]

/-- One row's coefficient is bounded before Cauchy; the row itself is
neither discarded nor inserted as a new parameter in the common measure. -/
theorem row_integral_energy_le (μ : Measure Ω) {weight : Ω → ℝ}
    (hm : Measurable weight) (hw : ∀ ξ, 0 ≤ weight ξ)
    (hi : Integrable weight μ) {coefficient f : Ω → ℂ}
    (hf : MemLp f 2 (kernelWeightedMeasure μ weight))
    (hint : Integrable (fun ξ => coefficient ξ * f ξ) μ)
    (hcoeff : ∀ᵐ ξ ∂μ, ‖coefficient ξ‖ ≤ weight ξ) :
    ‖∫ ξ, coefficient ξ * f ξ ∂μ‖ ^ 2 ≤
      (kernelWeightedMeasure μ weight).real Set.univ *
        ∫ ξ, ‖f ξ‖ ^ 2 ∂kernelWeightedMeasure μ weight := by
  letI : IsFiniteMeasure (kernelWeightedMeasure μ weight) :=
    kernelWeightedMeasure_finite μ hw hi
  have hpoint : ∀ᵐ ξ ∂μ,
      ‖coefficient ξ * f ξ‖ ≤ weight ξ * ‖f ξ‖ := by
    filter_upwards [hcoeff] with ξ hξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
  have hbound : ‖∫ ξ, coefficient ξ * f ξ ∂μ‖ ≤
      ∫ ξ, ‖f ξ‖ ∂kernelWeightedMeasure μ weight := by
    calc
      _ ≤ ∫ ξ, ‖coefficient ξ * f ξ‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ ξ, weight ξ * ‖f ξ‖ ∂μ :=
        integral_mono_ae hint.norm (integrable_weight_mul_norm μ hm hw hi hf) hpoint
      _ = _ := (integral_kernelWeightedMeasure μ hm hw (fun ξ => ‖f ξ‖)).symm
  exact (pow_le_pow_left₀ (norm_nonneg _) hbound 2).trans
    (integral_norm_sq_le_mass (kernelWeightedMeasure μ weight) hf)

/-- Exact finite-row assembly with no cardinality loss. -/
theorem finite_rows_integral_energy_le (μ : Measure Ω) (rows : Finset ι)
    {weight : Ω → ℝ} (hm : Measurable weight) (hw : ∀ ξ, 0 ≤ weight ξ)
    (hi : Integrable weight μ) (coefficient f : ι → Ω → ℂ)
    (hf : ∀ u ∈ rows, MemLp (f u) 2 (kernelWeightedMeasure μ weight))
    (hint : ∀ u ∈ rows, Integrable (fun ξ => coefficient u ξ * f u ξ) μ)
    (hcoeff : ∀ u ∈ rows, ∀ᵐ ξ ∂μ, ‖coefficient u ξ‖ ≤ weight ξ) :
    (∑ u ∈ rows, ‖∫ ξ, coefficient u ξ * f u ξ ∂μ‖ ^ 2) ≤
      (kernelWeightedMeasure μ weight).real Set.univ *
        ∫ ξ, ∑ u ∈ rows, ‖f u ξ‖ ^ 2 ∂kernelWeightedMeasure μ weight := by
  calc
    _ ≤ ∑ u ∈ rows, (kernelWeightedMeasure μ weight).real Set.univ *
        ∫ ξ, ‖f u ξ‖ ^ 2 ∂kernelWeightedMeasure μ weight := by
      apply Finset.sum_le_sum
      intro u hu
      exact row_integral_energy_le μ hm hw hi (hf u hu) (hint u hu) (hcoeff u hu)
    _ = _ := by
      rw [integral_finset_sum rows (fun u hu => (hf u hu).norm.integrable_sq),
        Finset.mul_sum]

/-- The common positive energy measure. Its density is the common L1
mass times the original envelope, not a row-dependent choice. -/
def rowEnergyKernel (μ : Measure Ω) (weight : Ω → ℝ) : Measure Ω :=
  kernelWeightedMeasure μ (fun ξ => (∫ η, weight η ∂μ) * weight ξ)

theorem rowEnergyKernel_finite (μ : Measure Ω) {weight : Ω → ℝ}
    (hw : ∀ ξ, 0 ≤ weight ξ) (hi : Integrable weight μ) :
    IsFiniteMeasure (rowEnergyKernel μ weight) := by
  apply kernelWeightedMeasure_finite μ
    (fun ξ => mul_nonneg (integral_nonneg hw) (hw ξ)) (hi.const_mul _)

/-- The exact mass is paid once, independently of the number of rows. -/
theorem rowEnergyKernel_mass (μ : Measure Ω) {weight : Ω → ℝ}
    (hm : Measurable weight) (hw : ∀ ξ, 0 ≤ weight ξ) :
    (rowEnergyKernel μ weight).real Set.univ = (∫ ξ, weight ξ ∂μ) ^ 2 := by
  rw [rowEnergyKernel, kernelWeightedMeasure_mass μ (hm.const_mul _)
    (fun ξ => mul_nonneg (integral_nonneg hw) (hw ξ)), integral_const_mul, pow_two]

theorem integral_rowEnergyKernel (μ : Measure Ω) {weight : Ω → ℝ}
    (hm : Measurable weight) (hw : ∀ ξ, 0 ≤ weight ξ) (value : Ω → ℝ) :
    (∫ ξ, value ξ ∂rowEnergyKernel μ weight) =
      (kernelWeightedMeasure μ weight).real Set.univ *
        ∫ ξ, value ξ ∂kernelWeightedMeasure μ weight := by
  rw [rowEnergyKernel, integral_kernelWeightedMeasure μ (hm.const_mul _)
    (fun ξ => mul_nonneg (integral_nonneg hw) (hw ξ)),
    kernelWeightedMeasure_mass μ hm hw,
    integral_kernelWeightedMeasure μ hm hw]
  simp only [mul_assoc]
  exact integral_const_mul _ _

/-- The whole original row energy is integrated over one common kernel. -/
theorem finite_rows_energy_le_rowEnergyKernel (μ : Measure Ω) (rows : Finset ι)
    {weight : Ω → ℝ} (hm : Measurable weight) (hw : ∀ ξ, 0 ≤ weight ξ)
    (hi : Integrable weight μ) (coefficient f : ι → Ω → ℂ)
    (hf : ∀ u ∈ rows, MemLp (f u) 2 (kernelWeightedMeasure μ weight))
    (hint : ∀ u ∈ rows, Integrable (fun ξ => coefficient u ξ * f u ξ) μ)
    (hcoeff : ∀ u ∈ rows, ∀ᵐ ξ ∂μ, ‖coefficient u ξ‖ ≤ weight ξ) :
    (∑ u ∈ rows, ‖∫ ξ, coefficient u ξ * f u ξ ∂μ‖ ^ 2) ≤
      ∫ ξ, ∑ u ∈ rows, ‖f u ξ‖ ^ 2 ∂rowEnergyKernel μ weight := by
  rw [integral_rowEnergyKernel μ hm hw]
  exact finite_rows_integral_energy_le μ rows hm hw hi coefficient f hf hint hcoeff

/-- A genuine pointwise remainder is charged separately from the common
reflection kernel; no cancellation is lost inside a child polynomial. -/
theorem finite_rows_energy_with_tail (μ : Measure Ω) (rows : Finset ι)
    {weight : Ω → ℝ} (hm : Measurable weight) (hw : ∀ ξ, 0 ≤ weight ξ)
    (hi : Integrable weight μ) (coefficient f : ι → Ω → ℂ)
    (hf : ∀ u ∈ rows, MemLp (f u) 2 (kernelWeightedMeasure μ weight))
    (hint : ∀ u ∈ rows, Integrable (fun ξ => coefficient u ξ * f u ξ) μ)
    (hcoeff : ∀ u ∈ rows, ∀ᵐ ξ ∂μ, ‖coefficient u ξ‖ ≤ weight ξ)
    (parent tail : ι → ℂ)
    (hparent : ∀ u ∈ rows, parent u = tail u + ∫ ξ, coefficient u ξ * f u ξ ∂μ) :
    (∑ u ∈ rows, ‖parent u‖ ^ 2) ≤ 2 * (∑ u ∈ rows, ‖tail u‖ ^ 2) +
      2 * ∫ ξ, ∑ u ∈ rows, ‖f u ξ‖ ^ 2 ∂rowEnergyKernel μ weight := by
  have hrow (u : ι) (hu : u ∈ rows) :
      ‖parent u‖ ^ 2 ≤ 2 * ‖tail u‖ ^ 2 +
        2 * ‖∫ ξ, coefficient u ξ * f u ξ ∂μ‖ ^ 2 := by
    rw [hparent u hu]
    have hn := norm_add_le (tail u) (∫ ξ, coefficient u ξ * f u ξ ∂μ)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖tail u‖ - ‖∫ ξ, coefficient u ξ * f u ξ ∂μ‖)]
  have hs := Finset.sum_le_sum hrow
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  exact hs.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left
      (finite_rows_energy_le_rowEnergyKernel μ rows hm hw hi coefficient f hf hint hcoeff)
      (by norm_num : (0 : ℝ) ≤ 2)) _)

end HeckeSkeleton.Moments.EngineInduction
