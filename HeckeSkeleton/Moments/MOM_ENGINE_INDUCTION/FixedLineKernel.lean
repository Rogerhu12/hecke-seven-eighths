import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FiniteRowKernel
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionDensity

/-!
# Row-dependent line selection inside a fixed common kernel

Each original row chooses one of the two contour lines. The common
children are indexed by both fixed lines; only a scalar coefficient
contains that row-dependent choice. Thus every common child still has
one fixed profile and scale for all of its original rows.

The finite dyadic and line labels are placed in one fixed product with
the continuous frequency space. Every branch is retained in the mass.
The only identity hypothesis below is a literal complex row identity,
before squares, Cauchy, integration of child energies, or induction.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory
open scoped BigOperators Classical NNReal

universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v}

def reflectionFixedLine (line : Bool) : ℝ := if line then 3 / 4 else 1 / 4

def reflectionLineChoice (ratio : ℝ) : Bool := decide (ratio ≤ 1)

theorem reflectionFixedLine_choice (ratio : ℝ) :
    reflectionFixedLine (reflectionLineChoice ratio) = ordinaryReflectionLine ratio := by
  by_cases h : ratio ≤ 1 <;> simp [reflectionFixedLine, reflectionLineChoice,
    ordinaryReflectionLine, h]

theorem reflectionFixedLine_bounds (line : Bool) :
    1 / 4 ≤ reflectionFixedLine line ∧ reflectionFixedLine line ≤ 3 / 4 := by
  cases line <;> norm_num [reflectionFixedLine]

def reflectionBranches (cutoff : ℕ) : Finset (ℕ × Bool) :=
  (Finset.range (cutoff + 1)).product Finset.univ

theorem reflectionBranches_card (cutoff : ℕ) :
    (reflectionBranches cutoff).card = 2 * (cutoff + 1) := by
  simp [reflectionBranches, Nat.mul_comm]

theorem mem_reflectionBranches (cutoff : ℕ) (b : ℕ × Bool) :
    b ∈ reflectionBranches cutoff ↔ b.1 ≤ cutoff := by
  simp only [reflectionBranches, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, Nat.lt_succ_iff]

/-- The row-dependent choice occurs only in the scalar coefficient. -/
def fixedLineCoefficient (selected : Bool) (coefficient : Bool → Ω → ℂ)
    (line : Bool) (ξ : Ω) : ℂ :=
  if line = selected then coefficient line ξ else 0

theorem fixedLineCoefficient_bound (selected : Bool) (coefficient : Bool → Ω → ℂ)
    (weight : Ω → ℝ) (hw : ∀ ξ, 0 ≤ weight ξ)
    (hc : ∀ ξ, ‖coefficient selected ξ‖ ≤ weight ξ)
    (line : Bool) (ξ : Ω) :
    ‖fixedLineCoefficient selected coefficient line ξ‖ ≤ weight ξ := by
  by_cases h : line = selected
  · subst line
    simpa [fixedLineCoefficient] using hc ξ
  · simpa only [fixedLineCoefficient, if_neg h, norm_zero] using hw ξ

theorem fixedLineCoefficient_integrable (μ : Measure Ω)
    (selected : Bool) (coefficient f : Bool → Ω → ℂ)
    (hi : Integrable (fun ξ => coefficient selected ξ * f selected ξ) μ)
    (line : Bool) :
    Integrable (fun ξ => fixedLineCoefficient selected coefficient line ξ * f line ξ) μ := by
  by_cases h : line = selected
  · subst line
    simpa [fixedLineCoefficient] using hi
  · simpa only [fixedLineCoefficient, if_neg h, zero_mul] using!
      (integrable_zero Ω ℂ μ)

/-- Sum over both fixed lines recovers the selected original integral
exactly, including the case of a line chosen separately for each row. -/
theorem fixedLineCoefficient_integral_sum (μ : Measure Ω)
    (selected : Bool) (coefficient f : Bool → Ω → ℂ) :
    (∑ line : Bool, ∫ ξ, fixedLineCoefficient selected coefficient line ξ * f line ξ ∂μ) =
      ∫ ξ, coefficient selected ξ * f selected ξ ∂μ := by
  rw [Finset.sum_eq_single selected]
  · simp [fixedLineCoefficient]
  · intro line _hline hline
    simp only [fixedLineCoefficient, if_neg hline, zero_mul, integral_zero]
  · simp

theorem reflectionBranches_integral_sum (μ : Measure Ω) (cutoff : ℕ)
    (selected : ℕ → Bool) (coefficient f : ℕ → Bool → Ω → ℂ) :
    (∑ b ∈ reflectionBranches cutoff,
      ∫ ξ, fixedLineCoefficient (selected b.1) (coefficient b.1) b.2 ξ * f b.1 b.2 ξ ∂μ) =
      ∑ j ∈ Finset.range (cutoff + 1),
        ∫ ξ, coefficient j (selected j) ξ * f j (selected j) ξ ∂μ := by
  rw [reflectionBranches, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _hj
  exact fixedLineCoefficient_integral_sum μ (selected j) (coefficient j) (f j)

/-- Assemble a literal parent identity on the common finite row set.
The two possible children remain fixed for all rows within each branch. -/
theorem fixedLine_rows_energy_le (μ : Measure Ω) (cutoff : ℕ) (rows : Finset ι)
    (weight : Ω → ℝ) (hm : Measurable weight) (hw : ∀ ξ, 0 ≤ weight ξ)
    (hi : Integrable weight μ) (selected : ι → ℕ → Bool)
    (coefficient f : ℕ → Bool → ι → Ω → ℂ)
    (hf : ∀ j ∈ Finset.range (cutoff + 1), ∀ line : Bool, ∀ u ∈ rows,
      MemLp (f j line u) 2 (kernelWeightedMeasure μ weight))
    (hint : ∀ j ∈ Finset.range (cutoff + 1), ∀ u ∈ rows,
      Integrable (fun ξ => coefficient j (selected u j) u ξ * f j (selected u j) u ξ) μ)
    (hc : ∀ j ∈ Finset.range (cutoff + 1), ∀ u ∈ rows, ∀ ξ,
      ‖coefficient j (selected u j) u ξ‖ ≤ weight ξ)
    (parent tail : ι → ℂ)
    (hparent : ∀ u ∈ rows, parent u = tail u +
      ∑ j ∈ Finset.range (cutoff + 1),
        ∫ ξ, coefficient j (selected u j) u ξ * f j (selected u j) u ξ ∂μ) :
    (∑ u ∈ rows, ‖parent u‖ ^ 2) ≤ 2 * (∑ u ∈ rows, ‖tail u‖ ^ 2) +
      ∑ b ∈ reflectionBranches cutoff, ∫ ξ, ∑ u ∈ rows, ‖f b.1 b.2 u ξ‖ ^ 2
        ∂finiteRowBranchKernel (reflectionBranches cutoff) (fun _ => μ) (fun _ => weight) b := by
  let c : (ℕ × Bool) → ι → Ω → ℂ := fun b u =>
    fixedLineCoefficient (selected u b.1) (fun line => coefficient b.1 line u) b.2
  have hrange (b : ℕ × Bool) (hb : b ∈ reflectionBranches cutoff) :
      b.1 ∈ Finset.range (cutoff + 1) := (Finset.mem_product.mp hb).1
  have h := finite_rows_branch_integrals_energy_le
    (reflectionBranches cutoff) (fun _ => μ) rows (fun _ => weight)
    (fun _ _ => hm) (fun _ _ => hw) (fun _ _ => hi) c
    (fun b u => f b.1 b.2 u)
    (fun b hb u hu => hf b.1 (hrange b hb) b.2 u hu)
    (fun b hb u hu => fixedLineCoefficient_integrable μ (selected u b.1)
      (fun line => coefficient b.1 line u) (fun line => f b.1 line u)
      (hint b.1 (hrange b hb) u hu) b.2)
    (fun b hb u hu => Filter.Eventually.of_forall
      (fixedLineCoefficient_bound (selected u b.1) (fun line => coefficient b.1 line u)
        weight hw (hc b.1 (hrange b hb) u hu) b.2)) parent tail (by
      intro u hu
      rw [hparent u hu]
      congr 1
      exact (reflectionBranches_integral_sum μ cutoff (selected u)
        (fun j line => coefficient j line u) (fun j line => f j line u)).symm)
  simpa only [integral_finiteRowBranchKernel, ← Finset.mul_sum] using h

section CommonKernel

variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]

/-- One fixed numerical parameter space for every cutoff and every row. -/
def reflectionCommonKernel (μ : Measure Ω) (weight : Ω → ℝ) (cutoff : ℕ) :
    Measure ((ℕ × Bool) × Ω) :=
  finiteBranchMeasure (reflectionBranches cutoff)
    (finiteRowBranchKernel (reflectionBranches cutoff) (fun _ => μ) (fun _ => weight))

theorem reflectionCommonKernel_finite (μ : Measure Ω) (weight : Ω → ℝ) (cutoff : ℕ)
    (hw : ∀ ξ, 0 ≤ weight ξ) (hi : Integrable weight μ) :
    IsFiniteMeasure (reflectionCommonKernel μ weight cutoff) := by
  letI : ∀ b, IsFiniteMeasure
      (finiteRowBranchKernel (reflectionBranches cutoff) (fun _ => μ) (fun _ => weight) b) :=
    fun b => finiteRowBranchKernel_finite (reflectionBranches cutoff)
      (fun _ => μ) (fun _ => weight) b hw hi
  exact finiteBranchMeasure_finite _ _

/-- The complete common measure has the exact square-of-L1 mass and
the exact full finite branch factor. The original row count is absent. -/
theorem reflectionCommonKernel_mass (μ : Measure Ω) (weight : Ω → ℝ) (cutoff : ℕ)
    (hm : Measurable weight) (hw : ∀ ξ, 0 ≤ weight ξ) (hi : Integrable weight μ) :
    (reflectionCommonKernel μ weight cutoff).real Set.univ =
      8 * ((cutoff + 1 : ℕ) : ℝ) ^ 2 * (∫ ξ, weight ξ ∂μ) ^ 2 := by
  letI : ∀ b, IsFiniteMeasure
      (finiteRowBranchKernel (reflectionBranches cutoff) (fun _ => μ) (fun _ => weight) b) :=
    fun b => finiteRowBranchKernel_finite (reflectionBranches cutoff)
      (fun _ => μ) (fun _ => weight) b hw hi
  rw [reflectionCommonKernel, finiteBranchMeasure_mass]
  simp_rw [finiteRowBranchKernel_mass (reflectionBranches cutoff)
    (fun _ => μ) (fun _ => weight) _ hm hw]
  simp [reflectionBranches_card, pow_two]
  <;> ring

theorem reflectionCommonKernel_integrable (μ : Measure Ω) (weight : Ω → ℝ)
    (cutoff : ℕ) (value : (ℕ × Bool) × Ω → ℝ)
    (hi : ∀ b ∈ reflectionBranches cutoff,
      Integrable (fun ξ => value (b, ξ)) (rowEnergyKernel μ weight)) :
    Integrable value (reflectionCommonKernel μ weight cutoff) := by
  apply finiteBranchMeasure_integrable
  intro b hb
  exact (hi b hb).smul_measure_nnreal

theorem integral_reflectionCommonKernel (μ : Measure Ω) (weight : Ω → ℝ)
    (cutoff : ℕ) (value : (ℕ × Bool) × Ω → ℝ)
    (hi : ∀ b ∈ reflectionBranches cutoff,
      Integrable (fun ξ => value (b, ξ)) (rowEnergyKernel μ weight)) :
    (∫ x, value x ∂reflectionCommonKernel μ weight cutoff) =
      ∑ b ∈ reflectionBranches cutoff, ∫ ξ, value (b, ξ)
        ∂finiteRowBranchKernel (reflectionBranches cutoff) (fun _ => μ) (fun _ => weight) b :=
  integral_finiteBranchMeasure _ _ value (fun b hb => (hi b hb).smul_measure_nnreal)

/-- Geometric assertions on the actual children pass through the finite
union of numerical branches, without a measurable child-model map. -/
theorem ae_reflectionCommonKernel (μ : Measure Ω) (weight : Ω → ℝ)
    (cutoff : ℕ) {p : (ℕ × Bool) × Ω → Prop}
    (hp : ∀ b ∈ reflectionBranches cutoff,
      ∀ᵐ ξ ∂rowEnergyKernel μ weight, p (b, ξ)) :
    ∀ᵐ x ∂reflectionCommonKernel μ weight cutoff, p x := by
  apply ae_finiteBranchMeasure
  intro b hb
  exact Measure.ae_smul_measure
    (c := (2 * ((reflectionBranches cutoff).card : ℝ≥0))) (hp b hb)

end CommonKernel

end HeckeSkeleton.Moments.EngineInduction
