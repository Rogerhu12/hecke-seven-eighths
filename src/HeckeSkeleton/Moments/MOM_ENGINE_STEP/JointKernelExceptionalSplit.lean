import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointKernel

/-!
# Exceptional rows are separated before paired Cauchy

The whole common-kernel form is partitioned on its original rows.
On the exceptional part the two complete Fourier polynomials are
estimated in the same row before summing.  Paired Cauchy is applied only
to the complementary rows.  Both terms use the original Fourier density
and the same continuous variable; all integrability is proved from the
actual Schwartz kernel and the finite whole coefficients.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def jointColumnPairMagnitude {H ι κ : Type*}
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) (ξ : V) : ℝ :=
  ∑ h ∈ rows, ‖q h‖ *
    ‖jointFourierColumn leftColumns (c h) (x h) ξ‖ *
      ‖jointFourierColumn rightColumns (d h) (y h) ξ‖

def jointColumnPairMass {H ι κ : Type*}
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ) : ℝ :=
  ∑ h ∈ rows, ‖q h‖ * (∑ a ∈ leftColumns, ‖c h a‖) *
    (∑ b ∈ rightColumns, ‖d h b‖)

theorem jointColumnPairMagnitude_nonneg {H ι κ : Type*}
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) (ξ : V) :
    0 ≤ jointColumnPairMagnitude rows leftColumns rightColumns q c d x y ξ :=
  Finset.sum_nonneg fun h _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

theorem continuous_jointColumnPairMagnitude {H ι κ : Type*}
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) :
    Continuous (jointColumnPairMagnitude rows leftColumns rightColumns q c d x y) := by
  apply continuous_finsetSum
  intro h hh
  exact (continuous_const.mul
    (continuous_jointFourierColumn leftColumns (c h) (x h)).norm).mul
    (continuous_jointFourierColumn rightColumns (d h) (y h)).norm

theorem jointColumnPairMagnitude_le_mass {H ι κ : Type*}
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) (ξ : V) :
    jointColumnPairMagnitude rows leftColumns rightColumns q c d x y ξ ≤
      jointColumnPairMass rows leftColumns rightColumns q c d := by
  apply Finset.sum_le_sum
  intro h hh
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (norm_jointFourierColumn_le leftColumns (c h) (x h) ξ)
      (norm_nonneg _))
    (norm_jointFourierColumn_le rightColumns (d h) (y h) ξ) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun a _ => norm_nonneg _))

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem joint_kernel_row_magnitude_integrable {H ι κ : Type*} (F : 𝓢(V, ℂ))
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) :
    Integrable (fun ξ : V => ‖(𝓕 F) ξ‖ *
      jointColumnPairMagnitude rows leftColumns rightColumns q c d x y ξ) := by
  apply ((𝓕 F).integrable (μ := (volume : Measure V))).norm.mul_bdd
    (c := jointColumnPairMass rows leftColumns rightColumns q c d)
    (continuous_jointColumnPairMagnitude rows leftColumns rightColumns q c d x y).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (jointColumnPairMagnitude_nonneg rows leftColumns rightColumns q c d x y ξ)]
    exact jointColumnPairMagnitude_le_mass rows leftColumns rightColumns q c d x y ξ

/-- Rowwise absolute values preserve the single centered saving.  This
estimate never replaces a sum of paired row magnitudes by two L2 sums. -/
theorem joint_kernel_rowwise_bound {H ι κ : Type*} (F : 𝓢(V, ℂ))
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) :
    ‖jointKernelPairing F rows leftColumns rightColumns q c d x y‖ ≤
      ∫ ξ : V, ‖(𝓕 F) ξ‖ *
        jointColumnPairMagnitude rows leftColumns rightColumns q c
          (fun h b => star (d h b)) x y ξ := by
  rw [joint_kernel_finite_separation]
  apply norm_integral_le_of_norm_le
    (joint_kernel_row_magnitude_integrable F rows leftColumns rightColumns q c
      (fun h b => star (d h b)) x y)
  exact Filter.Eventually.of_forall fun ξ => by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [jointColumnPairMagnitude, norm_mul] using
      norm_sum_le rows (fun h => q h *
        jointFourierColumn leftColumns (c h) (x h) ξ *
        jointFourierColumn rightColumns (fun b => star (d h b)) (y h) ξ)

/-- The actual common-kernel form is partitioned before any Cauchy
inequality.  Its complete centered columns remain unchanged. -/
theorem joint_kernel_row_partition {H ι κ : Type*} (F : 𝓢(V, ℂ))
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) (exceptional : H → Prop) :
    jointKernelPairing F rows leftColumns rightColumns q c d x y =
      jointKernelPairing F (rows.filter exceptional) leftColumns rightColumns q c d x y +
        jointKernelPairing F (rows.filter fun h => ¬exceptional h)
          leftColumns rightColumns q c d x y := by
  exact (Finset.sum_filter_add_sum_filter_not rows exceptional _).symm

/-- A single genuine Fourier integral carries both alternatives: the
exceptional paired row magnitudes and the actual nonexceptional Cauchy
energies.  No mixed exceptional/nonexceptional cross terms are created. -/
theorem joint_kernel_exceptional_split {H ι κ : Type*} (F : 𝓢(V, ℂ))
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) (exceptional : H → Prop) :
    ‖jointKernelPairing F rows leftColumns rightColumns q c d x y‖ ≤
      ∫ ξ : V, ‖(𝓕 F) ξ‖ *
        (jointColumnPairMagnitude (rows.filter exceptional) leftColumns rightColumns q c
          (fun h b => star (d h b)) x y ξ +
          Real.sqrt (jointColumnEnergy (rows.filter fun h => ¬exceptional h)
            leftColumns q c x ξ) *
          Real.sqrt (jointColumnEnergy (rows.filter fun h => ¬exceptional h)
            rightColumns q (fun h b => star (d h b)) y ξ)) := by
  let cstar := fun h b => star (d h b)
  have he := joint_kernel_rowwise_bound F (rows.filter exceptional)
    leftColumns rightColumns q c d x y
  have hn := joint_kernel_paired_cauchy F (rows.filter fun h => ¬exceptional h)
    leftColumns rightColumns q c d x y
  have hE := joint_kernel_row_magnitude_integrable F (rows.filter exceptional)
    leftColumns rightColumns q c cstar x y
  have hN := joint_kernel_energy_integrable F (rows.filter fun h => ¬exceptional h)
    leftColumns rightColumns q c cstar x y
  calc
    _ ≤ ‖jointKernelPairing F (rows.filter exceptional)
        leftColumns rightColumns q c d x y‖ +
      ‖jointKernelPairing F (rows.filter fun h => ¬exceptional h)
        leftColumns rightColumns q c d x y‖ := by
      rw [joint_kernel_row_partition F rows leftColumns rightColumns q c d x y exceptional]
      exact norm_add_le _ _
    _ ≤ _ := (add_le_add he hn).trans (by
      rw [← integral_add hE hN]
      apply le_of_eq
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        dsimp only [cstar]
        ring)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.joint_kernel_rowwise_bound
#print axioms HeckeSkeleton.Moments.EngineStep.joint_kernel_exceptional_split

