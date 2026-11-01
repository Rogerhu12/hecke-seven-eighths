import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointKernel

/-!
# The complete correlation with its actual common kernel

The residual coprimality sum is expanded while the coupled kernel is still
present.  The resulting divisor and finite-character labels are genuine
finite sums.  Fourier separation and paired Cauchy are then applied to the
same kernel and the same row weight in every child.

The pointwise common-support formula is supplied by
`ActualChildren.generated_correlation_common_support`; it is an arithmetic
identity, not a parent-to-child energy estimate.  No absolute value is taken
before the residual coprimality expansion.
-/

noncomputable section
open scoped NumberField Classical BigOperators FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField UniqueFactorizationMonoid
open HeckePort.Moments.MobiusRegroup

variable {K : Type*} [Field K] [NumberField K]

/-- A divisor restriction on an entire column coefficient. -/
def kernelDivisorCoefficient {ι H : Type*} (ideals : ι → Ideal (𝓞 K))
    (D : Ideal (𝓞 K)) (c phase : ι → ℂ) (column : ι → H → ℂ)
    (h : H) (i : ι) : ℂ :=
  if D ∣ ideals i then c i * phase i * column i h else 0

/-- The exact row identity retains a completely arbitrary coupled kernel. -/
theorem full_correlation_kernel_row {ι κ γ H : Type*} [Fintype γ]
    (leftColumns : Finset ι) (rightColumns : Finset κ)
    (leftIdeals : ι → Ideal (𝓞 K)) (rightIdeals : κ → Ideal (𝓞 K))
    (hRight : ∀ j ∈ rightColumns, rightIdeals j ≠ ⊥)
    (Corr : ι → κ → H → ℂ) (common : H → ℂ)
    (phaseCoefficient : γ → ℂ) (leftPhase : γ → ι → ℂ) (rightPhase : γ → κ → ℂ)
    (leftColumn : ι → H → ℂ) (rightColumn : κ → H → ℂ)
    (hcommon : ∀ i j h, IsCoprime (leftIdeals i) (rightIdeals j) →
      Corr i j h = common h *
        (∑ χ : γ, phaseCoefficient χ * leftPhase χ i * star (rightPhase χ j)) *
          (leftColumn i h * star (rightColumn j h)))
    (c : ι → ℂ) (d : κ → ℂ) (h : H) (kernel : ι → κ → ℂ) :
    (∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
      (if IsCoprime (leftIdeals i) (rightIdeals j) then Corr i j h else 0) *
        (c i * star (d j)) * kernel i j) =
      ∑ D ∈ divisorPool rightColumns rightIdeals, (moebius D : ℂ) *
        ∑ χ : γ, phaseCoefficient χ *
          ∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
            common h * kernelDivisorCoefficient leftIdeals D c (leftPhase χ) leftColumn h i *
              star (kernelDivisorCoefficient rightIdeals D d (rightPhase χ) rightColumn h j) *
                kernel i j := by
  rw [finite_correlation_mobius leftColumns rightColumns leftIdeals rightIdeals
    hRight (fun i j => Corr i j h)
    (fun i j => common h *
      (∑ χ : γ, phaseCoefficient χ * leftPhase χ i * star (rightPhase χ j)) *
        (leftColumn i h * star (rightColumn j h)))
    (fun i j hc => hcommon i j h hc) c d kernel]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hex (i : ι) (j : κ) :
      (if D ∣ leftIdeals i ∧ D ∣ rightIdeals j then
        common h * (∑ χ : γ, phaseCoefficient χ * leftPhase χ i * star (rightPhase χ j)) *
          (leftColumn i h * star (rightColumn j h)) * (c i * star (d j)) * kernel i j else 0) =
        ∑ χ : γ, phaseCoefficient χ *
          (common h * kernelDivisorCoefficient leftIdeals D c (leftPhase χ) leftColumn h i *
            star (kernelDivisorCoefficient rightIdeals D d (rightPhase χ) rightColumn h j) *
              kernel i j) := by
    by_cases hi : D ∣ leftIdeals i <;> by_cases hj : D ∣ rightIdeals j
    · simp only [hi, hj, and_self, ite_true, kernelDivisorCoefficient,
        Finset.mul_sum, Finset.sum_mul, star_mul]
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
    all_goals simp only [hi, hj, false_and, and_false, ite_false,
      kernelDivisorCoefficient, star_zero, zero_mul, mul_zero, Finset.sum_const_zero]
  simp_rw [hex]
  simp_rw [Finset.sum_comm (s := rightColumns) (t := Finset.univ)]
  rw [Finset.sum_comm (s := leftColumns) (t := Finset.univ)]
  simp only [Finset.mul_sum]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Genuine finite divisor/character blocks of the coupled correlation form. -/
theorem full_correlation_kernel_children {ι κ γ H : Type*} [Fintype γ]
    (F : 𝓢(V, ℂ)) (rows : Finset H)
    (leftColumns : Finset ι) (rightColumns : Finset κ)
    (leftIdeals : ι → Ideal (𝓞 K)) (rightIdeals : κ → Ideal (𝓞 K))
    (hRight : ∀ j ∈ rightColumns, rightIdeals j ≠ ⊥)
    (Corr : ι → κ → H → ℂ) (common q : H → ℂ)
    (phaseCoefficient : γ → ℂ) (leftPhase : γ → ι → ℂ) (rightPhase : γ → κ → ℂ)
    (leftColumn : ι → H → ℂ) (rightColumn : κ → H → ℂ)
    (hcommon : ∀ i j h, IsCoprime (leftIdeals i) (rightIdeals j) →
      Corr i j h = common h *
        (∑ χ : γ, phaseCoefficient χ * leftPhase χ i * star (rightPhase χ j)) *
          (leftColumn i h * star (rightColumn j h)))
    (c : ι → ℂ) (d : κ → ℂ) (x : H → ι → V) (y : H → κ → V) :
    (∑ h ∈ rows, q h * ∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
      (if IsCoprime (leftIdeals i) (rightIdeals j) then Corr i j h else 0) *
        (c i * star (d j)) * F (x h i + y h j)) =
      ∑ D ∈ divisorPool rightColumns rightIdeals, (moebius D : ℂ) *
        ∑ χ : γ, phaseCoefficient χ *
          jointKernelPairing F rows leftColumns rightColumns (fun h => q h * common h)
            (kernelDivisorCoefficient leftIdeals D c (leftPhase χ) leftColumn)
            (kernelDivisorCoefficient rightIdeals D d (rightPhase χ) rightColumn) x y := by
  simp_rw [full_correlation_kernel_row leftColumns rightColumns leftIdeals rightIdeals
    hRight Corr common phaseCoefficient leftPhase rightPhase leftColumn rightColumn hcommon c d]
  simp only [jointKernelPairing, Finset.mul_sum]
  rw [Finset.sum_comm (s := rows) (t := divisorPool rightColumns rightIdeals)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm (s := rows) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- One actual Fourier measure controls both Cauchy halves after the full
residual coprimality sum.  The outer sums keep their exact coefficients. -/
theorem full_correlation_kernel_bound {ι κ γ H : Type*} [Fintype γ]
    (F : 𝓢(V, ℂ)) (rows : Finset H)
    (leftColumns : Finset ι) (rightColumns : Finset κ)
    (leftIdeals : ι → Ideal (𝓞 K)) (rightIdeals : κ → Ideal (𝓞 K))
    (hRight : ∀ j ∈ rightColumns, rightIdeals j ≠ ⊥)
    (Corr : ι → κ → H → ℂ) (common q : H → ℂ)
    (phaseCoefficient : γ → ℂ) (leftPhase : γ → ι → ℂ) (rightPhase : γ → κ → ℂ)
    (leftColumn : ι → H → ℂ) (rightColumn : κ → H → ℂ)
    (hcommon : ∀ i j h, IsCoprime (leftIdeals i) (rightIdeals j) →
      Corr i j h = common h *
        (∑ χ : γ, phaseCoefficient χ * leftPhase χ i * star (rightPhase χ j)) *
          (leftColumn i h * star (rightColumn j h)))
    (c : ι → ℂ) (d : κ → ℂ) (x : H → ι → V) (y : H → κ → V) :
    ‖∑ h ∈ rows, q h * ∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
      (if IsCoprime (leftIdeals i) (rightIdeals j) then Corr i j h else 0) *
        (c i * star (d j)) * F (x h i + y h j)‖ ≤
      ∑ D ∈ divisorPool rightColumns rightIdeals, ‖(moebius D : ℂ)‖ *
        ∑ χ : γ, ‖phaseCoefficient χ‖ * ∫ ξ : V, ‖(𝓕 F) ξ‖ *
          (Real.sqrt (jointColumnEnergy rows leftColumns (fun h => q h * common h)
            (kernelDivisorCoefficient leftIdeals D c (leftPhase χ) leftColumn) x ξ) *
          Real.sqrt (jointColumnEnergy rows rightColumns (fun h => q h * common h)
            (fun h j => star (kernelDivisorCoefficient rightIdeals D d
              (rightPhase χ) rightColumn h j)) y ξ)) := by
  rw [full_correlation_kernel_children F rows leftColumns rightColumns leftIdeals rightIdeals
    hRight Corr common q phaseCoefficient leftPhase rightPhase leftColumn rightColumn
    hcommon c d x y]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro D hD
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro χ hχ
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (joint_kernel_paired_cauchy F rows leftColumns rightColumns _ _ _ x y)
    (norm_nonneg _)

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.full_correlation_kernel_children
#print axioms HeckeSkeleton.Moments.EngineStep.full_correlation_kernel_bound
