module

public import HeckeSkeleton.Moments.MOM_INV_STEP.MellinSeparation

/-!
# Mellin identities on complete norm pools

The fixed cutoff multiplies the true inverse Mellin integral. Outside
the original W-support the entire integral vanishes; its integrand is
not incorrectly identified with the unseparated source. This allows
complete squarefree pools before either positive energy is formed.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.MellinCompleteTests

open MeasureTheory
open MellinSchwartz MellinWeightedTests MellinSeparation CommonKernel
open scoped Classical BigOperators

theorem scaled_weighted_phase_all (a t u U : ℝ) (hu : 0 < u) (hU : 0 < U) :
    ((U ^ a : ℝ) : ℂ) * columnPhase t (Real.log U) *
        weightedTest a t (u / U) =
      cutoff (u / U) * ((u ^ a : ℝ) : ℂ) * columnPhase t (Real.log u) := by
  rw [weightedTest_eq]
  have hp : U ^ a * (u / U) ^ a = u ^ a := by
    rw [← Real.mul_rpow hU.le (div_pos hu hU).le]
    congr 1
    field_simp [hU.ne']
  have hl : Real.log U + Real.log (u / U) = Real.log u := by
    rw [Real.log_div hu.ne' hU.ne']
    ring
  calc
    _ = cutoff (u / U) * ((U ^ a * (u / U) ^ a : ℝ) : ℂ) *
        (columnPhase t (Real.log U) * columnPhase t (Real.log (u / U))) := by
      rw [Complex.ofReal_mul]
      ring
    _ = _ := by rw [hp, ← columnPhase_add, hl]

theorem cutoff_source (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (v u X U : ℝ) (hv : 0 < v) (hU : 0 < U) (hscale : X = v * U) :
    cutoff (u / U) * W (v * u / X) = W (v * u / X) := by
  have hr : v * u / X = u / U := by rw [hscale]; field_simp [hv.ne', hU.ne']
  rw [hr]
  by_cases hzero : W (u / U) = 0
  · rw [hzero, mul_zero]
  · have hmem := hW (subset_closure (Function.mem_support.mpr hzero))
    rw [cutoff_one hmem.1 hmem.2, one_mul]

/-- Valid for every positive u, including all points outside [U,2U]. -/
theorem separated_source_complete (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (a τ v u X U : ℝ)
    (hv : 0 < v) (hu : 0 < u) (hU : 0 < U) (hscale : X = v * U) :
    W (v * u / X) * ((u ^ a : ℝ) : ℂ) * columnPhase τ (Real.log u) =
      ∫ t : ℝ, density W hW t * columnPhase t (Real.log v) *
        columnPhase t (-Real.log X) *
        (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U) *
          weightedTest a (t + τ) (u / U)) := by
  have hX : 0 < X := by rw [hscale]; exact mul_pos hv hU
  calc
    _ = cutoff (u / U) *
        (W (v * u / X) * ((u ^ a : ℝ) : ℂ) * columnPhase τ (Real.log u)) := by
      rw [← mul_assoc, ← mul_assoc, cutoff_source W hW v u X U hv hU hscale]
    _ = ∫ t : ℝ, cutoff (u / U) *
        (density W hW t * columnPhase t (Real.log v) *
          columnPhase t (Real.log u) * columnPhase t (-Real.log X) *
          ((u ^ a : ℝ) : ℂ) * columnPhase τ (Real.log u)) := by
      rw [source_inverse W hW v u X hv hu hX,
        integral_const_mul, integral_mul_const, integral_mul_const]
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [scaled_weighted_phase_all a (t + τ) u U hu hU,
          ← columnPhase_frequency_add]
        ring

theorem integrable_complete (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (a τ v u X U : ℝ)
    (hu : 0 < u) (hU : 0 < U) :
    Integrable (fun t : ℝ => density W hW t * columnPhase t (Real.log v) *
      columnPhase t (-Real.log X) *
      (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U) *
        weightedTest a (t + τ) (u / U))) := by
  have hi := (((integrable_source W hW v u X).mul_const ((u ^ a : ℝ) : ℂ)).mul_const
    (columnPhase τ (Real.log u))).const_mul (cutoff (u / U))
  convert hi using 1
  funext t
  rw [scaled_weighted_phase_all a (t + τ) u U hu hU,
    ← columnPhase_frequency_add]
  ring

/-- Finite complete pools can be moved through the true Mellin integral.
There is no pointwise dyadic restriction on the pool elements. -/
theorem finite_source_complete {ι : Type*} (T : Finset ι)
    (weight : ι → ℂ) (height : ι → ℝ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (a τ v X U : ℝ) (hv : 0 < v) (hU : 0 < U) (hscale : X = v * U)
    (hheight : ∀ i ∈ T, 0 < height i) :
    (∑ i ∈ T, weight i *
      (W (v * height i / X) * ((height i ^ a : ℝ) : ℂ) *
        columnPhase τ (Real.log (height i)))) =
      ∫ t : ℝ, density W hW t * columnPhase t (Real.log v) *
        columnPhase t (-Real.log X) *
        (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U)) *
          ∑ i ∈ T, weight i * weightedTest a (t + τ) (height i / U) := by
  let F : ι → ℝ → ℂ := fun i t =>
    weight i * (density W hW t * columnPhase t (Real.log v) *
      columnPhase t (-Real.log X) *
      (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U) *
        weightedTest a (t + τ) (height i / U)))
  have hF (i : ι) (hi : i ∈ T) : Integrable (F i) :=
    (integrable_complete W hW a τ v (height i) X U (hheight i hi) hU).const_mul _
  calc
    _ = ∑ i ∈ T, ∫ t : ℝ, F i t := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [separated_source_complete W hW a τ v (height i) X U
        hv (hheight i hi) hU hscale, integral_const_mul]
    _ = ∫ t : ℝ, ∑ i ∈ T, F i t := (integral_finsetSum T hF).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only [F]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring

end HeckeSkeleton.Moments.MOM_INV_STEP.MellinCompleteTests

end

