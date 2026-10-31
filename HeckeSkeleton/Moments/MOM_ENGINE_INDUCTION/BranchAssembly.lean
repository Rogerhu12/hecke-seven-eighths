import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.BranchedIntegralRecursion
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Centering
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Measure.Real

/-!
# Combine the centered and comparison reductions before recursion

The actual ordinary energy is at most twice the centered energy plus
twice the comparison energy.  This file substitutes the two local
reductions into that inequality. Their children are concatenated, and
each original positive kernel is multiplied by two.

The centered node and the raw comparison node may have exactly the same
induction state as the ordinary parent. Neither is introduced as a
recursive child: the returned children are those already produced by
their local reductions. In particular, the comparison reduction must
contain its actual reflection and its own earlier children.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators Classical NNReal

namespace HeckeSkeleton.Moments.EngineInduction

universe u v

namespace BranchedIntegralAt

variable {X : Type u} {Ω : Type v} {bands : ℕ} [MeasurableSpace Ω]
variable {value : X → ℝ} {schedule : X → State bands} {parent center comparison : X}

private theorem doubled_branch_sum (step : BranchedIntegralAt (Ω := Ω) value schedule center) :
    (∑ b, ((∫ ξ, value (step.left b ξ) ∂((2 : ℝ≥0) • step.kernel b)) +
      ∫ ξ, value (step.right b ξ) ∂((2 : ℝ≥0) • step.kernel b)) / 2) =
      2 * ∑ b, ((∫ ξ, value (step.left b ξ) ∂step.kernel b) +
        ∫ ξ, value (step.right b ξ) ∂step.kernel b) / 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  norm_num [NNReal.smul_def] <;> ring

/-- Substitute both complete local reductions into the actual centering
inequality. The two intermediate nodes are not recursive calls. -/
def combine
    (centerStep : BranchedIntegralAt (Ω := Ω) value schedule center)
    (comparisonStep : BranchedIntegralAt (Ω := Ω) value schedule comparison)
    (hcenterState : schedule center = schedule parent)
    (hcomparisonState : schedule comparison = schedule parent)
    (hdecomposition : value parent ≤ 2 * value center + 2 * value comparison) :
    BranchedIntegralAt (Ω := Ω) value schedule parent where
  branches := centerStep.branches + comparisonStep.branches
  kernel := Fin.addCases
    (fun b => (2 : ℝ≥0) • centerStep.kernel b)
    (fun b => (2 : ℝ≥0) • comparisonStep.kernel b)
  finite := by
    intro b
    refine Fin.addCases ?_ ?_ b
    · intro i
      simp only [Fin.addCases_left]
      letI : IsFiniteMeasure (centerStep.kernel i) := centerStep.finite i
      infer_instance
    · intro i
      simp only [Fin.addCases_right]
      letI : IsFiniteMeasure (comparisonStep.kernel i) := comparisonStep.finite i
      infer_instance
  left := Fin.addCases centerStep.left comparisonStep.left
  right := Fin.addCases centerStep.right comparisonStep.right
  remainder := 2 * centerStep.remainder + 2 * comparisonStep.remainder
  left_integrable := by
    intro b
    refine Fin.addCases ?_ ?_ b
    · intro i
      simpa only [Fin.addCases_left] using
        (centerStep.left_integrable i).smul_measure_nnreal (c := (2 : ℝ≥0))
    · intro i
      simpa only [Fin.addCases_right] using
        (comparisonStep.left_integrable i).smul_measure_nnreal (c := (2 : ℝ≥0))
  right_integrable := by
    intro b
    refine Fin.addCases ?_ ?_ b
    · intro i
      simpa only [Fin.addCases_left] using
        (centerStep.right_integrable i).smul_measure_nnreal (c := (2 : ℝ≥0))
    · intro i
      simpa only [Fin.addCases_right] using
        (comparisonStep.right_integrable i).smul_measure_nnreal (c := (2 : ℝ≥0))
  left_earlier := by
    intro b
    refine Fin.addCases ?_ ?_ b
    · intro i
      simp only [Fin.addCases_left]
      apply Measure.ae_smul_measure (c := (2 : ℝ≥0))
      simpa only [hcenterState] using centerStep.left_earlier i
    · intro i
      simp only [Fin.addCases_right]
      apply Measure.ae_smul_measure (c := (2 : ℝ≥0))
      simpa only [hcomparisonState] using comparisonStep.left_earlier i
  right_earlier := by
    intro b
    refine Fin.addCases ?_ ?_ b
    · intro i
      simp only [Fin.addCases_left]
      apply Measure.ae_smul_measure (c := (2 : ℝ≥0))
      simpa only [hcenterState] using centerStep.right_earlier i
    · intro i
      simp only [Fin.addCases_right]
      apply Measure.ae_smul_measure (c := (2 : ℝ≥0))
      simpa only [hcomparisonState] using comparisonStep.right_earlier i
  estimate := by
    simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
    rw [doubled_branch_sum centerStep, doubled_branch_sum comparisonStep]
    linarith [centerStep.estimate, comparisonStep.estimate]

@[simp] theorem combine_remainder
    (centerStep : BranchedIntegralAt (Ω := Ω) value schedule center)
    (comparisonStep : BranchedIntegralAt (Ω := Ω) value schedule comparison)
    (hcenterState : schedule center = schedule parent)
    (hcomparisonState : schedule comparison = schedule parent)
    (hdecomposition : value parent ≤ 2 * value center + 2 * value comparison) :
    (centerStep.combine comparisonStep hcenterState hcomparisonState hdecomposition).remainder =
      2 * centerStep.remainder + 2 * comparisonStep.remainder := rfl

/-- Only the two centering coefficients are added to the genuine kernel
mass. There is no extra charge for the number of branches or the two
intermediate nodes. -/
theorem combine_mass
    (centerStep : BranchedIntegralAt (Ω := Ω) value schedule center)
    (comparisonStep : BranchedIntegralAt (Ω := Ω) value schedule comparison)
    (hcenterState : schedule center = schedule parent)
    (hcomparisonState : schedule comparison = schedule parent)
    (hdecomposition : value parent ≤ 2 * value center + 2 * value comparison) :
    (∑ b, ((centerStep.combine comparisonStep hcenterState hcomparisonState
      hdecomposition).kernel b).real Set.univ) =
      2 * (∑ b, (centerStep.kernel b).real Set.univ) +
        2 * (∑ b, (comparisonStep.kernel b).real Set.univ) := by
  simp [combine, Fin.sum_univ_add, Finset.mul_sum]

end BranchedIntegralAt

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- The actual centering inequality survives the common true row-width
normalization. Both comparison rectangles still use the same data. -/
theorem Node.normalizedEnergy_le_centered_add_comparison (n : Node K ω ψ)
    (hcentered : n.centered = true) (U t : ℝ) (hU : 0 < U) :
    (Node.ordinary n.data n.parameters).normalizedEnergy U t ≤
      2 * n.normalizedEnergy U t + 2 * n.comparisonOrdinary.normalizedEnergy U t := by
  have h := div_le_div_of_nonneg_right
    (n.pairedEnergy_le_centered_add_comparison hcentered U t)
    (Real.rpow_pos_of_pos hU n.width).le
  unfold Node.normalizedEnergy
  rw [Node.ordinary_energy, Node.comparison_width]
  simpa only [add_div, mul_div_assoc] using h

/-- A complete ordinary-parent reduction from the centered and actual
comparison local reductions. The latter must already contain the genuine
reflection, if reflection is needed to produce earlier children. -/
def PolynomialSystem.centeredComparisonBranch
    {Ω : Type v} [MeasurableSpace Ω] {σ W : ℝ}
    (S : PolynomialSystem.{u} K ω ψ σ W) (U t : ℝ) (hU : 0 < U)
    (parent center comparison : S.Label)
    (hcentered : (S.node center).centered = true)
    (hparent : S.node parent = Node.ordinary (S.node center).data (S.node center).parameters)
    (hcomparison : S.node comparison = (S.node center).comparisonOrdinary)
    (hcenterState : S.schedule center = S.schedule parent)
    (hcomparisonState : S.schedule comparison = S.schedule parent)
    (centerStep : BranchedIntegralAt (Ω := Ω)
      (fun x => (S.node x).normalizedEnergy U t) S.schedule center)
    (comparisonStep : BranchedIntegralAt (Ω := Ω)
      (fun x => (S.node x).normalizedEnergy U t) S.schedule comparison) :
    BranchedIntegralAt (Ω := Ω)
      (fun x => (S.node x).normalizedEnergy U t) S.schedule parent :=
  centerStep.combine comparisonStep hcenterState hcomparisonState (by
    simpa only [hparent, hcomparison] using
      (S.node center).normalizedEnergy_le_centered_add_comparison hcentered U t hU)

end HeckeSkeleton.Moments.EngineInduction
