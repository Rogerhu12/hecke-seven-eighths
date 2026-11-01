import HeckePort.Moments.MobiusRegroup
import HeckePort.Moments.Descent.Fibers
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Pool

/-!
# Separating complete-support children after the genuine transform

The common-support identity is used on its genuine residual-coprime
partition.  Only then is the residual coprimality condition expanded by
the complete ideal Moebius sum.  The finite phase expansion is a precise
pointwise input of MOM_BASE.  It is not a bound on any parent or child
energy.  Every original coefficient, including a centered rectangle,
remains intact in the resulting divisor polynomials.

The analytic kernel is separated only after truncation of the genuine
orbital sum.  This module gives the exact finite separation and the paired
Cauchy estimate.  It does not assume a parent-to-child energy inequality.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace HeckeSkeleton.Moments.EngineStep

open NumberField UniqueFactorizationMonoid
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

variable {K : Type*} [Field K] [NumberField K]

/-- The literal full divisor restriction, retaining the complete coefficient. -/
def divisorPolynomial {ι H : Type*} (columns : Finset ι)
    (ideals : ι → Ideal (𝓞 K)) (D : Ideal (𝓞 K)) (c phase : ι → ℂ)
    (column : ι → H → ℂ) (h : H) : ℂ :=
  ∑ i ∈ columns, if D ∣ ideals i then c i * phase i * column i h else 0

theorem divisor_pair_product {ι κ H : Type*}
    (leftColumns : Finset ι) (rightColumns : Finset κ)
    (leftIdeals : ι → Ideal (𝓞 K)) (rightIdeals : κ → Ideal (𝓞 K))
    (D : Ideal (𝓞 K)) (c leftPhase : ι → ℂ) (d rightPhase : κ → ℂ)
    (leftColumn : ι → H → ℂ) (rightColumn : κ → H → ℂ) (h : H) :
    (∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
      if D ∣ leftIdeals i ∧ D ∣ rightIdeals j then
        (c i * leftPhase i * leftColumn i h) *
          star (d j * rightPhase j * rightColumn j h) else 0) =
      divisorPolynomial leftColumns leftIdeals D c leftPhase leftColumn h *
        star (divisorPolynomial rightColumns rightIdeals D d rightPhase rightColumn h) := by
  unfold divisorPolynomial
  rw [star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hL : D ∣ leftIdeals i <;> by_cases hR : D ∣ rightIdeals j <;>
    simp only [hL, hR, and_self, false_and, and_false, ite_true, ite_false,
      zero_mul, mul_zero, star_zero]

/-- Exact separated children of the full correlation on its retained
common-support block.  The only arithmetic input is its pointwise common
support formula with the finite phase expansion supplied by MOM_BASE. -/
theorem full_correlation_divisor_children {ι κ γ H : Type*} [Fintype γ]
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
    (c : ι → ℂ) (d : κ → ℂ) (h : H) :
    (∑ i ∈ leftColumns, ∑ j ∈ rightColumns,
      (if IsCoprime (leftIdeals i) (rightIdeals j) then Corr i j h else 0) *
        (c i * star (d j))) =
      ∑ D ∈ divisorPool rightColumns rightIdeals,
        (moebius D : ℂ) * common h *
          ∑ χ : γ, phaseCoefficient χ *
            (divisorPolynomial leftColumns leftIdeals D c (leftPhase χ) leftColumn h *
              star (divisorPolynomial rightColumns rightIdeals D d
                (rightPhase χ) rightColumn h)) := by
  have hm := finite_correlation_mobius leftColumns rightColumns leftIdeals rightIdeals
    hRight (fun i j => Corr i j h)
    (fun i j => common h *
      (∑ χ : γ, phaseCoefficient χ * leftPhase χ i * star (rightPhase χ j)) *
        (leftColumn i h * star (rightColumn j h)))
    (fun i j hc => hcommon i j h hc) c d (fun _ _ => 1)
  simp only [mul_one] at hm
  rw [hm]
  apply Finset.sum_congr rfl
  intro D hD
  have hex (i : ι) (j : κ) :
      (if D ∣ leftIdeals i ∧ D ∣ rightIdeals j then
        common h * (∑ χ : γ, phaseCoefficient χ * leftPhase χ i * star (rightPhase χ j)) *
          (leftColumn i h * star (rightColumn j h)) * (c i * star (d j)) else 0) =
      ∑ χ : γ, common h * phaseCoefficient χ *
        (if D ∣ leftIdeals i ∧ D ∣ rightIdeals j then
          (c i * leftPhase χ i * leftColumn i h) *
            star (d j * rightPhase χ j * rightColumn j h) else 0) := by
    by_cases hc : D ∣ leftIdeals i ∧ D ∣ rightIdeals j
    · simp only [hc, and_self, ite_true, Finset.mul_sum, Finset.sum_mul, star_mul]
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
    · simp only [hc, ite_false, mul_zero, Finset.sum_const_zero]
  simp_rw [hex]
  simp_rw [Finset.sum_comm (s := rightColumns) (t := Finset.univ)]
  rw [Finset.sum_comm (s := leftColumns) (t := Finset.univ)]
  rw [mul_assoc (moebius D : ℂ) (common h)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  simp_rw [← Finset.mul_sum]
  rw [divisor_pair_product]
  ring

/-- Complex row scalars are handled by their actual absolute values in
both Cauchy halves; there is one common nonnegative row measure. -/
theorem complex_weighted_cauchy {H : Type*} (rows : Finset H)
    (q f g : H → ℂ) :
    ‖∑ h ∈ rows, q h * f h * star (g h)‖ ≤
      Real.sqrt (∑ h ∈ rows, ‖q h‖ * ‖f h‖ ^ 2) *
        Real.sqrt (∑ h ∈ rows, ‖q h‖ * ‖g h‖ ^ 2) := by
  have hf : (∑ h ∈ rows, (Real.sqrt ‖q h‖ * ‖f h‖) ^ 2) =
      ∑ h ∈ rows, ‖q h‖ * ‖f h‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  have hg : (∑ h ∈ rows, (Real.sqrt ‖q h‖ * ‖g h‖) ^ 2) =
      ∑ h ∈ rows, ‖q h‖ * ‖g h‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  calc
    _ ≤ ∑ h ∈ rows, ‖q h * f h * star (g h)‖ := norm_sum_le _ _
    _ = ∑ h ∈ rows,
        (Real.sqrt ‖q h‖ * ‖f h‖) * (Real.sqrt ‖q h‖ * ‖g h‖) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [norm_mul, norm_mul, norm_star]
      calc
        _ = (Real.sqrt ‖q h‖ * Real.sqrt ‖q h‖) * ‖f h‖ * ‖g h‖ := by
          rw [Real.mul_self_sqrt (norm_nonneg _)]
        _ = _ := by ring
    _ ≤ _ := by
      simpa only [hf, hg] using Real.sum_mul_le_sqrt_mul_sqrt rows
        (fun h => Real.sqrt ‖q h‖ * ‖f h‖) (fun h => Real.sqrt ‖q h‖ * ‖g h‖)

/-- Paired Cauchy is applied after the exact divisor and finite phase
expansion. The two norms keep their own complete centered coefficients. -/
theorem separated_children_bound {D γ H : Type*} [Fintype γ]
    (divisors : Finset D) (rows : Finset H)
    (μ : D → ℂ) (phase : γ → ℂ) (q : D → γ → H → ℂ)
    (left right : D → γ → H → ℂ) :
    ‖∑ d ∈ divisors, μ d * ∑ χ : γ, phase χ *
        ∑ h ∈ rows, q d χ h * left d χ h * star (right d χ h)‖ ≤
      ∑ d ∈ divisors, ‖μ d‖ * ∑ χ : γ, ‖phase χ‖ *
        (Real.sqrt (∑ h ∈ rows, ‖q d χ h‖ * ‖left d χ h‖ ^ 2) *
          Real.sqrt (∑ h ∈ rows, ‖q d χ h‖ * ‖right d χ h‖ ^ 2)) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro χ hχ
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (complex_weighted_cauchy rows _ _ _) (norm_nonneg _)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.full_correlation_divisor_children
#print axioms HeckeSkeleton.Moments.EngineStep.separated_children_bound
