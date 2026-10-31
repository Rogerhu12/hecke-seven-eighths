import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Interface

/-!
# Centering on the original paired row set

Changing the two rectangle lengths leaves `pairedRows` unchanged: its
definition uses the total row width and the zero/positive slot regime,
not the two plain lengths.  The comparison node below retains the entire
`MomentData`, including both tests, every slot and the common ideal mask.

The triangle inequality therefore supplies an actual finite-energy
decomposition.  The ordinary comparison is at the same width and slot
regime as the centered node, and is earlier in the finite stage order.
These are algebraic parts of parent assembly; no analytic estimate for
either summand is assumed here.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open scoped BigOperators Classical

universe u

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

namespace Node

/-- Only the two plain rectangle lengths change. -/
def comparisonParameters (n : Node K ω ψ) : RealParameters :=
  { n.parameters with n₁ := n.comparison₁, n₂ := n.comparison₂ }

/-- The ordinary comparison uses the identical polynomial data and mask. -/
def comparisonOrdinary (n : Node K ω ψ) : Node K ω ψ :=
  ordinary n.data n.comparisonParameters

@[simp] theorem comparison_rows (n : Node K ω ψ) (U : ℝ) :
    pairedRows n.data n.comparisonParameters U =
      pairedRows n.data n.parameters U := rfl

@[simp] theorem comparison_width (n : Node K ω ψ) :
    n.comparisonOrdinary.width = n.width := rfl

@[simp] theorem comparison_slots (n : Node K ω ψ) :
    n.comparisonOrdinary.parameters.z = n.parameters.z := rfl

@[simp] theorem comparison_centered (n : Node K ω ψ) :
    n.comparisonOrdinary.centered = false := rfl

/-- The pointwise squared triangle inequality, before summing rows. -/
theorem norm_sq_le_two_sub_sq_add_two_sq (a b : ℂ) :
    ‖a‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have htriangle : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    calc
      ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _
  have hsquare := mul_le_mul htriangle htriangle (norm_nonneg a)
    (add_nonneg (norm_nonneg (a - b)) (norm_nonneg b))
  nlinarith [sq_nonneg (‖a - b‖ - ‖b‖)]

/-- Centering decomposes the actual paired energy on one unchanged row
set.  All slot factors remain inside the rowwise square. -/
theorem pairedEnergy_le_centered_add_comparison (n : Node K ω ψ)
    (hcentered : n.centered = true) (U t : ℝ) :
    pairedEnergy n.data n.parameters U t ≤
      2 * n.energy U t + 2 * n.comparisonOrdinary.energy U t := by
  let rows := pairedRows n.data n.parameters U
  let p := fun u =>
    plainPolynomial n.data n.data.plainTest₁ u (U ^ n.parameters.n₁) t *
      plainPolynomial n.data n.data.plainTest₂ u (U ^ n.parameters.n₂) t
  let q := fun u =>
    plainPolynomial n.data n.data.plainTest₁ u (U ^ n.comparison₁) t *
      plainPolynomial n.data n.data.plainTest₂ u (U ^ n.comparison₂) t
  let s := fun u => slotProduct n.data u U t
  change (∑ u ∈ rows, ‖p u * s u‖ ^ 2) ≤
    2 * (∑ u ∈ rows, ‖(p u - if n.centered then q u else 0) * s u‖ ^ 2) +
    2 * (∑ u ∈ rows, ‖(q u - 0) * s u‖ ^ 2)
  simp only [hcentered, ite_true, sub_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  simpa only [sub_mul] using
    norm_sq_le_two_sub_sq_add_two_sq (p u * s u) (q u * s u)

end Node

namespace PolynomialSystem

variable {σ W : ℝ}

theorem comparison_same_slots (S : PolynomialSystem.{u} K ω ψ σ W)
    (child parent : S.Label)
    (hchild : S.node child = (S.node parent).comparisonOrdinary) :
    (S.schedule child).slots = (S.schedule parent).slots := by
  change (if (S.node child).parameters.z = 0 then (0 : Fin 2) else 1) = _
  simp only [hchild, Node.comparison_slots]

theorem comparison_same_band (S : PolynomialSystem.{u} K ω ψ σ W)
    (child parent : S.Label)
    (hchild : S.node child = (S.node parent).comparisonOrdinary) :
    (S.schedule child).band = (S.schedule parent).band := by
  apply Fin.ext
  change widthBand σ (S.node child).width = widthBand σ (S.node parent).width
  rw [hchild, Node.comparison_width]

/-- Comparison is an earlier-stage call at identical width and slot
regime; no strict-width decrease is claimed for this edge. -/
theorem comparison_earlier (S : PolynomialSystem.{u} K ω ψ σ W)
    (child parent : S.Label)
    (hchild : S.node child = (S.node parent).comparisonOrdinary)
    (hcentered : (S.node parent).centered = true) :
    (S.schedule child).Earlier (S.schedule parent) := by
  apply State.comparison (S.comparison_same_slots child parent hchild)
    (S.comparison_same_band child parent hchild)
  · change (if (S.node child).centered then (1 : Fin 2) else 0).val = 0
    simp only [hchild, Node.comparison_centered, Bool.false_eq_true, ite_false,
      Fin.val_zero]
  · change (if (S.node parent).centered then (1 : Fin 2) else 0).val = 1
    simp only [hcentered, ite_true, Fin.val_one]

end PolynomialSystem

end HeckeSkeleton.Moments.EngineInduction
