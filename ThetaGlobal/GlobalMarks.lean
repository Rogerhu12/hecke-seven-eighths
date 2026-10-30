import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring

/-!
# Finite mark insertion and the global invariance step

This file proves the algebraic and measure-theoretic parts of inserting
whole-index marks.  It does not assume a theta reflection identity.

The hypotheses of `weighted_weyl_average` are rational Weyl invariance
of a function on the group.  The hypotheses of
`angular_constant_term_vanishes` are a measure-preserving rotation,
radial invariance of the constant term, and a nontrivial angular
eigencharacter.  Constructing the required theta function and its
Whittaker expansion is deliberately outside these lemmas.

All powers and masks retain their literal zero values.  In particular,
the zeroth ordinary digit is the unit mask, not a constant character.
-/

noncomputable section
open scoped BigOperators

namespace ThetaGlobal.GlobalMarks

section FiniteAlgebra

variable {P I R : Type*} [CommRing R]

/-- Multiplying finitely many Boolean masks is the mask of their conjunction. -/
theorem prod_boolean_mask (s : Finset P) (p : P → Prop) [DecidablePred p] :
    (∏ q ∈ s, (if p q then (1 : R) else 0)) =
      if ∀ q ∈ s, p q then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert q s hq ih =>
    by_cases hp : p q
    · simp [Finset.prod_insert hq, ih, hp]
    · simp [Finset.prod_insert hq, hp]

/-- Whole-index divisibility marks are a finite alternating sum of
whole-index nondivisibility masks.  The predicate can literally be
`q.asIdeal ∣ A`, so no squarefree assumption is used here. -/
theorem marks_inclusion_exclusion (s : Finset P) (p : P → Prop)
    [DecidablePred p] :
    (if ∀ q ∈ s, p q then (1 : R) else 0) =
      ∑ t ∈ s.powerset, (-1 : R) ^ t.card *
        (if ∀ q ∈ t, ¬p q then 1 else 0) := by
  classical
  calc
    (if ∀ q ∈ s, p q then (1 : R) else 0) =
        ∏ q ∈ s, (1 - (if ¬p q then (1 : R) else 0)) := by
      rw [← prod_boolean_mask]
      apply Finset.prod_congr rfl
      intro q hq
      by_cases h : p q <;> simp [h]
    _ = ∑ t ∈ s.powerset, (-1 : R) ^ t.card *
        (if ∀ q ∈ t, ¬p q then 1 else 0) := by
      rw [Finset.prod_sub]
      simp only [Finset.prod_const_one, mul_one, prod_boolean_mask]

/-- Pointwise insertion of marks commutes with every other coefficient,
including a whole-index puncture mask. -/
theorem weighted_marks_inclusion_exclusion (s : Finset P) (p : P → Prop)
    [DecidablePred p] (a : R) :
    a * (if ∀ q ∈ s, p q then (1 : R) else 0) =
      ∑ t ∈ s.powerset, (-1 : R) ^ t.card *
        (a * (if ∀ q ∈ t, ¬p q then 1 else 0)) := by
  rw [marks_inclusion_exclusion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- The same formula for any finite collection of arithmetic indices. -/
theorem sum_marked_eq_alternating_unmarked (indices : Finset I)
    (marks : Finset P) (divides : P → I → Prop)
    [∀ q, DecidablePred (divides q)] (a : I → R) :
    (∑ i ∈ indices, a i * (if ∀ q ∈ marks, divides q i then (1 : R) else 0)) =
      ∑ t ∈ marks.powerset, (-1 : R) ^ t.card *
        ∑ i ∈ indices, a i * (if ∀ q ∈ t, ¬divides q i then 1 else 0) := by
  classical
  calc
    _ = ∑ i ∈ indices, ∑ t ∈ marks.powerset, (-1 : R) ^ t.card *
        (a i * (if ∀ q ∈ t, ¬divides q i then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_marks_inclusion_exclusion marks (fun q => divides q i) (a i)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]

/-- The ordinary zeroth digit, written independently of any residue field. -/
def ordinaryZeroDigit (Q : R) (x : I) [Zero I] [DecidableEq I] : R :=
  if x = 0 then 1 - Q else -Q

/-- Uniform marking is delta at zero minus the ordinary zeroth digit.
Here `Q` is the reciprocal residue cardinality. -/
theorem uniformDigit_eq_delta_sub_ordinary (Q : R) (x : I)
    [Zero I] [DecidableEq I] :
    Q = (if x = 0 then (1 : R) else 0) - ordinaryZeroDigit Q x := by
  by_cases hx : x = 0 <;> simp [ordinaryZeroDigit, hx]

/-- Expanding a tensor of digit differences gives exactly one branch for
each active/inactive subset.  This identity is independent of the
choice of the vector on which the digit functional acts. -/
theorem digit_tensor_expansion [DecidableEq P]
    (s : Finset P) (delta ordinary : P → R) :
    (∏ q ∈ s, (delta q - ordinary q)) =
      ∑ t ∈ s.powerset, (-1 : R) ^ t.card *
        (∏ q ∈ s \ t, delta q) * ∏ q ∈ t, ordinary q :=
  Finset.prod_sub delta ordinary s

end FiniteAlgebra

section InfiniteMarks

variable {P I : Type*}

/-- A Boolean restriction of an absolutely summable complex family remains
summable.  This is the convergence justification for all puncture masks. -/
theorem summable_mul_boolean_mask (f : I → ℂ) (hf : Summable f)
    (p : I → Prop) [DecidablePred p] :
    Summable (fun i => f i * (if p i then (1 : ℂ) else 0)) := by
  classical
  convert hf.indicator {i | p i} using 1
  funext i
  by_cases hi : p i <;> simp [Set.indicator, hi]

/-- Inclusion-exclusion for an actual infinite arithmetic sum.  Only the
unmarked coefficient's summability is required, and all new restricted
series are automatically summable by `summable_mul_boolean_mask`. -/
theorem tsum_marked_eq_alternating_unmarked (marks : Finset P)
    (divides : P → I → Prop) [∀ q, DecidablePred (divides q)]
    (a : I → ℂ) (ha : Summable a) :
    (∑' i, a i * (if ∀ q ∈ marks, divides q i then (1 : ℂ) else 0)) =
      ∑ t ∈ marks.powerset, (-1 : ℂ) ^ t.card *
        ∑' i, a i * (if ∀ q ∈ t, ¬divides q i then 1 else 0) := by
  classical
  have hs (t : Finset P) : Summable (fun i => (-1 : ℂ) ^ t.card *
      (a i * (if ∀ q ∈ t, ¬divides q i then 1 else 0))) :=
    (summable_mul_boolean_mask a ha (fun i => ∀ q ∈ t, ¬divides q i)).mul_left _
  calc
    _ = ∑' i, ∑ t ∈ marks.powerset, (-1 : ℂ) ^ t.card *
        (a i * (if ∀ q ∈ t, ¬divides q i then 1 else 0)) := by
      apply tsum_congr
      intro i
      exact weighted_marks_inclusion_exclusion marks (fun q => divides q i) (a i)
    _ = ∑ t ∈ marks.powerset, ∑' i, (-1 : ℂ) ^ t.card *
        (a i * (if ∀ q ∈ t, ¬divides q i then 1 else 0)) :=
      Summable.tsum_finsetSum (fun t ht => hs t)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      exact tsum_mul_left

end InfiniteMarks

section WeylAveraging

variable {G I R : Type*} [Mul G] [CommSemiring R]

/-- A finite digit average inherits rational Weyl invariance term by term.
No Whittaker expansion or reflection conclusion is a hypothesis. -/
theorem weighted_weyl_average (s : Finset I) (theta : G → R) (w : G)
    (hw : ∀ g, theta (w * g) = theta g) (weight : I → R) (arg : I → G) :
    (∑ d ∈ s, weight d * theta (w * arg d)) =
      ∑ d ∈ s, weight d * theta (arg d) := by
  apply Finset.sum_congr rfl
  intro d hd
  rw [hw]

end WeylAveraging

section AngularCancellation

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Integration of a nontrivial angular eigenfunction is zero.  The
integrability hypothesis ensures this is not merely the zero default of
the Bochner integral. -/
theorem integral_eq_zero_of_rotation (e : X ≃ᵐ X)
    (hμ : MeasurePreserving e μ μ) (f : X → ℂ) (_hf : Integrable f μ)
    (ζ : ℂ) (hζ : ζ ≠ 1) (hrot : ∀ x, f (e x) = ζ * f x) :
    ∫ x, f x ∂μ = 0 := by
  have heq : (∫ x, f x ∂μ) = ζ * ∫ x, f x ∂μ := by
    calc
      (∫ x, f x ∂μ) = ∫ x, f (e x) ∂μ := (hμ.integral_comp' f).symm
      _ = ∫ x, ζ * f x ∂μ := by congr 1; funext x; exact hrot x
      _ = ζ * ∫ x, f x ∂μ := integral_const_mul ζ f
  have hz : (1 - ζ) * (∫ x, f x ∂μ) = 0 := by
    calc
      (1 - ζ) * (∫ x, f x ∂μ) = (∫ x, f x ∂μ) - ζ * ∫ x, f x ∂μ := by ring
      _ = 0 := sub_eq_zero.mpr heq
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hζ))

/-- The angular character kills a radial constant term, including any
fixed finite-place or relative-radial weight. -/
theorem angular_constant_term_vanishes (e : X ≃ᵐ X)
    (hμ : MeasurePreserving e μ μ) (weight constantTerm : X → ℂ)
    (hint : Integrable (fun x => weight x * constantTerm x) μ)
    (ζ : ℂ) (hζ : ζ ≠ 1)
    (hweight : ∀ x, weight (e x) = ζ * weight x)
    (hradial : ∀ x, constantTerm (e x) = constantTerm x) :
    ∫ x, weight x * constantTerm x ∂μ = 0 := by
  apply integral_eq_zero_of_rotation μ e hμ _ hint ζ hζ
  intro x
  rw [hweight, hradial, mul_assoc]

end AngularCancellation

end ThetaGlobal.GlobalMarks
