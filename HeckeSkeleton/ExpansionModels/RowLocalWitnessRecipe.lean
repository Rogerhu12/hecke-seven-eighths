import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# One finite-sum recipe for witnesses and moment models

This module is independent of the unfinished HeckeSkeleton.  It proves the
row-local parameter assembly needed when a detector chooses a different
continuous parameter at each row.  The polynomial coefficients and their
zero masks are data, and no detector or moment estimate is assumed.

The project adapter `ProjectSharedWitnessRecipe.lean` instantiates the same
construction with the project's actual `MomentData` finite sums.
-/

set_option autoImplicit false
noncomputable section

namespace ExpansionRecipe

open scoped BigOperators

variable {Row Column Parameter Slot : Type*}

/-- A genuine finite polynomial, before applying its normalizing scalar. -/
structure FinitePolynomial (Column : Type*) where
  support : Finset Column
  coefficient : Column → ℂ
  mask : Column → Bool
  normalizer : ℂ

def FinitePolynomial.value (p : FinitePolynomial Column) : ℂ :=
  p.normalizer * ∑ I ∈ p.support, if p.mask I then p.coefficient I else 0

/-- Independent witness parameters enter at one row.  Slot values do not
depend on the witness parameter map.  A parameter may itself be a tuple of
heights, real shifts, imaginary shifts, and cutoff parameters. -/
structure SharedRecipe (Row Column Parameter Slot : Type*) where
  inverse : Row → Parameter → FinitePolynomial Column
  plain : Row → Parameter → FinitePolynomial Column
  slot : Slot → Row → FinitePolynomial Column

/-- A single inverse family indexed by independent row and inverse scales.
There is no subdivision or selected-slot argument in this field, matching
the intended `SourceMomentModels.unmarked U D` interface. -/
structure ScaleRecipe (Row Column Parameter Slot : Type*) where
  inverse : ℝ → ℝ → Row → Parameter → FinitePolynomial Column
  plain : ℝ → ℝ → Row → Parameter → FinitePolynomial Column
  slot : ℝ → Slot → Row → FinitePolynomial Column

def ScaleRecipe.atScales (r : ScaleRecipe Row Column Parameter Slot)
    (U D N Z : ℝ) : SharedRecipe Row Column Parameter Slot where
  inverse := r.inverse U D
  plain := r.plain U N
  slot := r.slot Z

/-- The same parameters are used by both the physical witness and its model. -/
structure WitnessData (Row Slot : Type*) where
  inverse : Row → ℂ
  plain : Row → ℂ
  slot : Slot → Row → ℂ

def SharedRecipe.witness (r : SharedRecipe Row Column Parameter Slot)
    (p : Row → Parameter) : WitnessData Row Slot where
  inverse u := (r.inverse u (p u)).value
  plain u := (r.plain u (p u)).value
  slot j u := (r.slot j u).value

structure SelectedModel (Row Slot : Type*) where
  inverse : Row → ℂ
  plain₁ : Row → ℂ
  plain₂ : Row → ℂ
  slots : Row → ℂ

def SharedRecipe.model (r : SharedRecipe Row Column Parameter Slot)
    (p : Row → Parameter) (selected : Finset Slot) : SelectedModel Row Slot where
  inverse u := (r.inverse u (p u)).value
  plain₁ u := (r.plain u (p u)).value
  plain₂ u := (r.plain u (p u)).value
  slots u := ∏ j ∈ selected, (r.slot j u).value

/-- Unmarked models use the same inverse recipe, independent of slot choice. -/
def SharedRecipe.unmarked (r : SharedRecipe Row Column Parameter Slot)
    (p : Row → Parameter) (u : Row) : ℂ := (r.inverse u (p u)).value

def ScaleRecipe.unmarkedModel (r : ScaleRecipe Row Column Parameter Slot)
    (U D : ℝ) (p : Row → Parameter) (u : Row) : ℂ :=
  (r.inverse U D u (p u)).value

/-- The marked and independent unmarked calls share an inverse polynomial
even when the plain scale, physical scale, and selected slots change. -/
theorem ScaleRecipe.unmarked_coherence (r : ScaleRecipe Row Column Parameter Slot)
    (U D N Z : ℝ) (p : Row → Parameter) (selected : Finset Slot) (u : Row) :
    ((r.atScales U D N Z).model p selected).inverse u =
      r.unmarkedModel U D p u := rfl

theorem ScaleRecipe.inverse_independent_of_plain_and_slots
    (r : ScaleRecipe Row Column Parameter Slot) (U D N N' Z Z' : ℝ)
    (p : Row → Parameter) (selected selected' : Finset Slot) (u : Row) :
    ((r.atScales U D N Z).model p selected).inverse u =
      ((r.atScales U D N' Z').model p selected').inverse u := rfl

structure PolynomialCalibration (w : WitnessData Row Slot)
    (m : SelectedModel Row Slot) (selected : Finset Slot)
    (unmarked : Row → ℂ) : Prop where
  inverse : ∀ u, w.inverse u = m.inverse u
  plain₁ : ∀ u, w.plain u = m.plain₁ u
  plain₂ : ∀ u, w.plain u = m.plain₂ u
  slots : ∀ u, (∏ j ∈ selected, w.slot j u) = m.slots u
  unmarked : ∀ u, w.inverse u = unmarked u

/-- Every calibration is proved by reducing the common recipe.  No equality
between independently chosen witness values and models is a hypothesis. -/
theorem SharedRecipe.calibration (r : SharedRecipe Row Column Parameter Slot)
    (p : Row → Parameter) (selected : Finset Slot) :
    PolynomialCalibration (r.witness p) (r.model p selected) selected (r.unmarked p) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Locality for all witness and model values follows from the constructor,
even when different rows choose different parameter values. -/
theorem SharedRecipe.row_local (r : SharedRecipe Row Column Parameter Slot)
    (p q : Row → Parameter) (selected : Finset Slot) (u : Row)
    (h : p u = q u) :
    (r.witness p).inverse u = (r.witness q).inverse u ∧
    (r.witness p).plain u = (r.witness q).plain u ∧
    (r.model p selected).inverse u = (r.model q selected).inverse u ∧
    (r.model p selected).plain₁ u = (r.model q selected).plain₁ u ∧
    (r.model p selected).plain₂ u = (r.model q selected).plain₂ u := by
  simp only [SharedRecipe.witness, SharedRecipe.model, h, and_self]

/-- Row-local predicates can be witnessed simultaneously on a finite row
set, with a prescribed default off that set.  This adds no subdivision. -/
theorem assemble_row_parameters (rows : Finset Row) (default : Parameter)
    (P : Row → Parameter → Prop)
    (h : ∀ u ∈ rows, ∃ p, P u p) :
    ∃ p : Row → Parameter,
      (∀ u ∈ rows, P u (p u)) ∧ (∀ u ∉ rows, p u = default) := by
  classical
  let p : Row → Parameter := fun u =>
    if hu : u ∈ rows then Classical.choose (h u hu) else default
  refine ⟨p, ?_, ?_⟩
  · intro u hu
    dsimp [p]
    rw [dite_eq_left hu]
    exact Classical.choose_spec (h u hu)
  · intro u hu
    simp [p, hu]

/-- Bounds and two simultaneous witness requirements are assembled together.
The row parameter is chosen once; inverse and plain do not get unrelated
maps.  The source supplies a local detector statement at each row. -/
theorem assemble_bounded_witness_parameters
    (r : SharedRecipe Row Column Parameter Slot) (rows : Finset Row)
    (default : Parameter) (admissible : Parameter → Prop)
    (hdefault : admissible default) (inverseTarget plainTarget : Row → ℝ)
    (h : ∀ u ∈ rows, ∃ p, admissible p ∧
      inverseTarget u ≤ ‖(r.inverse u p).value‖ ^ 2 ∧
      plainTarget u ≤ ‖(r.plain u p).value‖ ^ 2) :
    ∃ p : Row → Parameter,
      (∀ u, admissible (p u)) ∧
      (∀ u ∈ rows, inverseTarget u ≤ ‖(r.witness p).inverse u‖ ^ 2) ∧
      (∀ u ∈ rows, plainTarget u ≤ ‖(r.witness p).plain u‖ ^ 2) := by
  classical
  obtain ⟨p, hp, hout⟩ := assemble_row_parameters rows default
    (fun u p => admissible p ∧
      inverseTarget u ≤ ‖(r.inverse u p).value‖ ^ 2 ∧
      plainTarget u ≤ ‖(r.plain u p).value‖ ^ 2) h
  refine ⟨p, ?_, ?_, ?_⟩
  · intro u
    by_cases hu : u ∈ rows
    · exact (hp u hu).1
    · rw [hout u hu]
      exact hdefault
  · intro u hu
    exact (hp u hu).2.1
  · intro u hu
    exact (hp u hu).2.2

/-- The paired source really has a fourth power when both plain tests come
from the same witness recipe. -/
theorem SharedRecipe.paired_integrand
    (r : SharedRecipe Row Column Parameter Slot) (p : Row → Parameter)
    (selected : Finset Slot) (u : Row) :
    ‖(r.model p selected).plain₁ u * (r.model p selected).plain₂ u *
        (r.model p selected).slots u‖ ^ 2 =
      ‖(r.witness p).plain u‖ ^ 4 *
        ‖∏ j ∈ selected, (r.witness p).slot j u‖ ^ 2 := by
  simp only [SharedRecipe.model, SharedRecipe.witness, norm_mul]
  ring

theorem SharedRecipe.inverse_integrand
    (r : SharedRecipe Row Column Parameter Slot) (p : Row → Parameter)
    (selected : Finset Slot) (u : Row) :
    ‖(r.model p selected).inverse u * (r.model p selected).slots u‖ ^ 2 =
      ‖(r.witness p).inverse u *
        ∏ j ∈ selected, (r.witness p).slot j u‖ ^ 2 := rfl

theorem SharedRecipe.unmarked_eq_empty_model
    (r : SharedRecipe Row Column Parameter Slot) (p : Row → Parameter)
    (u : Row) :
    r.unmarked p u = (r.model p ∅).inverse u ∧
      (r.model p ∅).slots u = 1 := by
  simp [SharedRecipe.model, SharedRecipe.unmarked]

/-- Changing a coefficient at a row/column killed by the common mask cannot
change the polynomial.  The mask stays inside the finite sum. -/
theorem FinitePolynomial.value_eq_of_eq_on_live_support
    (p q : FinitePolynomial Column)
    (hsupport : p.support = q.support) (hmask : p.mask = q.mask)
    (hnorm : p.normalizer = q.normalizer)
    (hcoeff : ∀ I ∈ p.support, p.mask I = true → p.coefficient I = q.coefficient I) :
    p.value = q.value := by
  classical
  unfold FinitePolynomial.value
  rw [← hsupport, ← hmask, ← hnorm]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hm : p.mask I = true
  · simp [hm, hcoeff I hI hm]
  · simp [hm]

end ExpansionRecipe

#print axioms ExpansionRecipe.SharedRecipe.calibration
#print axioms ExpansionRecipe.ScaleRecipe.unmarked_coherence
#print axioms ExpansionRecipe.SharedRecipe.row_local
#print axioms ExpansionRecipe.assemble_row_parameters
#print axioms ExpansionRecipe.assemble_bounded_witness_parameters
#print axioms ExpansionRecipe.SharedRecipe.paired_integrand
#print axioms ExpansionRecipe.FinitePolynomial.value_eq_of_eq_on_live_support
