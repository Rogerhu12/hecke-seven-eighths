import HeckePort.Moments.Descent.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The numerical and energy interface of one canonical inverse step

This is an explicit full-parent reduction obligation for the consumer.
It is stronger than the published fixed reconstructed-block theorem
`MOMInvStep.fixed_triple_energy_step` in `cloud/mom-inv-step`, file
`HeckeSkeleton/Moments/MOM_INV_STEP/Interface.lean` (reviewed interface blob
`ef81d921d241be38b2d3ab8d3c1c156eaaa5644b`).  That theorem consumes two raw
child-energy bounds and does not construct every parent's reconstruction
packet or its outer aggregation.  Instantiating `StepEnergy` therefore
still requires those source identities for the literal canonical energies,
with the original masks, squarefree labels and frozen triples.  No final
canonical moment bound is a field of this interface.

The three prefactors are kept separate.  `normalization` is the identity
`κ + λ + count + 2 F_c = F` before clipping.  The normalized weight on the
distinct frozen triples has mass at most one; the small-power cost of that
measure is `pi` and is used once.  The child label weight is already part
of the child energy and must not be included again in this measure.

The parent reduction retains both principal terms.  The cost `28 * eta`
is `9/2 + 18 + 11/2`; the two occurrences of the clipping correction add
at most `12 * eta`, yielding the paper's `40 * eta` step loss.

The interface is deliberately independent of `HeckeSkeleton.Moments`:
the latter's source types currently contain admitted definitions.  The
consumer theorems in this directory therefore have an auditable type as
well as an auditable proof.  See `STATEMENT_AUDIT.md` for the original
source endpoint and the additional source/terminal transport obligations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open scoped BigOperators

/-- A finite positive measure on the distinct frozen triples after their
norm count has been extracted.  Its values are independent of the child
row and label variables. -/
structure StepData (α : Type*) where
  children : Finset α
  weight : α → ℝ
  weight_nonneg : ∀ y ∈ children, 0 ≤ weight y
  weight_mass : ∑ y ∈ children, weight y ≤ 1
  firstPrefactor : α → ℝ
  secondPrefactor : α → ℝ
  tripleCount : α → ℝ
  clipping : α → ℝ

/-- The geometric information supplied by a single two-transform
reduction, before any induction hypothesis is used. -/
structure StepGeometry {α : Type*} (F M Q z : α → ℝ)
    (eta d : ℝ) (x : α) (s : StepData α) : Prop where
  normalization : ∀ y ∈ s.children,
    s.firstPrefactor y + s.secondPrefactor y + s.tripleCount y +
      2 * (F y - s.clipping y) = F x
  clipping_nonneg : ∀ y ∈ s.children, 0 ≤ s.clipping y
  clipping_le : ∀ y ∈ s.children, s.clipping y ≤ 6 * eta
  row_decrease : ∀ y ∈ s.children, M y + d ≤ M x
  first_margin : ∀ y ∈ s.children,
    F x - M x - Q x - z x - 5 * eta ≤ F y - M y - Q y - z y
  second_margin : ∀ y ∈ s.children,
    4 * F x - 3 * M x - 6 * z x - 7 * eta ≤ 4 * F y - 3 * M y - 6 * z y
  total_length : ∀ y ∈ s.children, F y ≤ F x + 11 * eta

/-- The actual single-step energy inequality.  `S` is a uniform
finite-seminorm/height factor chosen before the current node; this
interface does not assert that the source's slice-profile predicate
supplies it.  Both principal contributions and the weighted child
energies remain explicit. -/
def StepEnergy {α : Type*} (E F M : α → ℝ)
    (Z eta tau pi S : ℝ) (x : α) (s : StepData α) : Prop :=
  E x ≤ S * (Z ^ M x + Z ^ (F x + 26 * eta + tau + pi) +
    Z ^ (28 * eta + tau + pi) *
      ∑ y ∈ s.children, s.weight y *
        (Z ^ (s.firstPrefactor y + s.secondPrefactor y + s.tripleCount y + F y) * E y))

/-- The loss charged once at a nonterminal step. -/
def stepLoss (eta tau pi : ℝ) : ℝ := 40 * eta + tau + pi

theorem stepLoss_nonneg {eta tau pi : ℝ}
    (heta : 0 ≤ eta) (htau : 0 ≤ tau) (hpi : 0 ≤ pi) :
    0 ≤ stepLoss eta tau pi := by
  unfold stepLoss
  positivity

/-- The exact prefactors, including the restored child normalization,
charge the clipping error twice and the child loss only once. -/
theorem normalized_prefactor_le {α : Type*} {F M Q z : α → ℝ}
    {eta d : ℝ} {x : α} {s : StepData α}
    (g : StepGeometry F M Q z eta d x s) (y : α) (hy : y ∈ s.children)
    (tau pi e : ℝ) :
    28 * eta + tau + pi +
      (s.firstPrefactor y + s.secondPrefactor y + s.tripleCount y + F y) +
      (F y + e) ≤ F x + stepLoss eta tau pi + e := by
  have hn := g.normalization y hy
  have hc := g.clipping_le y hy
  unfold stepLoss
  linarith

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
