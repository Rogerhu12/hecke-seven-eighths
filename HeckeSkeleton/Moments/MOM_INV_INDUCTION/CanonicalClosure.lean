import HeckeSkeleton.Moments.MOM_INV_INDUCTION.EnergyClosure
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.Terminal

/-!
# The canonical recursion with its actual depth-dependent margins

This specialization derives every child's numerical admissibility from
`StepGeometry`.  The source supplies only preservation of its arithmetic
coefficient class.  The terminal predicate is supplied by the actual block decomposition;
a short label alone is not assumed to make a whole node terminal.
Terminal and two-transform estimates have disjoint hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open HeckePort.Moments

/-- All data at a reachable node, including the upper bound on depth. -/
def ReachableData {α : Type*} (Admissible : α → Prop)
    (M F Q cap : α → ℝ) (D : ℕ) (c eta : ℝ) (h : ℕ) (x : α) : Prop :=
  h ≤ D ∧ Admissible x ∧ CanonicalAdmissible M F Q cap c eta h x

/-- Close the complete canonical recursion from its one-step input and
genuine short-block terminal input.  The strict margin, row descent, finite
termination and total loss are proved here. -/
theorem canonical_energy_from_ledger {α : Type*}
    (E F M Q cap : α → ℝ) (s : α → StepData α)
    (Terminal Admissible : α → Prop)
    {Mmax c eps : ℝ} (b : DescentBudget Mmax c eps) (hc : 0 < c)
    (Z C H A : ℝ) (hZ : 1 ≤ Z) (hC : 1 ≤ C) (hH : 1 ≤ H) (hA : 0 ≤ A)
    (hdata : ∀ x, Admissible x → 0 ≤ M x ∧ 0 ≤ Q x ∧ 0 ≤ cap x)
    (hgeometry : ∀ h x, h < b.depth → Admissible x →
      CanonicalAdmissible M F Q cap c b.eta h x → ¬ Terminal x →
      StepGeometry F M Q cap b.eta b.step x (s x))
    (harithmetic : ∀ h x y, h < b.depth → Admissible x →
      CanonicalAdmissible M F Q cap c b.eta h x → ¬ Terminal x →
      y ∈ (s x).children → Admissible y)
    (hterminal : ∀ h x, h < b.depth → Admissible x →
      CanonicalAdmissible M F Q cap c b.eta h x → Terminal x →
      E x ≤ C * H ^ A * Z ^ F x)
    (hstep : ∀ h x, h < b.depth → Admissible x →
      CanonicalAdmissible M F Q cap c b.eta h x → ¬ Terminal x →
      StepEnergy E F M Z b.eta b.tau b.pi (C * H ^ A) x (s x)) :
    ∀ x, Admissible x → CanonicalMargins (F x) (M x) (Q x) (cap x) c →
      M x ≤ Mmax →
      E x ≤ (3 * C) ^ b.depth * Z ^ (F x + eps / 2) * H ^ (A * (b.depth : ℝ)) := by
  let Good := ReachableData Admissible M F Q cap b.depth c b.eta
  have hnonneg : ∀ h x, Good h x → 0 ≤ M x := fun _ _ hx => hx.2.2.1
  have hMF : ∀ h x, Good h x → M x ≤ F x := by
    intro h x hx
    exact canonicalAdmissible_row_le_total b hc hx.1 hx.2.2
      (hdata x hx.2.1).2.1 (hdata x hx.2.1).2.2
  have hgeom : ∀ h x, h < b.depth → Good h x → ¬ Terminal x →
      StepGeometry F M Q cap b.eta b.step x (s x) := by
    intro h x hh hx ht
    exact hgeometry h x hh hx.2.1 hx.2.2 ht
  have hgood : ∀ h x y, h < b.depth → Good h x → ¬ Terminal x →
      y ∈ (s x).children → Good (h + 1) y := by
    intro h x y hh hx ht hy
    have ha := harithmetic h x y hh hx.2.1 hx.2.2 ht hy
    have hg := hgeom h x hh hx ht
    refine ⟨Nat.succ_le_of_lt hh, ha, ?_⟩
    apply canonicalAdmissible_child b.eta_pos.le (hdata y ha).1
    · exact (sub_le_sub_right hx.2.2.2.1 (5 * b.eta)).trans (hg.first_margin y hy)
    · exact (sub_le_sub_right hx.2.2.2.2 (7 * b.eta)).trans (hg.second_margin y hy)
  have hterm : ∀ h x, h < b.depth → Good h x → Terminal x →
      E x ≤ C * H ^ A * Z ^ F x := by
    intro h x hh hx ht
    exact hterminal h x hh hx.2.1 hx.2.2 ht
  have hstep' : ∀ h x, h < b.depth → Good h x → ¬ Terminal x →
      StepEnergy E F M Z b.eta b.tau b.pi (C * H ^ A) x (s x) := by
    intro h x hh hx ht
    exact hstep h x hh hx.2.1 hx.2.2 ht
  have hb := canonical_energy_polynomial_height E F M Q cap s
    Terminal Good b.depth Z b.eta b.tau b.pi C H A b.step Mmax (eps / 2)
    hZ b.eta_pos.le b.tau_pos.le b.pi_pos.le hC hH hA b.depth_bound b.loss_budget.le
    hnonneg hMF hgeom hgood hterm hstep'
  intro x hx hm hM
  apply hb x ?_ hM
  exact ⟨Nat.zero_le _, hx, (hdata x hx).1, by simpa [CanonicalMargins] using hm⟩

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
