import HeckeSkeleton.Moments.MOM_INV_INDUCTION.InductionGeometry

/-!
# Finite backward induction for canonical inverse energies

The conclusion predicate is arbitrary: it can carry the actual normalized
energy estimate together with its height order and finite seminorm order.
The only recursive premise is the estimate for genuine children.  A positive
drop in nonnegative row length closes this premise after a uniformly bounded
number of steps, rather than assuming a canonical moment input.
-/

set_option autoImplicit false

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open HeckePort.Moments

universe u

/-- Backward induction with a fixed row budget, starting at an arbitrary
reachable depth.  `Good` carries the arithmetic data and strict margins;
`P` carries the desired estimate at the allocated remaining loss. -/
theorem finite_descent_from {α : Type u}
    (row : α → ℝ) (Child : α → α → Prop)
    (Good P : ℕ → α → Prop) (D : ℕ) (d Mmax : ℝ)
    (hdepth : Mmax < (D : ℝ) * d)
    (hnonneg : ∀ h x, Good h x → 0 ≤ row x)
    (hchild : ∀ h x y, h < D → Good h x → Child x y →
      Good (h + 1) y ∧ row y + d ≤ row x)
    (hstep : ∀ h x, h < D → Good h x →
      (∀ y, Child x y → P (h + 1) y) → P h x) :
    ∀ h, h ≤ D → ∀ x, Good h x → row x + (h : ℝ) * d ≤ Mmax → P h x := by
  have aux : ∀ n : ℕ, ∀ h : ℕ, h + n = D →
      ∀ x, Good h x → row x + (h : ℝ) * d ≤ Mmax → P h x := by
    intro n
    induction n with
    | zero =>
        intro h hh x hx hrow
        have heq : h = D := by omega
        subst h
        have hx0 := hnonneg D x hx
        exact (by linarith : False).elim
    | succ n ih =>
        intro h hh x hx hrow
        have hhD : h < D := by omega
        apply hstep h x hhD hx
        intro y hy
        obtain ⟨hyGood, hyrow⟩ := hchild h x y hhD hx hy
        apply ih (h + 1) (by omega) y hyGood
        push_cast
        linarith
  intro h hh x hx hrow
  exact aux (D - h) h (by omega) x hx hrow

/-- Root form of `finite_descent_from`.  No separate hypothesis that the
recursive tree is finite is needed. -/
theorem finite_descent {α : Type u}
    (row : α → ℝ) (Child : α → α → Prop)
    (Good P : ℕ → α → Prop) (D : ℕ) (d Mmax : ℝ)
    (hdepth : Mmax < (D : ℝ) * d)
    (hnonneg : ∀ h x, Good h x → 0 ≤ row x)
    (hchild : ∀ h x y, h < D → Good h x → Child x y →
      Good (h + 1) y ∧ row y + d ≤ row x)
    (hstep : ∀ h x, h < D → Good h x →
      (∀ y, Child x y → P (h + 1) y) → P h x) :
    ∀ x, Good 0 x → row x ≤ Mmax → P 0 x := by
  intro x hx hrow
  exact finite_descent_from row Child Good P D d Mmax hdepth hnonneg hchild hstep
    0 (Nat.zero_le _) x hx (by simpa using hrow)

/-- Terminal blocks consume the reflected estimate; every other block
consumes only estimates for its children. -/
theorem finite_descent_with_terminal {α : Type u}
    (row : α → ℝ) (Child : α → α → Prop) (Terminal : α → Prop)
    (Good P : ℕ → α → Prop) (D : ℕ) (d Mmax : ℝ)
    (hdepth : Mmax < (D : ℝ) * d)
    (hnonneg : ∀ h x, Good h x → 0 ≤ row x)
    (hchild : ∀ h x y, h < D → Good h x → ¬ Terminal x → Child x y →
      Good (h + 1) y ∧ row y + d ≤ row x)
    (hterminal : ∀ h x, h < D → Good h x → Terminal x → P h x)
    (hstep : ∀ h x, h < D → Good h x → ¬ Terminal x →
      (∀ y, Child x y → P (h + 1) y) → P h x) :
    ∀ x, Good 0 x → row x ≤ Mmax → P 0 x := by
  classical
  apply finite_descent row (fun x y => ¬ Terminal x ∧ Child x y)
    Good P D d Mmax hdepth hnonneg
  · intro h x y hh hx hxy
    exact hchild h x y hh hx hxy.1 hxy.2
  · intro h x hh hx ih
    by_cases ht : Terminal x
    · exact hterminal h x hh hx ht
    · exact hstep h x hh hx ht (fun y hy => ih y ⟨ht, hy⟩)

/-- Numerical admissibility at depth `h`.  The mark cap remains a field of
the genuine state, allowing a child to retain any subcollection of slots. -/
def CanonicalAdmissible {α : Type u}
    (M F Q z : α → ℝ) (c η : ℝ) (h : ℕ) (x : α) : Prop :=
  0 ≤ M x ∧ CanonicalMargins (F x) (M x) (Q x) (z x) (c - 7 * (h : ℝ) * η)

/-- The first invariant absorbs the direct principal term `Z ^ M` into
the canonical scale `Z ^ F`, uniformly at all permitted depths. -/
theorem canonicalAdmissible_row_le_total {α : Type u}
    {M F Q z : α → ℝ} {Mmax c ε : ℝ} (b : DescentBudget Mmax c ε)
    (hc : 0 ≤ c) {h : ℕ} (hh : h ≤ b.depth) {x : α}
    (hx : CanonicalAdmissible M F Q z c b.eta h x)
    (hQ : 0 ≤ Q x) (hz : 0 ≤ z x) : M x ≤ F x := by
  have hmargin := budget_margin b hh
  have hfirst := hx.2.1
  linarith

/-- The puncture length stays in the same bounded range as the total
column-and-label length. -/
theorem canonicalAdmissible_puncture_le_total {α : Type u}
    {M F Q z : α → ℝ} {Mmax c ε : ℝ} (b : DescentBudget Mmax c ε)
    (hc : 0 ≤ c) {h : ℕ} (hh : h ≤ b.depth) {x : α}
    (hx : CanonicalAdmissible M F Q z c b.eta h x)
    (hz : 0 ≤ z x) : Q x ≤ F x := by
  have hmargin := budget_margin b hh
  have hfirst := hx.2.1
  have hM := hx.1
  linarith

/-- The paper's two sharp child margins imply the common depth invariant. -/
theorem canonicalAdmissible_child {α : Type u}
    {M F Q z : α → ℝ} {c η : ℝ} {h : ℕ} {y : α}
    (hη : 0 ≤ η) (hM : 0 ≤ M y)
    (hfirst : c - 7 * (h : ℝ) * η - 5 * η ≤ F y - M y - Q y - z y)
    (hsecond : c - 7 * (h : ℝ) * η - 7 * η ≤ 4 * F y - 3 * M y - 6 * z y) :
    CanonicalAdmissible M F Q z c η (h + 1) y := by
  refine ⟨hM, ?_, ?_⟩ <;> push_cast <;> linarith

/-- Finite closure with the exact margin losses of Proposition 4.10.
The single-step premise must produce the child ledger as well as the
conditional parent estimate. -/
theorem canonical_finite_descent {α : Type u}
    (M F Q z : α → ℝ) (Child : α → α → Prop)
    (P : ℕ → α → Prop) {Mmax c ε : ℝ} (b : DescentBudget Mmax c ε)
    (hchild : ∀ h x y, h < b.depth →
      CanonicalAdmissible M F Q z c b.eta h x → Child x y →
      0 ≤ M y ∧ M y + b.step ≤ M x ∧
      c - 7 * (h : ℝ) * b.eta - 5 * b.eta ≤ F y - M y - Q y - z y ∧
      c - 7 * (h : ℝ) * b.eta - 7 * b.eta ≤ 4 * F y - 3 * M y - 6 * z y)
    (hstep : ∀ h x, h < b.depth →
      CanonicalAdmissible M F Q z c b.eta h x →
      (∀ y, Child x y → P (h + 1) y) → P h x) :
    ∀ x, 0 ≤ M x → CanonicalMargins (F x) (M x) (Q x) (z x) c →
      M x ≤ Mmax → P 0 x := by
  intro x hx hm hbound
  apply finite_descent M Child (CanonicalAdmissible M F Q z c b.eta) P
    b.depth b.step Mmax b.depth_bound (fun _ _ h => h.1) ?_ hstep x
    ⟨hx, by simpa using hm⟩ hbound
  intro h x y hh hx hxy
  obtain ⟨hyM, hydrop, hyfirst, hysecond⟩ := hchild h x y hh hx hxy
  exact ⟨canonicalAdmissible_child b.eta_pos.le hyM hyfirst hysecond, hydrop⟩

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
