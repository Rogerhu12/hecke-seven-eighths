import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# Canonical local frozen exponents

This arithmetic module is the part of the previous valuation proof used by
actual ideals.  The minimum-zero condition is retained exactly.  Its proof
requires no complex, analytic or energy import.
-/

namespace HeckeSkeleton.LowFrozenCube

/-! ## Canonical local frozen exponent -/

/-- The nonzero local table allows precisely residues zero and one modulo three. -/
def AdmissibleExponent (e : ℕ) : Prop := e % 3 = 0 ∨ e % 3 = 1

/-- Zero is frozen at zero; positive residues one and zero are frozen at one and three. -/
def frozenMin (e : ℕ) : ℕ :=
  if e = 0 then 0 else if e % 3 = 1 then 1 else 3

/-- The exponent of the cube remaining after the minimum exponent is frozen. -/
def frozenCubeExp (e : ℕ) : ℕ := (e - frozenMin e) / 3

@[simp] theorem frozenMin_zero : frozenMin 0 = 0 := by
  simp [frozenMin]

@[simp] theorem frozenCubeExp_zero : frozenCubeExp 0 = 0 := by
  simp [frozenCubeExp]

theorem frozenMin_cases (e : ℕ) :
    frozenMin e = 0 ∨ frozenMin e = 1 ∨ frozenMin e = 3 := by
  unfold frozenMin
  split_ifs <;> simp

@[simp] theorem frozenMin_eq_zero_iff (e : ℕ) :
    frozenMin e = 0 ↔ e = 0 := by
  unfold frozenMin
  split_ifs <;> simp_all

theorem frozenMin_le (e : ℕ) (he : AdmissibleExponent e) :
    frozenMin e ≤ e := by
  unfold AdmissibleExponent at he
  unfold frozenMin
  split_ifs <;> omega

/-- Exact local decomposition.  The residue restriction is essential. -/
theorem frozenExponent_decomposition (e : ℕ) (he : AdmissibleExponent e) :
    e = frozenMin e + 3 * frozenCubeExp e := by
  unfold AdmissibleExponent at he
  simp only [frozenCubeExp, frozenMin]
  split_ifs <;> omega

/-- A zero base cannot hide a nontrivial cube in the canonical decomposition. -/
theorem frozenCubeExp_eq_zero_of_base_zero {e : ℕ} (he : frozenMin e = 0) :
    frozenCubeExp e = 0 := by
  have h := (frozenMin_eq_zero_iff e).mp he
  simpa [h]

/-- The allowed canonical pairs are `(1,x)`, `(3,x)`, and `(0,0)`. -/
def CanonicalFrozenPair (m x : ℕ) : Prop :=
  m = 1 ∨ m = 3 ∨ (m = 0 ∧ x = 0)

theorem frozenPair_canonical (e : ℕ) :
    CanonicalFrozenPair (frozenMin e) (frozenCubeExp e) := by
  rcases frozenMin_cases e with h | h | h
  · exact Or.inr (Or.inr ⟨h, frozenCubeExp_eq_zero_of_base_zero h⟩)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- Uniqueness also records the special treatment of zero. -/
theorem frozenExponent_unique {e m x : ℕ}
    (hc : CanonicalFrozenPair m x) (he : e = m + 3 * x) :
    m = frozenMin e ∧ x = frozenCubeExp e := by
  unfold CanonicalFrozenPair at hc
  simp only [frozenCubeExp, frozenMin]
  split_ifs <;> omega

theorem canonicalPair_admissible {e m x : ℕ}
    (hc : CanonicalFrozenPair m x) (he : e = m + 3 * x) :
    AdmissibleExponent e := by
  unfold CanonicalFrozenPair at hc
  unfold AdmissibleExponent
  omega

#print axioms frozenExponent_decomposition
#print axioms frozenExponent_unique
#print axioms canonicalPair_admissible

end HeckeSkeleton.LowFrozenCube
