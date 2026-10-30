import Init

/-!
The algebraic induction in the complex-place Weyl calculation.

This file deliberately proves only the operator-algebra step.  Instantiating
`W`, `E`, `F`, and `Ebar` with the local representation, and proving the four
displayed hypotheses there, is a separate analytic representation-theory task.
-/

namespace HeckeSkeleton.ThetaLocal

universe u

/-- Repeated application of one root operator. -/
def rootIterate {V : Type u} (E : V → V) : Nat → V → V
  | 0, v => v
  | n + 1, v => E (rootIterate E n v)

/-- An intertwiner carries an iterated operator to the corresponding iterate. -/
theorem intertwining_rootIterate {V : Type u} (W E F : V → V)
    (h : ∀ v, W (E v) = F (W v)) (n : Nat) (v : V) :
    W (rootIterate E n v) = rootIterate F n (W v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change W (E (rootIterate E n v)) = F (rootIterate F n (W v))
    rw [h, ih]

/-- A commuting operator commutes with every iterate. -/
theorem commuting_rootIterate {V : Type u} (F Ebar : V → V)
    (h : ∀ v, F (Ebar v) = Ebar (F v)) (n : Nat) (v : V) :
    F (rootIterate Ebar n v) = rootIterate Ebar n (F v) :=
  intertwining_rootIterate F Ebar Ebar h n v

/-- Equality of the two root actions on the spherical vector propagates. -/
theorem opposite_rootIterate {V : Type u} (F Ebar : V → V) (v₀ : V)
    (hcomm : ∀ v, F (Ebar v) = Ebar (F v))
    (hcompact : F v₀ = Ebar v₀) (n : Nat) :
    rootIterate F n v₀ = rootIterate Ebar n v₀ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rootIterate F (n + 1) v₀ = F (rootIterate F n v₀) := rfl
      _ = F (rootIterate Ebar n v₀) := congrArg F ih
      _ = rootIterate Ebar n (F v₀) :=
        commuting_rootIterate F Ebar hcomm n v₀
      _ = rootIterate Ebar n (Ebar v₀) :=
        congrArg (rootIterate Ebar n) hcompact
      _ = Ebar (rootIterate Ebar n v₀) :=
        (commuting_rootIterate Ebar Ebar (fun _ => rfl) n v₀).symm
      _ = rootIterate Ebar (n + 1) v₀ := rfl

/-- The precise algebraic implication used for `π(w) φ_m = φ_{-m}`. -/
theorem weyl_rootIterate {V : Type u} (W E F Ebar : V → V) (v₀ : V)
    (hweyl : ∀ v, W (E v) = F (W v))
    (hspherical : W v₀ = v₀)
    (hcomm : ∀ v, F (Ebar v) = Ebar (F v))
    (hcompact : F v₀ = Ebar v₀) (n : Nat) :
    W (rootIterate E n v₀) = rootIterate Ebar n v₀ := by
  calc
    W (rootIterate E n v₀) = rootIterate F n (W v₀) :=
      intertwining_rootIterate W E F hweyl n v₀
    _ = rootIterate F n v₀ := congrArg (rootIterate F n) hspherical
    _ = rootIterate Ebar n v₀ :=
      opposite_rootIterate F Ebar v₀ hcomm hcompact n

#print axioms intertwining_rootIterate
#print axioms commuting_rootIterate
#print axioms opposite_rootIterate
#print axioms weyl_rootIterate

end HeckeSkeleton.ThetaLocal
