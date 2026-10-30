import HeckeSkeleton.LowFrozenCube.Phases

/-!
# Assembly of the frozen cube into the hybrid row

The splitting function, the finite supports, and both coefficient functions are
fixed before any row is introduced.  This makes the required row independence
part of the types of the data.  The source sum and the target sum are equal,
with all collision masks retained and with no Cauchy--Schwarz loss.

The `split` hypothesis is discharged, for actual ideals, by uniqueness of the
supported/prime-to-supported factorization.  Its valuation version is proved
in `Valuations.fullCube_unique`.
-/

namespace HeckeSkeleton.LowFrozenCube

open scoped BigOperators Classical

noncomputable section

variable {A : Type*} [CommMonoid A]

def cubeProduct (q : A × A) : A := q.1 * q.2

/-- A single fixed coefficient depending only on the squarefree column and
the full cube.  There are no row or active-mark arguments. -/
def fullCubeCoefficient (split : A → A × A)
    (B : A → A → A → ℂ) (c b : A) : ℂ :=
  B c (split b).1 (split b).2

theorem cubeProduct_injective_on (t : Finset (A × A)) (split : A → A × A)
    (hsplit : ∀ q ∈ t, split (cubeProduct q) = q) :
    Set.InjOn cubeProduct (t : Set (A × A)) := by
  intro q hq r hr h
  calc
    q = split (cubeProduct q) := (hsplit q hq).symm
    _ = split (cubeProduct r) := congrArg split h
    _ = r := hsplit r hr

/-- Transport preserves the coefficient sup norm on its exact inherited support. -/
theorem fullCubeCoefficient_norm_le (t : Finset (A × A))
    (split : A → A × A) (hsplit : ∀ q ∈ t, split (cubeProduct q) = q)
    (B : A → A → A → ℂ) (c : A) (R : ℝ)
    (hB : ∀ q ∈ t, ‖B c q.1 q.2‖ ≤ R)
    (b : A) (hb : b ∈ t.image cubeProduct) :
    ‖fullCubeCoefficient split B c b‖ ≤ R := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  simpa [fullCubeCoefficient, hsplit q hq] using hB q hq

/-- The full-cube reindexing has no coefficient multiplicity loss. -/
theorem fullCubeCoefficient_energy (t : Finset (A × A))
    (split : A → A × A) (hsplit : ∀ q ∈ t, split (cubeProduct q) = q)
    (B : A → A → A → ℂ) (c : A) :
    (∑ b ∈ t.image cubeProduct, ‖fullCubeCoefficient split B c b‖ ^ 2) =
      ∑ q ∈ t, ‖B c q.1 q.2‖ ^ 2 := by
  rw [Finset.sum_image (cubeProduct_injective_on t split hsplit)]
  apply Finset.sum_congr rfl
  intro q hq
  simp [fullCubeCoefficient, hsplit q hq]

variable (χ : A → A →* ℂ) (Cop : A → A → Prop)

/-- Source inner sum after the minimum valuations have been frozen. -/
def frozenCubeInner (B : A → A → A → ℂ) (t : Finset (A × A))
    (d P c : A) : ℂ :=
  ∑ q ∈ t, B c q.1 q.2 *
    (((χ d q.1) ^ 3 * (χ d (c * q.2)) ^ 3) * (χ P c) ^ 4 *
      (if Cop P q.2 then (1 : ℂ) else 0))

/-- The corresponding inner sum in the hybrid estimate. -/
def fullCubeInner (β : A → A → ℂ) (bs : Finset A) (d P c : A) : ℂ :=
  ∑ b ∈ bs, β c b *
    ((χ d (c * b)) ^ 3 * (χ P c) ^ 4 *
      (if Cop P b then (1 : ℂ) else 0))

theorem frozenCubeInner_eq_fullCubeInner
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (t : Finset (A × A)) (split : A → A × A)
    (hsplit : ∀ q ∈ t, split (cubeProduct q) = q)
    (B : A → A → A → ℂ) (d P c : A)
    (hPx : ∀ q ∈ t, Cop P q.1) :
    frozenCubeInner χ Cop B t d P c =
      fullCubeInner χ Cop (fullCubeCoefficient split B) (t.image cubeProduct) d P c := by
  unfold frozenCubeInner fullCubeInner
  rw [Finset.sum_image (cubeProduct_injective_on t split hsplit)]
  apply Finset.sum_congr rfl
  intro q hq
  have hs : split (q.1 * q.2) = q := hsplit q hq
  simp only [fullCubeCoefficient, cubeProduct, hs]
  rw [frozen_cube_hybrid_summand χ Cop h6 d P c q.1 q.2 (hPx q hq)]
  rfl

/-- `a(P)` may already include the factor `N(P)^(-1/2)` and any fixed
mark-column phases.  It has no row argument. -/
def frozenSeparatedRow (a : A → ℂ) (B : A → A → A → ℂ)
    (marks columns : Finset A) (t : Finset (A × A)) (d : A) : ℂ :=
  ∑ P ∈ marks, a P * (if Cop P d then (1 : ℂ) else 0) *
    ∑ c ∈ columns, frozenCubeInner χ Cop B t d P c

def hybridSeparatedRow (a : A → ℂ) (β : A → A → ℂ)
    (marks columns cubes : Finset A) (d : A) : ℂ :=
  ∑ P ∈ marks, a P * (if Cop P d then (1 : ℂ) else 0) *
    ∑ c ∈ columns, fullCubeInner χ Cop β cubes d P c

/-- Exact finite row assembly into the hybrid form.  The splitting map,
supports, `a`, and `B` are common to every row and active mark. -/
theorem frozenSeparatedRow_eq_hybrid
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (marks columns : Finset A) (t : Finset (A × A))
    (split : A → A × A) (hsplit : ∀ q ∈ t, split (cubeProduct q) = q)
    (a : A → ℂ) (B : A → A → A → ℂ)
    (hPx : ∀ P ∈ marks, ∀ q ∈ t, Cop P q.1) (d : A) :
    frozenSeparatedRow χ Cop a B marks columns t d =
      hybridSeparatedRow χ Cop a (fullCubeCoefficient split B)
        marks columns (t.image cubeProduct) d := by
  unfold frozenSeparatedRow hybridSeparatedRow
  apply Finset.sum_congr rfl
  intro P hP
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  exact frozenCubeInner_eq_fullCubeInner χ Cop h6 t split hsplit B d P c (hPx P hP)

/-- A unimodular frozen row factor disappears from the squared row norm.
This is the exact energy-level exit to the hybrid estimate. -/
theorem frozenSeparatedRow_energy_eq_hybrid
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (rows marks columns : Finset A) (t : Finset (A × A))
    (split : A → A × A) (hsplit : ∀ q ∈ t, split (cubeProduct q) = q)
    (a : A → ℂ) (B : A → A → A → ℂ)
    (hPx : ∀ P ∈ marks, ∀ q ∈ t, Cop P q.1)
    (ρ : A → ℂ) (hρ : ∀ d ∈ rows, ‖ρ d‖ = 1) :
    (∑ d ∈ rows, ‖ρ d * frozenSeparatedRow χ Cop a B marks columns t d‖ ^ 2) =
      ∑ d ∈ rows, ‖hybridSeparatedRow χ Cop a (fullCubeCoefficient split B)
        marks columns (t.image cubeProduct) d‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro d hd
  rw [norm_mul, hρ d hd, one_mul,
    frozenSeparatedRow_eq_hybrid χ Cop h6 marks columns t split hsplit a B hPx d]

end

end HeckeSkeleton.LowFrozenCube
