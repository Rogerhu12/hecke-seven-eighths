module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic

/-!
# Exact restriction to the live slots

The full tuple has a singleton support at every frozen slot.  Restriction
to the actual finite set of live indices is a bijection of finite supports.
All sums retain their original whole coefficient, including when no slot
remains.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep.SlotRestriction

variable {k : ℕ} {P : Type*}

def index (keep : Finset (Fin k)) (j : Fin keep.card) : Fin k :=
  (keep.equivFin.symm j).val

def restrict (keep : Finset (Fin k)) (x : Fin k → P) : Fin keep.card → P :=
  fun j => x (index keep j)

def extend (keep : Finset (Fin k)) (frozen : Fin k → P)
    (y : Fin keep.card → P) : Fin k → P :=
  fun i => if hi : i ∈ keep then y (keep.equivFin ⟨i, hi⟩) else frozen i

def fullSupport (keep : Finset (Fin k)) (S : Fin k → Finset P)
    (frozen : Fin k → P) : Finset (Fin k → P) :=
  Fintype.piFinset (fun i => if i ∈ keep then S i else {frozen i})

def liveSupport (keep : Finset (Fin k)) (S : Fin k → Finset P) :
    Finset (Fin keep.card → P) :=
  Fintype.piFinset (fun j => S (index keep j))

theorem index_mem (keep : Finset (Fin k)) (j : Fin keep.card) : index keep j ∈ keep :=
  (keep.equivFin.symm j).property

@[simp] theorem extend_index (keep : Finset (Fin k)) (frozen : Fin k → P)
    (y : Fin keep.card → P) (j : Fin keep.card) :
    extend keep frozen y (index keep j) = y j := by
  simp only [extend, index, dif_pos (keep.equivFin.symm j).property,
    Subtype.eta, Equiv.apply_symm_apply]

@[simp] theorem restrict_extend (keep : Finset (Fin k)) (frozen : Fin k → P)
    (y : Fin keep.card → P) : restrict keep (extend keep frozen y) = y := by
  funext j
  exact extend_index keep frozen y j

theorem restrict_mem (keep : Finset (Fin k)) (S : Fin k → Finset P)
    (frozen : Fin k → P) (x : Fin k → P) (hx : x ∈ fullSupport keep S frozen) :
    restrict keep x ∈ liveSupport keep S := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have h := Fintype.mem_piFinset.mp hx (index keep j)
  simpa only [restrict, if_pos (index_mem keep j)] using h

theorem extend_mem (keep : Finset (Fin k)) (S : Fin k → Finset P)
    (frozen : Fin k → P) (y : Fin keep.card → P) (hy : y ∈ liveSupport keep S) :
    extend keep frozen y ∈ fullSupport keep S frozen := by
  apply Fintype.mem_piFinset.mpr
  intro i
  by_cases hi : i ∈ keep
  · have h := Fintype.mem_piFinset.mp hy (keep.equivFin ⟨i, hi⟩)
    simpa [extend, index, hi] using h
  · simp [extend, hi]

theorem extend_restrict (keep : Finset (Fin k)) (S : Fin k → Finset P)
    (frozen : Fin k → P) (x : Fin k → P) (hx : x ∈ fullSupport keep S frozen) :
    extend keep frozen (restrict keep x) = x := by
  funext i
  by_cases hi : i ∈ keep
  · simp [extend, restrict, index, hi]
  · have h := Fintype.mem_piFinset.mp hx i
    have he : x i = frozen i := by simpa [hi] using h
    simpa [extend, hi] using he.symm

theorem sum_restrict {B : Type*} [AddCommMonoid B]
    (keep : Finset (Fin k)) (S : Fin k → Finset P) (frozen : Fin k → P)
    (C : (Fin k → P) → B) :
    (∑ x ∈ fullSupport keep S frozen, C x) =
      ∑ y ∈ liveSupport keep S, C (extend keep frozen y) := by
  refine Finset.sum_bij (fun x _ => restrict keep x) ?_ ?_ ?_ ?_
  · intro x hx
    exact restrict_mem keep S frozen x hx
  · intro x hx y hy he
    rw [← extend_restrict keep S frozen x hx,
      ← extend_restrict keep S frozen y hy, he]
  · intro y hy
    exact ⟨extend keep frozen y, extend_mem keep S frozen y hy, restrict_extend keep frozen y⟩
  · intro x hx
    rw [extend_restrict keep S frozen x hx]

theorem paired_sum_restrict {X Y B : Type*} [AddCommMonoid B]
    (S₁ : Finset X) (S₂ : Finset Y)
    (keep : Finset (Fin k)) (S : Fin k → Finset P) (frozen : Fin k → P)
    (C : X → Y → (Fin k → P) → B) :
    (∑ a ∈ S₁, ∑ b ∈ S₂, ∑ x ∈ fullSupport keep S frozen, C a b x) =
      ∑ a ∈ S₁, ∑ b ∈ S₂, ∑ y ∈ liveSupport keep S, C a b (extend keep frozen y) := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact sum_restrict keep S frozen (C a b)

theorem product_extend {M : Type*} [CommMonoid M]
    (keep : Finset (Fin k)) (frozen : Fin k → P) (y : Fin keep.card → P)
    (f : Fin k → P → M) :
    (∏ i, f i (extend keep frozen y i)) =
      (∏ i ∈ Finset.univ.filter (fun i => i ∉ keep), f i (frozen i)) *
        ∏ j, f (index keep j) (y j) := by
  have hk : (∏ i ∈ keep, f i (extend keep frozen y i)) =
      ∏ j, f (index keep j) (y j) := by
    rw [← Finset.prod_coe_sort keep (fun i => f i (extend keep frozen y i))]
    calc
      _ = ∏ j : Fin keep.card,
          f (index keep j) (extend keep frozen y (index keep j)) :=
        (keep.equivFin.symm.prod_comp (fun i : keep => f i.val (extend keep frozen y i.val))).symm
      _ = _ := by simp only [extend_index]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i => i ∈ keep) (fun i => f i (extend keep frozen y i))]
  have hf : Finset.univ.filter (fun i : Fin k => i ∈ keep) = keep := by ext i; simp
  rw [hf, hk, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [extend, dif_neg (Finset.mem_filter.mp hi).2]

end HeckeSkeleton.Moments.EngineStep.SlotRestriction

#print axioms HeckeSkeleton.Moments.EngineStep.SlotRestriction.sum_restrict
#print axioms HeckeSkeleton.Moments.EngineStep.SlotRestriction.product_extend
