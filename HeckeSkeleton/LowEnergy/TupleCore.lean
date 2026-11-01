import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Exact marked-tuple reindexing

Selected slots are fixed, inactive slots remain outside the active row sum,
and disjoint windows make the active prime-set encoding injective.  All
identities are finite linear identities, before any norm is taken.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.TupleCore
open scoped BigOperators Classical

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

def join (P : ι → Prop) [DecidablePred P]
    (a : {i // P i} → α) (b : {i // ¬P i} → α) : ι → α :=
  (Equiv.piEquivPiSubtypeProd P (fun _ => α)).symm (a, b)

theorem join_of_true (P : ι → Prop) [DecidablePred P]
    (a : {i // P i} → α) (b : {i // ¬P i} → α) (i : ι) (hi : P i) :
    join P a b i = a ⟨i, hi⟩ := by simp [join, Equiv.piEquivPiSubtypeProd, hi]

theorem join_of_false (P : ι → Prop) [DecidablePred P]
    (a : {i // P i} → α) (b : {i // ¬P i} → α) (i : ι) (hi : ¬P i) :
    join P a b i = b ⟨i, hi⟩ := by simp [join, Equiv.piEquivPiSubtypeProd, hi]

/-- Separate two sets of slots without changing the order of the row norm. -/
theorem sum_piFinset_split (W : ι → Finset α) (P : ι → Prop)
    [DecidablePred P] (f : (ι → α) → ℂ) :
    (∑ t ∈ Fintype.piFinset W, f t) =
      ∑ a ∈ Fintype.piFinset (fun i : {i // P i} => W i),
      ∑ b ∈ Fintype.piFinset (fun i : {i // ¬P i} => W i), f (join P a b) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => α)
  rw [← Finset.sum_product _ _ (fun ab => f (join P ab.1 ab.2))]
  apply Finset.sum_bij (fun t _ => e t)
  · intro t ht
    have ht' := Fintype.mem_piFinset.mp ht
    exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun i => ht' i),
      Fintype.mem_piFinset.mpr (fun i => ht' i)⟩
  · intro t _ u _ h
    exact e.injective h
  · intro ab hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    refine ⟨e.symm ab, Fintype.mem_piFinset.mpr ?_, e.apply_symm_apply ab⟩
    intro i
    by_cases hi : P i
    · simpa [e, Equiv.piEquivPiSubtypeProd, hi] using
        Fintype.mem_piFinset.mp ha ⟨i, hi⟩
    · simpa [e, Equiv.piEquivPiSubtypeProd, hi] using
        Fintype.mem_piFinset.mp hb ⟨i, hi⟩
  · intro t _
    exact congrArg f (e.symm_apply_apply t).symm

/-- A fixed selected tuple occurs exactly once.  Its coordinates have to be
in their windows, as they are in the target's quantifier over `p`. -/
theorem sum_piFinset_fixed (W : ι → Finset α) (P : ι → Prop)
    [DecidablePred P] (p : ι → α) (hp : ∀ i, P i → p i ∈ W i)
    (f : (ι → α) → ℂ) :
    (∑ t ∈ Fintype.piFinset W, if ∀ i, P i → t i = p i then f t else 0) =
      ∑ b ∈ Fintype.piFinset (fun i : {i // ¬P i} => W i),
        f (join P (fun i => p i) b) := by
  classical
  rw [sum_piFinset_split W P]
  let p₀ : {i // P i} → α := fun i => p i
  have hp₀ : p₀ ∈ Fintype.piFinset (fun i : {i // P i} => W i) :=
    Fintype.mem_piFinset.mpr (fun i => hp i i.property)
  rw [Finset.sum_eq_single_of_mem p₀ hp₀]
  · apply Finset.sum_congr rfl
    intro b _
    have hfix : ∀ i, P i → join P p₀ b i = p i := by
      intro i hi
      exact join_of_true P p₀ b i hi
    rw [if_pos hfix]
  · intro a _ hap
    apply Finset.sum_eq_zero
    intro b _
    apply if_neg
    intro h
    apply hap
    funext i
    simpa only [join_of_true P a b i i.property] using h i i.property

/-- Disjoint windows identify each coordinate from the unordered prime set. -/
theorem image_univ_injOn_piFinset [DecidableEq α] (W : ι → Finset α)
    (hdisjoint : ∀ i j : ι, i ≠ j → Disjoint (W i) (W j)) :
    Set.InjOn (fun t : ι → α => Finset.univ.image t) (Fintype.piFinset W) := by
  classical
  intro t ht u hu heq
  change Finset.univ.image t = Finset.univ.image u at heq
  funext i
  have hi : t i ∈ Finset.univ.image u := by
    rw [← heq]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
  have hij : i = j := by
    by_contra hn
    have hti := Fintype.mem_piFinset.mp ht i
    have huj := Fintype.mem_piFinset.mp hu j
    rw [hj] at huj
    exact Finset.disjoint_left.mp (hdisjoint i j hn) hti huj
  subst j
  exact hj.symm

def pushCoeff {β γ : Type*} (s : Finset β) (encode : β → γ)
    (a : β → ℂ) (g : γ) : ℂ :=
  if h : ∃ b ∈ s, encode b = g then a (Classical.choose h) else 0

theorem pushCoeff_apply {β γ : Type*} (s : Finset β) (encode : β → γ)
    (hinj : Set.InjOn encode s) (a : β → ℂ) {b : β} (hb : b ∈ s) :
    pushCoeff s encode a (encode b) = a b := by
  classical
  have hex : ∃ c ∈ s, encode c = encode b := ⟨b, hb, rfl⟩
  rw [pushCoeff, dif_pos hex]
  exact congrArg a (hinj (Classical.choose_spec hex).1 hb (Classical.choose_spec hex).2)

/-- Encoding the active tuple introduces no coefficient multiplicity. -/
theorem pushCoeff_norm_le {β γ : Type*} (s : Finset β) (encode : β → γ)
    (a : β → ℂ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ b ∈ s, ‖a b‖ ≤ C) (g : γ) :
    ‖pushCoeff s encode a g‖ ≤ C := by
  classical
  unfold pushCoeff
  split_ifs with h
  · exact ha _ (Classical.choose_spec h).1
  · simpa using hC

theorem sum_pushCoeff {β γ : Type*} [DecidableEq γ] (s : Finset β) (encode : β → γ)
    (hinj : Set.InjOn encode s) (a : β → ℂ) (kernel : γ → ℂ) :
    (∑ b ∈ s, a b * kernel (encode b)) =
      ∑ g ∈ s.image encode, pushCoeff s encode a g * kernel g := by
  classical
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro b hb
  rw [pushCoeff_apply s encode hinj a hb]

#print axioms sum_piFinset_split
#print axioms sum_piFinset_fixed
#print axioms image_univ_injOn_piFinset
#print axioms sum_pushCoeff

end HeckeSkeleton.LowEnergy.TupleCore
