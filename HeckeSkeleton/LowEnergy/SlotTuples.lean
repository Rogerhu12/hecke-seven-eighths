import HeckeSkeleton.LowEnergy.TupleCore
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Exact selected, active and inactive slot reconstruction

The selected coordinates are fixed.  The active and inactive tuples range
over their actual original slot subtypes.  The bijection below removes all
nested subtype changes from the target marked-row assembly.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.SlotTuples

open scoped Classical BigOperators

variable {ι α : Type*} [Fintype ι]

theorem card_partition (J A : Finset ι) (hA : A ⊆ Finset.univ \ J) :
    J.card + A.card + (Finset.univ \ J \ A).card = Fintype.card ι := by
  have hJ := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ J)
  have hI := Finset.card_sdiff_add_card_eq_card hA
  rw [Finset.card_univ] at hJ
  omega

def fill (J A : Finset ι) (p : ι → α) (a : A → α)
    (b : (Finset.univ \ J \ A) → α) : ι → α :=
  fun i => if hJ : i ∈ J then p i else if hA : i ∈ A then a ⟨i, hA⟩ else
    b ⟨i, by simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]; exact ⟨hJ, hA⟩⟩

theorem fill_selected (J A : Finset ι) (p : ι → α) (a : A → α)
    (b : (Finset.univ \ J \ A) → α) (i : ι) (hi : i ∈ J) :
    fill J A p a b i = p i := by simp only [fill, dif_pos hi]

theorem fill_active (J A : Finset ι) (hA : A ⊆ Finset.univ \ J)
    (p : ι → α) (a : A → α) (b : (Finset.univ \ J \ A) → α)
    (i : A) : fill J A p a b i = a i := by
  have hiJ := (Finset.mem_sdiff.mp (hA i.property)).2
  simp only [fill, dif_neg hiJ, dif_pos i.property]

theorem fill_inactive (J A : Finset ι) (p : ι → α) (a : A → α)
    (b : (Finset.univ \ J \ A) → α) (i : (Finset.univ \ J \ A)) :
    fill J A p a b i = b i := by
  have hi := Finset.mem_sdiff.mp i.property
  have hiJ := (Finset.mem_sdiff.mp hi.1).2
  simp only [fill, dif_neg hiJ, dif_neg hi.2]

theorem fill_fixed (J A : Finset ι) (p : ι → α) (a : A → α)
    (b : (Finset.univ \ J \ A) → α) :
    ∀ i ∈ J, fill J A p a b i = p i :=
  fun i hi => fill_selected J A p a b i hi

theorem fill_restrict (J A : Finset ι) (hA : A ⊆ Finset.univ \ J)
    (p t : ι → α) (ht : ∀ i ∈ J, t i = p i) :
    fill J A p (fun i => t i) (fun i => t i) = t := by
  funext i
  by_cases hiJ : i ∈ J
  · exact (fill_selected J A p _ _ i hiJ).trans (ht i hiJ).symm
  · by_cases hiA : i ∈ A
    · exact fill_active J A hA p _ _ ⟨i, hiA⟩
    · exact fill_inactive J A p _ _ ⟨i, by simp [hiJ, hiA]⟩

theorem fill_mem_piFinset (W : ι → Finset α)
    (J A : Finset ι) (hA : A ⊆ Finset.univ \ J)
    (p : ι → α) (hp : ∀ i ∈ J, p i ∈ W i)
    (a : A → α) (b : (Finset.univ \ J \ A) → α)
    (ha : a ∈ Fintype.piFinset (fun i : A => W i))
    (hb : b ∈ Fintype.piFinset (fun i : (Finset.univ \ J \ A) => W i)) :
    fill J A p a b ∈ Fintype.piFinset W := by
  apply Fintype.mem_piFinset.mpr
  intro i
  by_cases hiJ : i ∈ J
  · rw [fill_selected J A p a b i hiJ]
    exact hp i hiJ
  · by_cases hiA : i ∈ A
    · rw [fill_active J A hA p a b ⟨i, hiA⟩]
      exact Fintype.mem_piFinset.mp ha ⟨i, hiA⟩
    · let ii : (Finset.univ \ J \ A) := ⟨i, by simp [hiJ, hiA]⟩
      rw [fill_inactive J A p a b ii]
      exact Fintype.mem_piFinset.mp hb ii

/-- The inactive tuple is the outer sum; active marks remain in the linear
inner row.  There is one full tuple for each pair of partial tuples. -/
theorem sum_pi_fixed_active_split (W : ι → Finset α)
    (J A : Finset ι) (hA : A ⊆ Finset.univ \ J)
    (p : ι → α) (hp : ∀ i ∈ J, p i ∈ W i) (f : (ι → α) → ℂ) :
    (∑ t ∈ Fintype.piFinset W, if ∀ i ∈ J, t i = p i then f t else 0) =
      ∑ b ∈ Fintype.piFinset (fun i : (Finset.univ \ J \ A) => W i),
        ∑ a ∈ Fintype.piFinset (fun i : A => W i), f (fill J A p a b) := by
  rw [← Finset.sum_filter]
  rw [← Finset.sum_product _ _ (fun ba => f (fill J A p ba.2 ba.1))]
  apply Finset.sum_bij (fun t _ =>
    ((fun i : (Finset.univ \ J \ A) => t i), (fun i : A => t i)))
  · intro t ht
    have htW := Fintype.mem_piFinset.mp (Finset.mem_filter.mp ht).1
    exact Finset.mem_product.mpr
      ⟨Fintype.mem_piFinset.mpr (fun i => htW i),
        Fintype.mem_piFinset.mpr (fun i => htW i)⟩
  · intro t ht u hu htu
    have htJ := (Finset.mem_filter.mp ht).2
    have huJ := (Finset.mem_filter.mp hu).2
    funext i
    by_cases hiJ : i ∈ J
    · exact (htJ i hiJ).trans (huJ i hiJ).symm
    · by_cases hiA : i ∈ A
      · exact congrArg (fun ba => ba.2 ⟨i, hiA⟩) htu
      · let ii : (Finset.univ \ J \ A) := ⟨i, by simp [hiJ, hiA]⟩
        exact congrArg (fun ba => ba.1 ii) htu
  · intro ba hba
    obtain ⟨hb, ha⟩ := Finset.mem_product.mp hba
    refine ⟨fill J A p ba.2 ba.1, Finset.mem_filter.mpr
      ⟨fill_mem_piFinset W J A hA p hp ba.2 ba.1 ha hb,
        fill_fixed J A p ba.2 ba.1⟩, ?_⟩
    apply Prod.ext
    · funext i
      exact fill_inactive J A p ba.2 ba.1 i
    · funext i
      exact fill_active J A hA p ba.2 ba.1 i
  · intro t ht
    exact congrArg f (fill_restrict J A hA p t (Finset.mem_filter.mp ht).2).symm

/-- The actual surviving prime set is the union of the two partial images. -/
theorem image_surviving_fill (J A : Finset ι) (hA : A ⊆ Finset.univ \ J)
    (p : ι → α) (a : A → α) (b : (Finset.univ \ J \ A) → α) :
    (Finset.univ \ J).image (fill J A p a b) =
      Finset.univ.image a ∪ Finset.univ.image b := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    by_cases hiA : i ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨⟨i, hiA⟩, Finset.mem_univ _, (fill_active J A hA p a b ⟨i, hiA⟩).symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨⟨i, Finset.mem_sdiff.mpr ⟨hi, hiA⟩⟩, Finset.mem_univ _,
          (fill_inactive J A p a b ⟨i, Finset.mem_sdiff.mpr ⟨hi, hiA⟩⟩).symm⟩)
  · intro hq
    rcases Finset.mem_union.mp hq with hqa | hqb
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hqa
      exact Finset.mem_image.mpr ⟨i, hA i.property,
        (fill_active J A hA p a b i).trans hi⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hqb
      exact Finset.mem_image.mpr ⟨i, (Finset.mem_sdiff.mp i.property).1,
        (fill_inactive J A p a b i).trans hi⟩

theorem image_active_fill (J A : Finset ι) (hA : A ⊆ Finset.univ \ J)
    (p : ι → α) (a : A → α) (b : (Finset.univ \ J \ A) → α) :
    A.image (fill J A p a b) = Finset.univ.image a := by
  ext q
  constructor
  · rintro hq
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _,
      (fill_active J A hA p a b ⟨i, hi⟩).symm.trans heq⟩
  · rintro hq
    obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨i, i.property, (fill_active J A hA p a b i).trans heq⟩

theorem image_inactive_fill (J A : Finset ι)
    (p : ι → α) (a : A → α) (b : (Finset.univ \ J \ A) → α) :
    (Finset.univ \ J \ A).image (fill J A p a b) = Finset.univ.image b := by
  ext q
  constructor
  · rintro hq
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _,
      (fill_inactive J A p a b ⟨i, hi⟩).symm.trans heq⟩
  · rintro hq
    obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨i, i.property, (fill_inactive J A p a b i).trans heq⟩

theorem active_inactive_images_disjoint (J A : Finset ι)
    (hA : A ⊆ Finset.univ \ J) (p : ι → α) (a : A → α)
    (b : (Finset.univ \ J \ A) → α) (hinj : Function.Injective (fill J A p a b)) :
    Disjoint (Finset.univ.image a) (Finset.univ.image b) := by
  apply Finset.disjoint_left.mpr
  intro q hqa hqb
  obtain ⟨ia, _, haq⟩ := Finset.mem_image.mp hqa
  obtain ⟨ib, _, hbq⟩ := Finset.mem_image.mp hqb
  have hidx : ia.val = ib.val := hinj
    ((fill_active J A hA p a b ia).trans (haq.trans (hbq.symm.trans
      (fill_inactive J A p a b ib).symm)))
  exact (Finset.mem_sdiff.mp ib.property).2 (hidx ▸ ia.property)

#print axioms sum_pi_fixed_active_split
#print axioms image_surviving_fill
#print axioms active_inactive_images_disjoint

end HeckeSkeleton.LowEnergy.SlotTuples
