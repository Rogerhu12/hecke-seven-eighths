import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedReindex
import HeckeSkeleton.Moments.MOM_INV_STEP.PrimeChoiceSlots

/-!
# Split the literal original prime tuple at its actual overlap slots

The selected and surviving lists are restrictions of the original
disjoint lists.  Their finite tuple product is exactly the original
tuple source.  The selected product is the actual gcd, so the fixed
fibers consumed by `ProviderMarkedMellin` are obtained from the original
source and are not separately prescribed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedTupleSplit

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.Moments.MOM_INV_STEP
open ProviderMarkedOverlap ProviderMarkedSlots ProviderMarkedReindex
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {d : ℕ}

def remaining (J : Finset (Fin d)) : Finset (Fin d) := Finset.univ \ J

def slot (J : Finset (Fin d)) (i : Fin J.card) : Fin d :=
  (J.equivFin.symm i).val

theorem slot_mem (J : Finset (Fin d)) (i : Fin J.card) : slot J i ∈ J :=
  (J.equivFin.symm i).property

theorem slot_injective (J : Finset (Fin d)) : Function.Injective (slot J) := by
  intro i k h
  exact J.equivFin.symm.injective (Subtype.ext h)

theorem slot_equivFin (J : Finset (Fin d)) (i : Fin d) (hi : i ∈ J) :
    slot J (J.equivFin ⟨i, hi⟩) = i :=
  congrArg Subtype.val (J.equivFin.symm_apply_apply ⟨i, hi⟩)

def restrictedLists (J : Finset (Fin d))
    (lists : Fin d → Finset (HeightOneSpectrum (𝓞 K))) :
    Fin J.card → Finset (HeightOneSpectrum (𝓞 K)) := fun i => lists (slot J i)

theorem restrictedLists_disjoint (J : Finset (Fin d))
    (lists : Fin d → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) :
    Pairwise (Disjoint on restrictedLists J lists) := by
  intro i k hik
  exact hdis (fun h => hik (slot_injective J h))

def restrict {β : Type*} (J : Finset (Fin d)) (p : Fin d → β) : Fin J.card → β :=
  fun i => p (slot J i)

def glue {β : Type*} (J : Finset (Fin d))
    (q : Fin J.card → β) (r : Fin (remaining J).card → β) (i : Fin d) : β :=
  if hi : i ∈ J then q (J.equivFin ⟨i, hi⟩)
  else r ((remaining J).equivFin ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩⟩)

theorem glue_selected {β : Type*} (J : Finset (Fin d))
    (q : Fin J.card → β) (r : Fin (remaining J).card → β) (i : Fin J.card) :
    glue J q r (slot J i) = q i := by
  rw [glue, dif_pos (slot_mem J i)]
  change q (J.equivFin (J.equivFin.symm i)) = q i
  rw [Equiv.apply_symm_apply]

theorem glue_remaining {β : Type*} (J : Finset (Fin d))
    (q : Fin J.card → β) (r : Fin (remaining J).card → β)
    (i : Fin (remaining J).card) : glue J q r (slot (remaining J) i) = r i := by
  have hi : slot (remaining J) i ∉ J := (Finset.mem_sdiff.mp (slot_mem (remaining J) i)).2
  rw [glue, dif_neg hi]
  change r ((remaining J).equivFin ((remaining J).equivFin.symm i)) = r i
  rw [Equiv.apply_symm_apply]

theorem glue_restrict {β : Type*} (J : Finset (Fin d)) (p : Fin d → β) :
    glue J (restrict J p) (restrict (remaining J) p) = p := by
  funext i
  by_cases hi : i ∈ J
  · rw [glue, dif_pos hi]
    exact congrArg p (slot_equivFin J i hi)
  · rw [glue, dif_neg hi]
    exact congrArg p (slot_equivFin (remaining J) i
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩))

theorem restrict_glue_selected {β : Type*} (J : Finset (Fin d))
    (q : Fin J.card → β) (r : Fin (remaining J).card → β) :
    restrict J (glue J q r) = q := funext (glue_selected J q r)

theorem restrict_glue_remaining {β : Type*} (J : Finset (Fin d))
    (q : Fin J.card → β) (r : Fin (remaining J).card → β) :
    restrict (remaining J) (glue J q r) = r := funext (glue_remaining J q r)

theorem restrict_mem (J : Finset (Fin d))
    (lists : Fin d → Finset (HeightOneSpectrum (𝓞 K)))
    (p : Fin d → HeightOneSpectrum (𝓞 K)) (hp : p ∈ tuples lists) :
    restrict J p ∈ tuples (restrictedLists J lists) :=
  Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mp hp (slot J i)

theorem glue_mem (J : Finset (Fin d))
    (lists : Fin d → Finset (HeightOneSpectrum (𝓞 K)))
    (q : Fin J.card → HeightOneSpectrum (𝓞 K))
    (r : Fin (remaining J).card → HeightOneSpectrum (𝓞 K))
    (hq : q ∈ tuples (restrictedLists J lists))
    (hr : r ∈ tuples (restrictedLists (remaining J) lists)) :
    glue J q r ∈ tuples lists := by
  apply Fintype.mem_piFinset.mpr
  intro i
  by_cases hi : i ∈ J
  · rw [glue, dif_pos hi]
    have h := Fintype.mem_piFinset.mp hq (J.equivFin ⟨i, hi⟩)
    simpa only [restrictedLists, slot_equivFin] using h
  · rw [glue, dif_neg hi]
    have hri : i ∈ remaining J := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
    have h := Fintype.mem_piFinset.mp hr ((remaining J).equivFin ⟨i, hri⟩)
    simpa only [restrictedLists, slot_equivFin] using h

/-- An exact finite source bijection; no choice multiplicity is lost. -/
theorem sum_tuples_split (J : Finset (Fin d))
    (lists : Fin d → Finset (HeightOneSpectrum (𝓞 K)))
    (f : (Fin d → HeightOneSpectrum (𝓞 K)) → ℂ) :
    (∑ p ∈ tuples lists, f p) =
      ∑ q ∈ tuples (restrictedLists J lists),
        ∑ r ∈ tuples (restrictedLists (remaining J) lists), f (glue J q r) := by
  symm
  rw [← Finset.sum_product]
  apply Finset.sum_bij (fun qr hqr => glue J qr.1 qr.2)
  · intro qr hqr
    exact glue_mem J lists qr.1 qr.2 (Finset.mem_product.mp hqr).1
      (Finset.mem_product.mp hqr).2
  · intro qr hqr qr' hqr' heq
    apply Prod.ext
    · have h := congrArg (restrict J) heq
      simpa only [restrict_glue_selected] using h
    · have h := congrArg (restrict (remaining J)) heq
      simpa only [restrict_glue_remaining] using h
  · intro p hp
    exact ⟨(restrict J p, restrict (remaining J) p),
      Finset.mem_product.mpr ⟨restrict_mem J lists p hp, restrict_mem (remaining J) lists p hp⟩,
      glue_restrict J p⟩
  · intro qr hqr
    rfl

theorem restriction_product {M : Type*} [CommMonoid M]
    (J : Finset (Fin d)) (f : Fin d → M) :
    (∏ i, f (slot J i)) = ∏ i ∈ J, f i := by
  calc
    _ = ∏ i : J, f i.val := Fintype.prod_equiv J.equivFin.symm _ _ (fun _ => rfl)
    _ = _ := Finset.prod_coe_sort J f

theorem primeProduct_glue (J : Finset (Fin d))
    (q : Fin J.card → HeightOneSpectrum (𝓞 K))
    (r : Fin (remaining J).card → HeightOneSpectrum (𝓞 K)) :
    primeProduct Finset.univ (glue J q r) =
      primeProduct Finset.univ q * primeProduct Finset.univ r := by
  rw [primeProduct_split Finset.univ J (Finset.subset_univ _) (glue J q r)]
  change (∏ i ∈ J, (glue J q r i).asIdeal) *
      (∏ i ∈ remaining J, (glue J q r i).asIdeal) = _
  rw [← restriction_product J (fun i => (glue J q r i).asIdeal),
    ← restriction_product (remaining J) (fun i => (glue J q r i).asIdeal)]
  simp only [glue_selected, glue_remaining, primeProduct]

/-- Coprimality of the selected and remaining products follows from
the original lists before any row-dependent mask is inserted. -/
theorem selected_remaining_coprime (J : Finset (Fin d))
    (lists : Fin d → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists))
    (q : Fin J.card → HeightOneSpectrum (𝓞 K))
    (r : Fin (remaining J).card → HeightOneSpectrum (𝓞 K))
    (hq : q ∈ tuples (restrictedLists J lists))
    (hr : r ∈ tuples (restrictedLists (remaining J) lists)) :
    IsCoprime (primeProduct Finset.univ q) (primeProduct Finset.univ r) := by
  have hsf := tuple_product_squarefree lists hdis (glue J q r)
    (glue_mem J lists q r hq hr)
  rw [primeProduct_glue] at hsf
  exact ideal_coprime_of_relPrime (squarefree_mul_iff.mp hsf).1

theorem selected_product_glue (J : Finset (Fin d))
    (q : Fin J.card → HeightOneSpectrum (𝓞 K))
    (r : Fin (remaining J).card → HeightOneSpectrum (𝓞 K)) :
    primeProduct J (glue J q r) = primeProduct Finset.univ q := by
  change (∏ i ∈ J, (glue J q r i).asIdeal) = _
  rw [← restriction_product J (fun i => (glue J q r i).asIdeal)]
  simp only [glue_selected, primeProduct]

theorem primeProduct_subsets_injective (p : Fin d → HeightOneSpectrum (𝓞 K))
    (hinj : Function.Injective p) (I J : Finset (Fin d))
    (heq : primeProduct I p = primeProduct J p) : I = J := by
  have hsub {A B : Finset (Fin d)}
      (hAB : primeProduct A p = primeProduct B p) : A ⊆ B := by
    intro i hi
    have hpi : (p i).asIdeal ∣ primeProduct B p := by
      rw [← hAB]
      exact Finset.dvd_prod_of_mem (fun i => (p i).asIdeal) hi
    obtain ⟨k, hk, hdvd⟩ := ((p i).prime.dvd_finsetProd_iff
      (fun k => (p k).asIdeal)).mp hpi
    have hik : p i = p k := by
      by_contra hne
      exact (p i).prime.not_unit (((p i).isCoprime_of_ne (p k) hne).isUnit_of_dvd hdvd)
    exact (hinj hik).symm ▸ hk
  exact Finset.Subset.antisymm (hsub heq) (hsub heq.symm)

/-- The selected subset is determined by the original gcd, with no
possibility of a second subset representing the same label. -/
theorem commonSlots_eq_iff_gcd
    (p : Fin d → HeightOneSpectrum (𝓞 K)) (hinj : Function.Injective p)
    (n : Ideal (𝓞 K)) (J : Finset (Fin d)) :
    commonSlots Finset.univ p n = J ↔ gcd n (primeProduct Finset.univ p) = primeProduct J p := by
  have hg := commonSlots_product_eq_gcd Finset.univ p
    (fun _ _ _ _ heq => hinj heq) n
  constructor
  · intro hJ
    rw [← hg, hJ]
  · intro hJ
    exact primeProduct_subsets_injective p hinj _ _ (hg.trans hJ)

/-- Exact grouping over all overlap subsets before any selected tuple
is frozen. Every source pair occurs in exactly one summand. -/
theorem sum_commonSlots_partition
    (lists : Fin d → Finset (HeightOneSpectrum (𝓞 K)))
    (N : Finset (Ideal (𝓞 K)))
    (f : (Fin d → HeightOneSpectrum (𝓞 K)) → Ideal (𝓞 K) → ℂ) :
    (∑ p ∈ tuples lists, ∑ n ∈ N, f p n) =
      ∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ p ∈ tuples lists, ∑ n ∈ N.filter (fun n => commonSlots Finset.univ p n = J),
          f p n := by
  calc
    _ = ∑ p ∈ tuples lists, ∑ n ∈ N,
        ∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
          if commonSlots Finset.univ p n = J then f p n else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro n hn
      symm
      rw [Finset.sum_eq_single (commonSlots Finset.univ p n)]
      · simp only [ite_true]
      · intro J hJ hne
        exact if_neg (Ne.symm hne)
      · intro hnot
        exact (hnot (Finset.mem_powerset.mpr (Finset.filter_subset _ _))).elim
    _ = ∑ p ∈ tuples lists, ∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ n ∈ N, if commonSlots Finset.univ p n = J then f p n else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]

theorem sourcePool_eq_selected_filter
    (J : Finset (Fin d))
    (lists : Fin d → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists))
    (q : Fin J.card → HeightOneSpectrum (𝓞 K))
    (r : Fin (remaining J).card → HeightOneSpectrum (𝓞 K))
    (hq : q ∈ tuples (restrictedLists J lists))
    (hr : r ∈ tuples (restrictedLists (remaining J) lists)) (X : ℝ) :
    ProviderMarkedPools.sourcePool X (primeProduct Finset.univ q) (primeProduct Finset.univ r) =
      ((ProviderMarkedPools.pool X).filter Squarefree).filter
        (fun n => commonSlots Finset.univ (glue J q r) n = J) := by
  have hinj := tuple_injective lists hdis (glue J q r) (glue_mem J lists q r hq hr)
  ext n
  simp only [ProviderMarkedPools.sourcePool, Finset.mem_filter,
    commonSlots_eq_iff_gcd (glue J q r) hinj n J, primeProduct_glue, selected_product_glue]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- The complete actual initial overlap decomposition: first the
actual subset, then its original selected tuple, then all remaining
original tuples, and finally the proved fixed gcd fiber. -/
theorem full_source_decomposition
    (lists : Fin d → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (X : ℝ)
    (f : (Fin d → HeightOneSpectrum (𝓞 K)) → Ideal (𝓞 K) → ℂ) :
    (∑ p ∈ tuples lists, ∑ n ∈ (ProviderMarkedPools.pool X).filter Squarefree, f p n) =
      ∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ q ∈ tuples (restrictedLists J lists),
          ∑ r ∈ tuples (restrictedLists (remaining J) lists),
            ∑ n ∈ ProviderMarkedPools.sourcePool X
              (primeProduct Finset.univ q) (primeProduct Finset.univ r),
              f (glue J q r) n := by
  rw [sum_commonSlots_partition]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [sum_tuples_split J lists]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  rw [sourcePool_eq_selected_filter J lists hdis q r hq hr X]

theorem weight_glue (J : Finset (Fin d))
    (a : Fin d → HeightOneSpectrum (𝓞 K) → ℂ)
    (q : Fin J.card → HeightOneSpectrum (𝓞 K))
    (r : Fin (remaining J).card → HeightOneSpectrum (𝓞 K)) :
    (∏ i, a i (glue J q r i)) =
      (∏ i, a (slot J i) (q i)) *
        (∏ i, a (slot (remaining J) i) (r i)) := by
  rw [← Finset.prod_sdiff (Finset.subset_univ J)]
  change (∏ i ∈ remaining J, a i (glue J q r i)) *
      (∏ i ∈ J, a i (glue J q r i)) = _
  rw [← restriction_product (remaining J) (fun i => a i (glue J q r i)),
    ← restriction_product J (fun i => a i (glue J q r i))]
  simp only [glue_remaining, glue_selected]
  exact mul_comm _ _

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedTupleSplit
