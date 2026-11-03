import HeckeSkeleton.Moments.MOM_ENGINE_STEP.WholeAllocation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SlotRestriction
import HeckeGeneral.Analysis.SelectedMomentSlots
import HeckePort.Moments.Descent.Quotients

/-!
# The literal child support of an allocated paired polynomial

A nonempty actual allocation fixes every selected prime slot to its
original prime.  The remaining slots are enumerated by the same
selectedSlotIndex used by MomentData.restrictSlots.  Both plain divisor
filters are reindexed by the repository's genuine quotientSupport.
The whole coefficient is evaluated on the reconstructed original tuple.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace HeckeSkeleton.Moments.EngineStep.AllocatedSubsupport

open WholeAllocation HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

def liveSlots (D : Ideal (𝓞 K))
    (v : primeSupport D → Finset (Fin (k + 2))) : Finset (Fin k) :=
  Finset.univ.filter (fun i => ∀ p, i.succ.succ ∉ v p)

theorem live_divisor_eq_one (D : Ideal (𝓞 K))
    (v : primeSupport D → Finset (Fin (k + 2))) (i : Fin k)
    (hi : i ∈ liveSlots D v) : occurrenceDivisor D v i.succ.succ = 1 := by
  apply Finset.prod_eq_one
  intro p hp
  exact False.elim ((Finset.mem_filter.mp hi).2 p (Finset.mem_filter.mp hp).2)

theorem actual_slot_filter (D : Ideal (𝓞 K))
    (v : primeSupport D → Finset (Fin (k + 2))) (i : Fin k)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (frozen : HeightOneSpectrum (𝓞 K))
    (hfrozen : frozen ∈ S.filter (fun p => occurrenceDivisor D v i.succ.succ ∣ p.asIdeal)) :
    S.filter (fun p => occurrenceDivisor D v i.succ.succ ∣ p.asIdeal) =
      if i ∈ liveSlots D v then S else {frozen} := by
  by_cases hi : i ∈ liveSlots D v
  · rw [if_pos hi, live_divisor_eq_one D v i hi]
    simp
  · rw [if_neg hi]
    have hex : ∃ p : primeSupport D, i.succ.succ ∈ v p := by
      by_contra hn
      apply hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      intro p hp
      exact hn ⟨p, hp⟩
    obtain ⟨p, hp⟩ := hex
    have hfixed := selected_prime_slot_eq D v i.succ.succ p frozen hp
      (Finset.mem_filter.mp hfrozen).2
    ext r
    constructor
    · intro hr
      apply Finset.mem_singleton.mpr
      apply HeightOneSpectrum.asIdeal_injective
      exact (selected_prime_slot_eq D v i.succ.succ p r hp
        (Finset.mem_filter.mp hr).2).symm.trans hfixed
    · intro hr
      rw [Finset.mem_singleton.mp hr]
      exact hfrozen

theorem index_eq_selected (keep : Finset (Fin k)) (j : Fin keep.card) :
    SlotRestriction.index keep j = selectedSlotIndex keep j := rfl

theorem actual_allocated_polynomial_restrict
    (D : Ideal (𝓞 K)) (v : primeSupport D → Finset (Fin (k + 2)))
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (frozen : Fin k → HeightOneSpectrum (𝓞 K))
    (hfrozen : ∀ i, frozen i ∈ (S i).filter
      (fun p => occurrenceDivisor D v i.succ.succ ∣ p.asIdeal))
    (C : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → HeightOneSpectrum (𝓞 K)) → ℂ) :
    (∑ x ∈ pairedAllocatedColumns D v S₁ S₂ S id id HeightOneSpectrum.asIdeal, C x) =
      ∑ y ∈ childCartesianColumns
        (S₁.filter (fun I => occurrenceDivisor D v 0 ∣ I))
        (S₂.filter (fun J => occurrenceDivisor D v (Fin.succ 0) ∣ J))
        (fun j => S (selectedSlotIndex (liveSlots D v) j)),
        C (y.1, SlotRestriction.extend (liveSlots D v) frozen y.2) := by
  have hs : (fun i => (S i).filter (fun p => occurrenceDivisor D v i.succ.succ ∣ p.asIdeal)) =
      fun i => if i ∈ liveSlots D v then S i else {frozen i} := by
    funext i
    exact actual_slot_filter D v i (S i) (frozen i) (hfrozen i)
  unfold pairedAllocatedColumns
  rw [hs]
  simp only [childCartesianColumns, Finset.product_eq_sprod, Finset.sum_product]
  exact SlotRestriction.paired_sum_restrict
    (S₁.filter (fun I => occurrenceDivisor D v 0 ∣ I))
    (S₂.filter (fun J => occurrenceDivisor D v (Fin.succ 0) ∣ J))
    (liveSlots D v) S frozen (fun I J x => C ((I, J), x))

theorem paired_plain_quotients {P : Type*} {n : ℕ}
    (B₁ B₂ : Ideal (𝓞 K)) (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin n → Finset P)
    (C : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin n → P) → ℂ) :
    (∑ x ∈ childCartesianColumns
      (S₁.filter (fun I => B₁ ∣ I)) (S₂.filter (fun J => B₂ ∣ J)) S, C x) =
      ∑ y ∈ childCartesianColumns (quotientSupport B₁ S₁) (quotientSupport B₂ S₂) S,
        C ((B₁ * y.1.1, B₂ * y.1.2), y.2) := by
  simp only [childCartesianColumns, Finset.product_eq_sprod, Finset.sum_product]
  rw [sum_quotientSupport B₁ S₁]
  apply Finset.sum_congr rfl
  intro I _
  rw [sum_quotientSupport B₂ S₂]

theorem actual_allocated_polynomial_subsupport
    (D : Ideal (𝓞 K)) (v : primeSupport D → Finset (Fin (k + 2)))
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (frozen : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → HeightOneSpectrum (𝓞 K)))
    (hfrozen : frozen ∈ pairedAllocatedColumns D v S₁ S₂ S id id HeightOneSpectrum.asIdeal)
    (C : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → HeightOneSpectrum (𝓞 K)) → ℂ) :
    (∑ x ∈ pairedAllocatedColumns D v S₁ S₂ S id id HeightOneSpectrum.asIdeal, C x) =
      ∑ y ∈ childCartesianColumns
        (quotientSupport (occurrenceDivisor D v 0) S₁)
        (quotientSupport (occurrenceDivisor D v (Fin.succ 0)) S₂)
        (fun j => S (selectedSlotIndex (liveSlots D v) j)),
        C ((occurrenceDivisor D v 0 * y.1.1,
          occurrenceDivisor D v (Fin.succ 0) * y.1.2),
          SlotRestriction.extend (liveSlots D v) frozen.2 y.2) := by
  have hslots : ∀ i, frozen.2 i ∈ (S i).filter
      (fun p => occurrenceDivisor D v i.succ.succ ∣ p.asIdeal) := by
    have hf := hfrozen
    simp only [pairedAllocatedColumns, childCartesianColumns, Finset.product_eq_sprod,
      Finset.mem_product] at hf
    exact Fintype.mem_piFinset.mp hf.2
  rw [actual_allocated_polynomial_restrict D v S₁ S₂ S frozen.2 hslots C]
  exact paired_plain_quotients (occurrenceDivisor D v 0)
    (occurrenceDivisor D v (Fin.succ 0)) S₁ S₂
    (fun j => S (selectedSlotIndex (liveSlots D v) j))
    (fun y => C (y.1, SlotRestriction.extend (liveSlots D v) frozen.2 y.2))

end HeckeSkeleton.Moments.EngineStep.AllocatedSubsupport

#print axioms HeckeSkeleton.Moments.EngineStep.AllocatedSubsupport.actual_allocated_polynomial_restrict
#print axioms HeckeSkeleton.Moments.EngineStep.AllocatedSubsupport.actual_allocated_polynomial_subsupport
