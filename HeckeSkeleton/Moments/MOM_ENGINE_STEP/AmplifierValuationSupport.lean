import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ValuationAllocation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.WholeAllocation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SlotRestriction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Ledger
import HeckeGeneral.Analysis.SelectedMomentSlots

/-!
# Actual slot supports in the errors of depth one, six, and seven

Exact valuations are distributed over both plain occurrences and every
prime slot.  A slot of valuation zero retains its support with the
amplifying prime erased; valuation one freezes that slot to that actual
prime; higher valuation makes the branch empty.  Nonempty branches use
the same selectedSlotIndex as the genuine child geometry.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace HeckeSkeleton.Moments.EngineStep.AmplifierValuationSupport

open WholeAllocation HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]

theorem prime_slot_count (p r : HeightOneSpectrum (𝓞 K)) :
    (normalizedFactors r.asIdeal).count p.asIdeal = if r = p then 1 else 0 := by
  by_cases h : r = p
  · subst r
    simp [normalizedFactors_irreducible p.irreducible, normalize_eq]
  · have hI : p.asIdeal ≠ r.asIdeal :=
      fun he => h (HeightOneSpectrum.asIdeal_injective he.symm)
    simp [normalizedFactors_irreducible r.irreducible, normalize_eq, h, hI]

theorem prime_slot_zero (p : HeightOneSpectrum (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    S.filter (fun r => (normalizedFactors r.asIdeal).count p.asIdeal = 0) = S.erase p := by
  ext r
  by_cases h : r = p <;> simp [prime_slot_count, h, Finset.mem_erase, and_comm]

theorem prime_slot_one (p : HeightOneSpectrum (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hp : p ∈ S) :
    S.filter (fun r => (normalizedFactors r.asIdeal).count p.asIdeal = 1) = {p} := by
  ext r
  by_cases h : r = p <;> simp [prime_slot_count, h, hp]

theorem prime_slot_large_empty (p : HeightOneSpectrum (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : 2 ≤ n) :
    S.filter (fun r => (normalizedFactors r.asIdeal).count p.asIdeal = n) = ∅ := by
  ext r
  constructor
  · intro hr
    exfalso
    have hc := (Finset.mem_filter.mp hr).2
    rw [prime_slot_count] at hc
    split_ifs at hc <;> omega
  · simp

theorem prime_slot_filter_of_nonempty (p : HeightOneSpectrum (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (r : HeightOneSpectrum (𝓞 K))
    (hr : r ∈ S.filter (fun r => (normalizedFactors r.asIdeal).count p.asIdeal = n)) :
    S.filter (fun r => (normalizedFactors r.asIdeal).count p.asIdeal = n) =
      if n = 0 then S.erase p else {p} := by
  by_cases hn : n = 0
  · rw [hn, if_pos rfl]
    exact prime_slot_zero p S
  · rw [if_neg hn]
    have hc := (Finset.mem_filter.mp hr).2
    have hrp : r = p := by
      by_contra h
      rw [prime_slot_count, if_neg h] at hc
      exact hn hc.symm
    have hp : p ∈ S := hrp ▸ (Finset.mem_filter.mp hr).1
    have hn1 : n = 1 := by
      rw [prime_slot_count, if_pos hrp] at hc
      exact hc.symm
    rw [hn1]
    exact prime_slot_one p S hp

section Paired

variable {X Y : Type*} {k : ℕ}

def liveSlots (n : Fin (k + 2) → ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => n i.succ.succ = 0)

def pairedColumns (p : HeightOneSpectrum (𝓞 K)) (n : Fin (k + 2) → ℕ)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) :
    Finset ((X × Y) × (Fin k → HeightOneSpectrum (𝓞 K))) :=
  childCartesianColumns
    (S₁.filter (fun x => (normalizedFactors (I x)).count p.asIdeal = n 0))
    (S₂.filter (fun y => (normalizedFactors (J y)).count p.asIdeal = n (Fin.succ 0)))
    (fun i => (S i).filter
      (fun r => (normalizedFactors r.asIdeal).count p.asIdeal = n i.succ.succ))

theorem paired_columns_eq_filter (p : HeightOneSpectrum (𝓞 K)) (n : Fin (k + 2) → ℕ)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) :
    pairedColumns p n S₁ S₂ S I J =
      (childCartesianColumns S₁ S₂ S).filter
        (fun x => ∀ i, (normalizedFactors
          (pairedOccurrences I J HeightOneSpectrum.asIdeal x i)).count p.asIdeal = n i) := by
  ext x
  simp only [pairedColumns, childCartesianColumns, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_filter, Fintype.mem_piFinset,
    pairedOccurrences, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, forall_and]
  tauto

theorem whole_error_polynomial (p : HeightOneSpectrum (𝓞 K)) (j : ℕ)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K))
    (hI : ∀ x ∈ S₁, I x ≠ 0) (hJ : ∀ y ∈ S₂, J y ≠ 0)
    (C : (X × Y) × (Fin k → HeightOneSpectrum (𝓞 K)) → ℂ) :
    (∑ x ∈ childCartesianColumns S₁ S₂ S with
      (normalizedFactors (I x.1.1 * J x.1.2 * ∏ i, (x.2 i).asIdeal)).count p.asIdeal = j, C x) =
      ∑ n ∈ ValuationAllocation.choices (k + 2) j,
        ∑ x ∈ pairedColumns p n S₁ S₂ S I J, C x := by
  have ha : ∀ x ∈ childCartesianColumns S₁ S₂ S,
      ∀ i, pairedOccurrences I J HeightOneSpectrum.asIdeal x i ≠ 0 := by
    intro x hx i
    simp only [childCartesianColumns, Finset.product_eq_sprod, Finset.mem_product,
      Fintype.mem_piFinset] at hx
    refine Fin.cases ?_ (fun t => Fin.cases ?_ (fun l => ?_) t) i
    · exact hI x.1.1 hx.1.1
    · exact hJ x.1.2 hx.1.2
    · exact (x.2 l).ne_bot
  calc
    _ = ∑ x ∈ childCartesianColumns S₁ S₂ S with
        (normalizedFactors (∏ i, pairedOccurrences I J HeightOneSpectrum.asIdeal x i)).count
          p.asIdeal = j, C x := by
      apply Finset.sum_congr ?_ (fun x _ => rfl)
      ext x
      simp only [Finset.mem_filter, paired_occurrences_product]
    _ = ∑ n ∈ ValuationAllocation.choices (k + 2) j,
        ∑ x ∈ childCartesianColumns S₁ S₂ S with
          ∀ i, (normalizedFactors
            (pairedOccurrences I J HeightOneSpectrum.asIdeal x i)).count p.asIdeal = n i,
          C x := ValuationAllocation.whole_polynomial
      (childCartesianColumns S₁ S₂ S) (k + 2) j
      p.asIdeal (pairedOccurrences I J HeightOneSpectrum.asIdeal) C ha
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr ?_ (fun x _ => rfl)
      ext x
      rw [paired_columns_eq_filter] <;> simp only [Finset.mem_filter]

theorem actual_error_polynomial_subsupport
    (p : HeightOneSpectrum (𝓞 K)) (n : Fin (k + 2) → ℕ)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K))
    (frozen : (X × Y) × (Fin k → HeightOneSpectrum (𝓞 K)))
    (hfrozen : frozen ∈ pairedColumns p n S₁ S₂ S I J)
    (C : (X × Y) × (Fin k → HeightOneSpectrum (𝓞 K)) → ℂ) :
    (∑ x ∈ pairedColumns p n S₁ S₂ S I J, C x) =
      ∑ y ∈ childCartesianColumns
        (S₁.filter (fun x => (normalizedFactors (I x)).count p.asIdeal = n 0))
        (S₂.filter (fun y => (normalizedFactors (J y)).count p.asIdeal = n (Fin.succ 0)))
        (fun j => (S (selectedSlotIndex (liveSlots n) j)).erase p),
        C (y.1, SlotRestriction.extend (liveSlots n) (fun _ => p) y.2) := by
  have hf := hfrozen
  simp only [pairedColumns, childCartesianColumns, Finset.product_eq_sprod,
    Finset.mem_product] at hf
  have hs : (fun i => (S i).filter
      (fun r => (normalizedFactors r.asIdeal).count p.asIdeal = n i.succ.succ)) =
      fun i => if i ∈ liveSlots n then (S i).erase p else {p} := by
    funext i
    have hi := Fintype.mem_piFinset.mp hf.2 i
    simpa only [liveSlots, Finset.mem_filter, Finset.mem_univ, true_and] using
      prime_slot_filter_of_nonempty p (S i) (n i.succ.succ) (frozen.2 i) hi
  unfold pairedColumns
  rw [hs]
  simp only [childCartesianColumns, Finset.product_eq_sprod, Finset.sum_product]
  exact SlotRestriction.paired_sum_restrict
    (S₁.filter (fun x => (normalizedFactors (I x)).count p.asIdeal = n 0))
    (S₂.filter (fun y => (normalizedFactors (J y)).count p.asIdeal = n (Fin.succ 0)))
    (liveSlots n) (fun i => (S i).erase p) (fun _ => p) (fun x y z => C ((x, y), z))

theorem amplifier_error_allocation_count (e : AmplifierValuation) :
    (ValuationAllocation.choices (k + 2) e.multiplicity).card ≤ 8 ^ (k + 2) :=
  ValuationAllocation.card_choices_le_eight _ _ (by cases e <;> decide)

end Paired
end HeckeSkeleton.Moments.EngineStep.AmplifierValuationSupport

#print axioms HeckeSkeleton.Moments.EngineStep.AmplifierValuationSupport.whole_error_polynomial
#print axioms HeckeSkeleton.Moments.EngineStep.AmplifierValuationSupport.actual_error_polynomial_subsupport
