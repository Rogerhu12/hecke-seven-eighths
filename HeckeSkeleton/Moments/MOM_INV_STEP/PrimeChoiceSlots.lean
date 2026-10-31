module

public import HeckeSkeleton.Moments.MOM_INV_STEP.AssignedMarkSource
public import Mathlib.Data.Fintype.EquivFin

/-!
# Original slot sets and their actual doubled prime choices

The canonical family stores arbitrary finite slot sets and lists of
prime ideals. These definitions only enumerate those same slots and
package the same ideals as height-one primes. Every individual weight
is unchanged. The resulting doubled choices have exactly twice the
original number of slots and no additional multiplicity.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrimeChoiceSlots

open NumberField IsDedekindDomain
open HeckeSkeleton.Moments.MOMInvStep AssignedMarkSource
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {σ : Type*}

def slot (J : Finset σ) (i : Fin J.card) : σ := (J.equivFin.symm i).val

theorem slot_mem (J : Finset σ) (i : Fin J.card) : slot J i ∈ J :=
  (J.equivFin.symm i).property

def primeLift (L : Finset (Ideal (𝓞 K))) (hL : ∀ p ∈ L, Prime p) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  L.attach.image fun p => HeightOneSpectrum.ofPrime (hL p.val p.property)

theorem primeLift_image (L : Finset (Ideal (𝓞 K))) (hL : ∀ p ∈ L, Prime p) :
    (primeLift L hL).image HeightOneSpectrum.asIdeal = L := by
  ext I
  simp only [primeLift, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨p,⟨q,rfl⟩,rfl⟩
    exact q.property
  · intro hI
    exact ⟨HeightOneSpectrum.ofPrime (hL I hI), ⟨⟨I,hI⟩,rfl⟩,rfl⟩

theorem mem_primeLift (L : Finset (Ideal (𝓞 K))) (hL : ∀ p ∈ L, Prime p)
    (p : HeightOneSpectrum (𝓞 K)) : p ∈ primeLift L hL ↔ p.asIdeal ∈ L := by
  constructor
  · intro hp
    have hi : p.asIdeal ∈ (primeLift L hL).image HeightOneSpectrum.asIdeal :=
      Finset.mem_image.mpr ⟨p,hp,rfl⟩
    rwa [primeLift_image] at hi
  · intro hp
    have hi : p.asIdeal ∈ (primeLift L hL).image HeightOneSpectrum.asIdeal := by
      rwa [primeLift_image]
    obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hi
    exact HeightOneSpectrum.asIdeal_injective hqp ▸ hq

def lists (J : Finset σ) (P : σ → Finset (Ideal (𝓞 K)))
    (hP : ∀ i ∈ J, ∀ p ∈ P i, Prime p) :
    Fin J.card → Finset (HeightOneSpectrum (𝓞 K)) :=
  fun i => primeLift (P (slot J i)) (hP _ (slot_mem J i))

def weights (J : Finset σ) (a : σ → Ideal (𝓞 K) → ℂ) :
    Fin J.card → Ideal (𝓞 K) → ℂ := fun i => a (slot J i)

theorem original_weights (J : Finset σ) (P : σ → Finset (Ideal (𝓞 K)))
    (hP : ∀ i ∈ J, ∀ p ∈ P i, Prime p) (a : σ → Ideal (𝓞 K) → ℂ)
    (ha : ∀ i ∈ J, ∀ p ∈ P i, ‖a i p‖ ≤ 1) :
    ∀ i, ∀ p ∈ lists J P hP i, ‖weights J a i p.asIdeal‖ ≤ 1 := by
  intro i p hp
  exact ha _ (slot_mem J i) _ ((mem_primeLift _ _ p).mp hp)

theorem divisorMark_selected (J : Finset σ) (P : σ → Finset (Ideal (𝓞 K)))
    (hP : ∀ i ∈ J, ∀ p ∈ P i, Prime p) (a : σ → Ideal (𝓞 K) → ℂ)
    (E : Ideal (𝓞 K)) :
    divisorMark Finset.univ (fun i => (lists J P hP i).image HeightOneSpectrum.asIdeal)
      (weights J a) E = divisorMark J P a E := by
  simp only [lists, primeLift_image, divisorMark, weights]
  calc
    _ = ∏ i : J, ∑ p ∈ P i.val, if p ∣ E then a i.val p else 0 :=
      Fintype.prod_equiv J.equivFin.symm _ _ (fun _ => rfl)
    _ = _ := Finset.prod_coe_sort J
      (fun i : σ => ∑ p ∈ P i, if p ∣ E then a i p else 0)

/-- The square of the actual selected mark, with its two independent
copies of each unchanged original prime coefficient. -/
theorem actual_mark_square (J : Finset σ) (P : σ → Finset (Ideal (𝓞 K)))
    (hP : ∀ i ∈ J, ∀ p ∈ P i, Prime p) (a : σ → Ideal (𝓞 K) → ℂ)
    (E : Ideal (𝓞 K)) :
    ((‖divisorMark J P a E‖ ^ 2 : ℝ) : ℂ) =
      ∑ q ∈ pairedChoices (lists J P hP) E, pairedWeight (weights J a) q := by
  rw [← divisorMark_selected J P hP a E]
  exact divisorMark_norm_sq_eq_pairedChoices _ _ _

theorem actual_mark_square_le (J : Finset σ) (P : σ → Finset (Ideal (𝓞 K)))
    (hP : ∀ i ∈ J, ∀ p ∈ P i, Prime p) (a : σ → Ideal (𝓞 K) → ℂ)
    (E : Ideal (𝓞 K)) :
    ‖divisorMark J P a E‖ ^ 2 ≤
      ∑ q ∈ pairedChoices (lists J P hP) E, ‖pairedWeight (weights J a) q‖ := by
  have h := norm_sum_le (pairedChoices (lists J P hP) E) (pairedWeight (weights J a))
  rw [← actual_mark_square J P hP a E, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _)] at h
  exact h

theorem doubled_slot_cap (J I : Finset σ) (hJ : J ⊆ I) (cap : ℕ) (hcap : I.card ≤ cap) :
    J.card + J.card ≤ 2 * cap := by
  have hc := (Finset.card_le_card hJ).trans hcap
  omega

end HeckeSkeleton.Moments.MOM_INV_STEP.PrimeChoiceSlots

end
