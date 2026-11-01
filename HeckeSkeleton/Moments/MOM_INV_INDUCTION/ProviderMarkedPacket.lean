import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMass

/-!
# The literal original slot packet and all of its overlap restrictions

This record contains only the original finite lists, coefficients and
norm windows.  Every common tuple, residual mark and counting statement
below is derived from those lists; it carries no energy premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedPacket

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP AssignedMarkSource
open ProviderMarkedSlots ProviderMarkedReindex ProviderMarkedTupleSplit
  ProviderMarkedWindows ProviderMarkedAnnuli ProviderNodes
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

structure Slots (S : Finset (HeightOneSpectrum (𝓞 K))) (slotCap : ℕ) (Z z : ℝ) where
  count : ℕ
  lists : Fin count → Finset (HeightOneSpectrum (𝓞 K))
  weight : Fin count → Ideal (𝓞 K) → ℂ
  length : Fin count → ℝ
  count_le : count ≤ slotCap
  length_nonneg : ∀ i, 0 ≤ length i
  length_sum : (∑ i, length i) = z
  disjoint : Pairwise (Disjoint on lists)
  exterior : ∀ i p, p ∈ lists i → p ∉ (S : Set (HeightOneSpectrum (𝓞 K)))
  window : ∀ i p, p ∈ lists i →
    (1 / 2) * Z ^ length i ≤ ProviderMarkedPools.norm p.asIdeal ∧
      ProviderMarkedPools.norm p.asIdeal ≤ 2 * Z ^ length i
  weight_le : ∀ i p, p ∈ lists i → ‖weight i p.asIdeal‖ ≤ 1

variable {K} {S : Finset (HeightOneSpectrum (𝓞 K))} {slotCap : ℕ} {Z z : ℝ}

namespace Slots

variable (s : Slots K S slotCap Z z)

def commonLength (J : Finset (Fin s.count)) : ℝ := ∑ i ∈ J, s.length i
def commonTuples (J : Finset (Fin s.count)) := tuples (restrictedLists J s.lists)
def residualLists (J : Finset (Fin s.count)) := restrictedLists (remaining J) s.lists
def residualWeight (J : Finset (Fin s.count)) := fun i => s.weight (slot (remaining J) i)
def residualLength (J : Finset (Fin s.count)) := fun i => s.length (slot (remaining J) i)

theorem commonLength_nonneg (J : Finset (Fin s.count)) : 0 ≤ s.commonLength J :=
  Finset.sum_nonneg (fun i _ => s.length_nonneg i)

theorem commonLength_le (J : Finset (Fin s.count)) : s.commonLength J ≤ z := by
  calc
    s.commonLength J ≤ ∑ i, s.length i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
        (fun i _ _ => s.length_nonneg i)
    _ = z := s.length_sum

theorem subset_card (J : Finset (Fin s.count)) : J.card ≤ slotCap := by
  have h : J.card ≤ s.count := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ J
  exact h.trans s.count_le

theorem residual_sum (J : Finset (Fin s.count)) :
    (∑ i, s.residualLength J i) = z - s.commonLength J := by
  rw [residualLength, remaining_sum, s.length_sum]
  rfl

theorem residual_disjoint (J : Finset (Fin s.count)) :
    Pairwise (Disjoint on s.residualLists J) :=
  restrictedLists_disjoint (remaining J) s.lists s.disjoint

theorem common_squarefree (J : Finset (Fin s.count))
    (q : Fin J.card → HeightOneSpectrum (𝓞 K)) (hq : q ∈ s.commonTuples J) :
    Squarefree (primeProduct Finset.univ q) :=
  tuple_product_squarefree (restrictedLists J s.lists)
    (restrictedLists_disjoint J s.lists s.disjoint) q hq

theorem residual_squarefree (J : Finset (Fin s.count))
    (p : Fin (remaining J).card → HeightOneSpectrum (𝓞 K)) (hp : p ∈ tuples (s.residualLists J)) :
    Squarefree (primeProduct Finset.univ p) :=
  tuple_product_squarefree (s.residualLists J) (s.residual_disjoint J) p hp

theorem common_weight_norm (J : Finset (Fin s.count))
    (q : Fin J.card → HeightOneSpectrum (𝓞 K)) (hq : q ∈ s.commonTuples J) :
    ‖choiceWeight (fun i => s.weight (slot J i)) q‖ ≤ 1 := by
  rw [choiceWeight, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ =>
    s.weight_le (slot J i) (q i) (Fintype.mem_piFinset.mp hq i))

theorem common_window (hZ : 0 < Z) (J : Finset (Fin s.count))
    (q : Fin J.card → HeightOneSpectrum (𝓞 K)) (hq : q ∈ s.commonTuples J) :
    ((2 : ℝ) ^ slotCap)⁻¹ ≤
        ProviderMarkedPools.norm (primeProduct Finset.univ q) / Z ^ s.commonLength J ∧
      ProviderMarkedPools.norm (primeProduct Finset.univ q) / Z ^ s.commonLength J ≤
        (2 : ℝ) ^ slotCap := by
  have h := product_window slotCap (s.subset_card J) (restrictedLists J s.lists)
    (fun i => s.length (slot J i)) Z hZ
    (fun i p hp => s.window (slot J i) p hp) q hq
  simpa only [restriction_sum, commonLength] using h

theorem residual_window (hZ : 0 < Z) (J : Finset (Fin s.count))
    (p : Fin (remaining J).card → HeightOneSpectrum (𝓞 K)) (hp : p ∈ tuples (s.residualLists J)) :
    ((2 : ℝ) ^ slotCap)⁻¹ ≤
        ProviderMarkedPools.norm (primeProduct Finset.univ p) / Z ^ (z - s.commonLength J) ∧
      ProviderMarkedPools.norm (primeProduct Finset.univ p) / Z ^ (z - s.commonLength J) ≤
        (2 : ℝ) ^ slotCap := by
  have h := product_window slotCap (s.subset_card (remaining J)) (s.residualLists J)
    (s.residualLength J) Z hZ
    (fun i p hp => s.window (slot (remaining J) i) p hp) p hp
  simpa only [s.residual_sum J] using h

theorem residual_marks (J : Finset (Fin s.count)) (t : ℝ) :
    MarkConditions K S slotCap Z (z - s.commonLength J) (1 / 2) 2 Finset.univ
      (fun i => (s.residualLists J i).image HeightOneSpectrum.asIdeal)
      (ProviderMarkedMellin.primeWeight (s.residualWeight J) t) (s.residualLength J) := by
  exact marks S slotCap Z (z - s.commonLength J) (s.residualLists J) (s.residualWeight J)
    (s.residualLength J) (s.subset_card (remaining J))
    (fun i => s.length_nonneg (slot (remaining J) i)) (s.residual_sum J).le
    (fun i p hp => s.exterior (slot (remaining J) i) p hp)
    (fun i p hp => s.window (slot (remaining J) i) p hp)
    (fun i p hp => s.weight_le (slot (remaining J) i) p hp) (s.residual_disjoint J) t

theorem common_norm_le (hZ : 0 < Z) (J : Finset (Fin s.count))
    (q : Fin J.card → HeightOneSpectrum (𝓞 K)) (hq : q ∈ s.commonTuples J) :
    ProviderMarkedPools.norm (primeProduct Finset.univ q) ≤
      supportConstant slotCap * Z ^ s.commonLength J := by
  have h := (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (s.common_window hZ J q hq).2
  exact h.trans (mul_le_mul_of_nonneg_right (productConstant_le_support slotCap)
    (Real.rpow_nonneg hZ.le _))

theorem common_coprime (J : Finset (Fin s.count))
    (q : Fin J.card → HeightOneSpectrum (𝓞 K)) (hq : q ∈ s.commonTuples J)
    (p : Fin (remaining J).card → HeightOneSpectrum (𝓞 K)) (hp : p ∈ tuples (s.residualLists J)) :
    IsCoprime (primeProduct Finset.univ q) (primeProduct Finset.univ p) :=
  selected_remaining_coprime J s.lists s.disjoint q p hq hp

end Slots

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedPacket

end
