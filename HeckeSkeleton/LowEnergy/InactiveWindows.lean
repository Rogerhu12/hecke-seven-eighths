import HeckeSkeleton.LowEnergy.InactiveCore
import HeckeSkeleton.LowEnergy.SlotTuples
import HeckeSkeleton.LowEnergy.WindowTuples
import HeckeGeneral.Analysis.FrequencyRowCounting

/-!
# Actual inactive marked windows have uniformly bounded total mass

The original reciprocal norm of every inactive prime is retained.  The
linear ideal count cancels that reciprocal norm on each physical window.
All constants are selected before the scale, ray filter, selected slots,
active slots and prime tuple.  Smooth compact support supplies the weight
bound; no coefficient bound or prime counting statement is postulated.

Project adapter over the actual window and reflection definitions.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.InactiveWindows
open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.LowEnergy.TupleCore HeckeSkeleton.LowEnergy.InactiveCore
open HeckeSkeleton.LowEnergy.WindowTuples
open scoped NumberField BigOperators Classical ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def primeInverseWeight (g : PrimeWindowGeometry) (Z : ℝ)
    (i : Fin g.slots) (p : ExteriorPrime K S) : ℂ :=
  windowWeight K S g Z i p / (p.val.asIdeal.absNorm : ℂ)

theorem primeInverseWeight_norm (g : PrimeWindowGeometry) (Z : ℝ)
    (i : Fin g.slots) (p : ExteriorPrime K S) :
    ‖primeInverseWeight K S g Z i p‖ =
      ‖windowWeight K S g Z i p‖ / (p.val.asIdeal.absNorm : ℝ) := by
  simp only [primeInverseWeight, norm_div, RCLike.norm_natCast]

/-- A single constant works for every slot, scale and ray filter.
The proof uses the actual compactly supported smooth weights and the
proved linear count of genuine ideals. -/
theorem exists_window_inverse_mass_bound (g : PrimeWindowGeometry) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (T : Finset (HeckeCharacter K)) (Z : ℝ), 1 ≤ Z →
      ∀ i : Fin g.slots,
        (∑ p ∈ primeWindow K S g T Z i, ‖primeInverseWeight K S g Z i p‖) ≤ C := by
  obtain ⟨Clin, hClin, hcount⟩ := dyadicIdealSupport_linear_count K
  obtain ⟨W, hW, hweight⟩ := exists_profile_bound g
  refine ⟨max 1 (2 * Clin * W), le_max_left _ _, ?_⟩
  intro T Z hZ i
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hx : 0 < primeScale g Z := Real.rpow_pos_of_pos hZ0 _
  have hterm (p : ExteriorPrime K S) (hp : p ∈ primeWindow K S g T Z i) :
      ‖primeInverseWeight K S g Z i p‖ ≤ W / primeScale g Z := by
    have hnorm := (window_norm_bounds hZ0 hp).1
    have hnpos : 0 < (p.val.asIdeal.absNorm : ℝ) := hx.trans hnorm
    rw [primeInverseWeight_norm]
    calc
      ‖windowWeight K S g Z i p‖ / (p.val.asIdeal.absNorm : ℝ) ≤
          W / (p.val.asIdeal.absNorm : ℝ) :=
        div_le_div_of_nonneg_right (hweight i _) hnpos.le
      _ ≤ W / primeScale g Z := div_le_div_of_nonneg_left hW.le hx hnorm.le
  calc
    (∑ p ∈ primeWindow K S g T Z i, ‖primeInverseWeight K S g Z i p‖) ≤
        ∑ _p ∈ primeWindow K S g T Z i, W / primeScale g Z :=
      Finset.sum_le_sum (fun p hp => hterm p hp)
    _ = ((primeWindow K S g T Z i).card : ℝ) * (W / primeScale g Z) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Clin * (2 * primeScale g Z)) * (W / primeScale g Z) :=
      mul_le_mul_of_nonneg_right (window_card_le hZ i hcount)
        (div_nonneg hW.le hx.le)
    _ = 2 * Clin * W := by field_simp [hx.ne']; ring
    _ ≤ max 1 (2 * Clin * W) := le_max_right _ _

/-- The same physical bound works for nested selected/active subtypes.
Only injectivity of the map back to the original slots is needed, avoiding
any arbitrary multiplicity or a choice of subtype representatives. -/
theorem exists_slot_inverse_mass_bound (g : PrimeWindowGeometry) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (slot : ι → Fin g.slots), Function.Injective slot →
      ∀ (T : Finset (HeckeCharacter K)) (Z : ℝ), 1 ≤ Z →
      (∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z (slot i)),
        ‖∏ i, primeInverseWeight K S g Z (slot i) (p i)‖) ≤ M := by
  obtain ⟨C, hC, hslot⟩ := exists_window_inverse_mass_bound K S g
  refine ⟨C ^ g.slots, one_le_pow₀ hC, ?_⟩
  intro ι _ _ slot hinj T Z hZ
  calc
    _ ≤ C ^ Fintype.card ι := tuple_l1_mass_le_pow
      (fun i => primeWindow K S g T Z (slot i))
      (fun i p => primeInverseWeight K S g Z (slot i) p)
      (fun i => hslot T Z hZ (slot i))
    _ ≤ C ^ g.slots := pow_le_pow_right₀ hC (by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective slot hinj)

/-- Finite inactive assembly with a retained contraction such as the
target Hecke phase.  Constants precede all subtypes, scales and rows. -/
theorem exists_slot_inactive_energy_constant (g : PrimeWindowGeometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (slot : ι → Fin g.slots), Function.Injective slot →
      ∀ (T : Finset (HeckeCharacter K)) (Z : ℝ), 1 ≤ Z →
      ∀ (rows : Finset (Ideal (𝓞 K)))
        (phase : (ι → ExteriorPrime K S) → ℂ)
        (v : (ι → ExteriorPrime K S) → Ideal (𝓞 K) → ℂ) (E : ℝ),
      0 ≤ E →
      (∀ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z (slot i)),
        ‖phase p‖ ≤ 1) →
      (∀ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z (slot i)),
        (∑ k ∈ rows, ‖v p k‖ ^ 2) ≤ E) →
      (∑ k ∈ rows, ‖∑ p ∈ Fintype.piFinset
          (fun i => primeWindow K S g T Z (slot i)),
        ((∏ i, primeInverseWeight K S g Z (slot i) (p i)) * phase p) * v p k‖ ^ 2)
        ≤ C * E := by
  obtain ⟨M, hM, hm⟩ := exists_slot_inverse_mass_bound K S g
  refine ⟨M ^ 2, pow_pos (zero_lt_one.trans_le hM) _, ?_⟩
  intro ι _ _ slot hinj T Z hZ rows phase v E hE hphase hblock
  apply finite_weighted_energy_le_of_mass _ rows _ v hE ?_ hblock
  calc
    _ ≤ ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z (slot i)),
        ‖∏ i, primeInverseWeight K S g Z (slot i) (p i)‖ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hphase p hp)
    _ ≤ M := hm slot hinj T Z hZ

def inactiveWeight (g : PrimeWindowGeometry) (Z : ℝ)
    (I : Finset (Fin g.slots)) (p : I → ExteriorPrime K S) : ℂ :=
  ∏ i : I, primeInverseWeight K S g Z i (p i)

/-- This coefficient is exactly the physical window product times the
reflection's inactive reciprocal-prime prefactor. -/
theorem inactiveWeight_eq_weight_mul_prefactor (g : PrimeWindowGeometry)
    (Z : ℝ) (I : Finset (Fin g.slots)) (p : I → ExteriorPrime K S) :
    inactiveWeight K S g Z I p =
      (∏ i : I, windowWeight K S g Z i (p i)) *
        ∏ i : I, ((p i).val.asIdeal.absNorm : ℂ)⁻¹ := by
  simp only [inactiveWeight, primeInverseWeight, div_eq_mul_inv, Finset.prod_mul_distrib]

/-- The character factor from the literal target is carried along with
the inactive reciprocal norm. -/
def inactiveTwistedWeight (ψ : HeckeCharacter K) (g : PrimeWindowGeometry) (Z : ℝ)
    (I : Finset (Fin g.slots)) (p : I → ExteriorPrime K S) : ℂ :=
  inactiveWeight K S g Z I p *
    conj (heckeIdealCoefficient K ψ (activeIdeal K S I p).val)

theorem inactiveTwistedWeight_norm_le (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (I : Finset (Fin g.slots))
    (p : I → ExteriorPrime K S) :
    ‖inactiveTwistedWeight K S ψ g Z I p‖ ≤ ‖inactiveWeight K S g Z I p‖ := by
  rw [inactiveTwistedWeight, norm_mul, Complex.norm_conj]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_heckeIdealCoefficient_le_one K ψ _)

/-- Uniformity includes the empty inactive set, whose total mass is one. -/
theorem exists_inactive_mass_bound (g : PrimeWindowGeometry) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (T : Finset (HeckeCharacter K)) (Z : ℝ), 1 ≤ Z →
      ∀ I : Finset (Fin g.slots),
        (∑ p ∈ activeTuples K S g T Z I, ‖inactiveWeight K S g Z I p‖) ≤ M := by
  obtain ⟨C, hC, hslot⟩ := exists_window_inverse_mass_bound K S g
  refine ⟨C ^ g.slots, one_le_pow₀ hC, ?_⟩
  intro T Z hZ I
  calc
    (∑ p ∈ activeTuples K S g T Z I, ‖inactiveWeight K S g Z I p‖) ≤
        C ^ Fintype.card I :=
      tuple_l1_mass_le_pow (fun i : I => primeWindow K S g T Z i)
        (fun i : I => primeInverseWeight K S g Z i) (fun i => hslot T Z hZ i)
    _ = C ^ I.card := by simp
    _ ≤ C ^ g.slots := pow_le_pow_right₀ hC (by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ I))

/-- An arbitrary additional finite support restriction only decreases the
inactive mass.  This retains every frozen and conductor compatibility mask. -/
theorem exists_restricted_inactive_mass_bound (g : PrimeWindowGeometry) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (T : Finset (HeckeCharacter K)) (Z : ℝ), 1 ≤ Z →
      ∀ (I : Finset (Fin g.slots)) (s : Finset (I → ExteriorPrime K S)),
        s ⊆ activeTuples K S g T Z I →
        (∑ p ∈ s, ‖inactiveWeight K S g Z I p‖) ≤ M := by
  obtain ⟨M, hM, hmass⟩ := exists_inactive_mass_bound K S g
  refine ⟨M, hM, ?_⟩
  intro T Z hZ I s hs
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => norm_nonneg _)).trans
    (hmass T Z hZ I)

/-- This uniform bound includes the actual Hecke character in the target,
and any extra frozen/row compatibility restriction. -/
theorem exists_twisted_inactive_mass_bound (g : PrimeWindowGeometry) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (ψ : HeckeCharacter K) (T : Finset (HeckeCharacter K))
      (Z : ℝ), 1 ≤ Z →
      ∀ (I : Finset (Fin g.slots)) (s : Finset (I → ExteriorPrime K S)),
        s ⊆ activeTuples K S g T Z I →
        (∑ p ∈ s, ‖inactiveTwistedWeight K S ψ g Z I p‖) ≤ M := by
  obtain ⟨M, hM, hm⟩ := exists_restricted_inactive_mass_bound K S g
  refine ⟨M, hM, ?_⟩
  intro ψ T Z hZ I s hs
  exact (Finset.sum_le_sum (fun p _ =>
    inactiveTwistedWeight_norm_le K S ψ g Z I p)).trans (hm T Z hZ I s hs)

theorem primeSetIdeal_val_union (A B : Finset (ExteriorPrime K S))
    (hAB : Disjoint A B) :
    (primeSetIdeal K S (A ∪ B)).val =
      (primeSetIdeal K S A).val * (primeSetIdeal K S B).val := by
  have hd : Disjoint (A.image Subtype.val) (B.image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpB
    obtain ⟨a, ha, hap⟩ := Finset.mem_image.mp hpA
    obtain ⟨b, hb, hbp⟩ := Finset.mem_image.mp hpB
    have hab : a = b := Subtype.ext (hap.trans hbp.symm)
    subst b
    exact Finset.disjoint_left.mp hAB ha hb
  change SquarefreeAmplification.squarefreeIdeal K ((A ∪ B).image Subtype.val) = _
  rw [Finset.image_union]
  exact SquarefreeAmplification.squarefreeIdeal_union K _ _ hd

/-- Actual target character coefficients split over the active/inactive
prime products because the original physical tuple is injective. -/
theorem subset_coefficient_split (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (M A : Finset (Fin g.slots)) (hA : A ⊆ M) :
    heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p M).val =
      heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p A).val *
        heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p (M \ A)).val := by
  have hinj := window_tuple_injective hp
  have hd : Disjoint (A.image p) ((M \ A).image p) := by
    apply Finset.disjoint_left.mpr
    intro q hqA hqI
    obtain ⟨a, ha, haq⟩ := Finset.mem_image.mp hqA
    obtain ⟨i, hi, hiq⟩ := Finset.mem_image.mp hqI
    have hai : a = i := hinj (haq.trans hiq.symm)
    exact (Finset.mem_sdiff.mp hi).2 (hai ▸ ha)
  have hu : A.image p ∪ (M \ A).image p = M.image p := by
    rw [← Finset.image_union, Finset.union_sdiff_of_subset hA]
  change heckeIdealCoefficient K ψ (primeSetIdeal K S (M.image p)).val = _
  rw [← hu, primeSetIdeal_val_union K S _ _ hd, heckeIdealCoefficient_mul]

/-- Literal prime-set prefactor equals the product over inactive slots. -/
theorem inactive_prime_prefactor_eq_slots (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (M A : Finset (Fin g.slots)) :
    (∏ q ∈ M.image p \ A.image p, (q.val.asIdeal.absNorm : ℂ)⁻¹) =
      ∏ i ∈ M \ A, ((p i).val.asIdeal.absNorm : ℂ)⁻¹ := by
  have hinj := window_tuple_injective hp
  rw [← Finset.image_sdiff M A hinj]
  exact Finset.prod_image (fun i _ j _ hij => hinj hij)

/-- The precise physical coefficient after choosing the active marked
slots.  No inactive reciprocal norm is discarded before Minkowski. -/
theorem weights_prefactor_split (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (M A : Finset (Fin g.slots)) (hA : A ⊆ M) :
    (∏ i ∈ M, windowWeight K S g Z i (p i)) *
        (∏ q ∈ M.image p \ A.image p, (q.val.asIdeal.absNorm : ℂ)⁻¹) =
      (∏ i ∈ A, windowWeight K S g Z i (p i)) *
        inactiveWeight K S g Z (M \ A) (fun i => p i) := by
  rw [inactive_prime_prefactor_eq_slots K S g T Z p hp,
    inactiveWeight_eq_weight_mul_prefactor]
  simp only [Finset.prod_coe_sort]
  rw [← Finset.prod_sdiff hA (f := fun i => windowWeight K S g Z i (p i))]
  ring

/-- Complete coefficient identity for the target, including its Hecke
phase and the reflection's reciprocal inactive-prime prefactor. -/
theorem target_weights_prefactor_split (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (M A : Finset (Fin g.slots)) (hA : A ⊆ M) :
    (∏ i ∈ M, windowWeight K S g Z i (p i)) *
      conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p M).val) *
      (∏ q ∈ M.image p \ A.image p, (q.val.asIdeal.absNorm : ℂ)⁻¹) =
    activeWeight K S ψ g Z A (fun i => p i) *
      inactiveTwistedWeight K S ψ g Z (M \ A) (fun i => p i) := by
  have hw := weights_prefactor_split K S g T Z p hp M A hA
  rw [subset_coefficient_split K S ψ g T Z p hp M A hA, map_mul]
  unfold activeWeight inactiveTwistedWeight
  rw [activeIdeal_restrict, activeIdeal_restrict]
  simp only [Finset.prod_coe_sort]
  calc
    _ = ((∏ i ∈ M, windowWeight K S g Z i (p i)) *
        (∏ q ∈ M.image p \ A.image p, (q.val.asIdeal.absNorm : ℂ)⁻¹)) *
        conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p A).val) *
        conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p (M \ A)).val) := by ring
    _ = _ := by rw [hw]; ring

/-- Literal selected-coordinate restriction, active-slot sum and inactive
weighted outer sum.  The original target character and inverse-prime
prefactor are retained through the exact finite bijection. -/
theorem target_marked_slot_split (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (J A : Finset (Fin g.slots)) (hA : A ⊆ Finset.univ \ J)
    (f : (Fin g.slots → ExteriorPrime K S) → ℂ) :
    (∑ t ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
      if ∀ i ∈ J, t i = p i then
        (∏ i ∈ Finset.univ \ J, windowWeight K S g Z i (t i)) *
          conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S t (Finset.univ \ J)).val) *
          (∏ q ∈ (Finset.univ \ J).image t \ A.image t,
            (q.val.asIdeal.absNorm : ℂ)⁻¹) * f t else 0) =
    ∑ b ∈ activeTuples K S g T Z ((Finset.univ \ J) \ A),
      inactiveTwistedWeight K S ψ g Z ((Finset.univ \ J) \ A) b *
        ∑ a ∈ activeTuples K S g T Z A,
          activeWeight K S ψ g Z A a * f (SlotTuples.fill J A p a b) := by
  have hsplit := SlotTuples.sum_pi_fixed_active_split
    (fun i => primeWindow K S g T Z i) J A hA p
    (fun i _ => Fintype.mem_piFinset.mp hp i)
    (fun t => (∏ i ∈ Finset.univ \ J, windowWeight K S g Z i (t i)) *
      conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S t (Finset.univ \ J)).val) *
      (∏ q ∈ (Finset.univ \ J).image t \ A.image t,
        (q.val.asIdeal.absNorm : ℂ)⁻¹) * f t)
  refine Eq.trans ?_ (hsplit.trans ?_)
  · apply Finset.sum_congr rfl
    intro t ht
    by_cases hfix : ∀ i ∈ J, t i = p i
    · simp only [if_pos hfix]
    · simp only [if_neg hfix]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have ht := SlotTuples.fill_mem_piFinset
      (fun i => primeWindow K S g T Z i) J A hA p
      (fun i _ => Fintype.mem_piFinset.mp hp i) a b ha hb
    have hw := target_weights_prefactor_split K S ψ g T Z
      (SlotTuples.fill J A p a b) ht (Finset.univ \ J) A hA
    have ha' : (fun i : A => SlotTuples.fill J A p a b i) = a :=
      funext (SlotTuples.fill_active J A hA p a b)
    have hb' : (fun i : ↥((Finset.univ \ J) \ A) => SlotTuples.fill J A p a b i) = b :=
      funext (SlotTuples.fill_inactive J A p a b)
    rw [hw, ha', hb']
    ring

/-- Active reflection prime subsets can be reindexed by their actual
slot subsets. Disjoint physical windows make this reindexing injective. -/
theorem active_prime_subsets_eq_slot_subsets (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (M : Finset (Fin g.slots)) (f : Finset (ExteriorPrime K S) → ℂ) :
    (∑ A ∈ (M.image p).powerset, f A) = ∑ I ∈ M.powerset, f (I.image p) := by
  rw [Finset.powerset_image]
  exact Finset.sum_image (fun I _ J _ h =>
    Finset.image_injective (window_tuple_injective hp) h)

/-- This version applies directly to the surviving-slot subtype obtained
after fixing the selected coordinates.  Its active predicate is arbitrary,
so it also handles every active reflection subset before ideal aggregation. -/
theorem marked_weighted_pi_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (slot : ι → Fin g.slots) (active : ι → Prop) [DecidablePred active]
    (f : (ι → ExteriorPrime K S) → ℂ) :
    (∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z (slot i)),
      (∏ i, windowWeight K S g Z (slot i) (p i)) *
        (∏ i : {i // ¬active i}, ((p i).val.asIdeal.absNorm : ℂ)⁻¹) * f p) =
      ∑ b ∈ Fintype.piFinset
        (fun i : {i // ¬active i} => primeWindow K S g T Z (slot i)),
        (∏ i : {i // ¬active i}, primeInverseWeight K S g Z (slot i) (b i)) *
          ∑ a ∈ Fintype.piFinset
            (fun i : {i // active i} => primeWindow K S g T Z (slot i)),
            (∏ i : {i // active i}, windowWeight K S g Z (slot i) (a i)) *
              f (join active a b) := by
  simpa only [primeInverseWeight, div_eq_mul_inv] using
    weighted_sum_piFinset_split (fun i => primeWindow K S g T Z (slot i)) active
      (fun i p => windowWeight K S g Z (slot i) p)
      (fun _ p => (p.val.asIdeal.absNorm : ℂ)⁻¹) f

/-- The actual inactive tuple assembly costs a fixed geometry constant
squared.  The row set, selected slots and all inner data remain arbitrary. -/
theorem exists_inactive_energy_constant (g : PrimeWindowGeometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (HeckeCharacter K)) (Z : ℝ), 1 ≤ Z →
      ∀ (I : Finset (Fin g.slots)) (rows : Finset (Ideal (𝓞 K)))
        (v : (I → ExteriorPrime K S) → Ideal (𝓞 K) → ℂ) (E : ℝ), 0 ≤ E →
        (∀ p ∈ activeTuples K S g T Z I, (∑ k ∈ rows, ‖v p k‖ ^ 2) ≤ E) →
        (∑ k ∈ rows, ‖∑ p ∈ activeTuples K S g T Z I,
          inactiveWeight K S g Z I p * v p k‖ ^ 2) ≤ C * E := by
  obtain ⟨M, hM, hmass⟩ := exists_inactive_mass_bound K S g
  refine ⟨M ^ 2, pow_pos (zero_lt_one.trans_le hM) _, ?_⟩
  intro T Z hZ I rows v E hE hblock
  exact finite_weighted_energy_le_of_mass (activeTuples K S g T Z I) rows
    (inactiveWeight K S g Z I) v hE (hmass T Z hZ I) hblock

/-- The literal target's inactive coefficients, with their character
phase, cost only one fixed geometry constant in energy. -/
theorem exists_twisted_inactive_energy_constant (g : PrimeWindowGeometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : HeckeCharacter K) (T : Finset (HeckeCharacter K))
      (Z : ℝ), 1 ≤ Z →
      ∀ (I : Finset (Fin g.slots)) (s : Finset (I → ExteriorPrime K S))
        (rows : Finset (Ideal (𝓞 K)))
        (v : (I → ExteriorPrime K S) → Ideal (𝓞 K) → ℂ) (E : ℝ),
      s ⊆ activeTuples K S g T Z I → 0 ≤ E →
      (∀ p ∈ s, (∑ k ∈ rows, ‖v p k‖ ^ 2) ≤ E) →
      (∑ k ∈ rows, ‖∑ p ∈ s,
        inactiveTwistedWeight K S ψ g Z I p * v p k‖ ^ 2) ≤ C * E := by
  obtain ⟨M, hM, hm⟩ := exists_twisted_inactive_mass_bound K S g
  refine ⟨M ^ 2, pow_pos (zero_lt_one.trans_le hM) _, ?_⟩
  intro ψ T Z hZ I s rows v E hs hE hblock
  exact finite_weighted_energy_le_of_mass s rows
    (inactiveTwistedWeight K S ψ g Z I) v hE (hm ψ T Z hZ I s hs) hblock

#print axioms exists_window_inverse_mass_bound
#print axioms exists_inactive_mass_bound
#print axioms weights_prefactor_split
#print axioms marked_weighted_pi_split
#print axioms exists_inactive_energy_constant
#print axioms target_weights_prefactor_split
#print axioms target_marked_slot_split
#print axioms exists_twisted_inactive_energy_constant

end HeckeSkeleton.LowEnergy.InactiveWindows
