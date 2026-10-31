import HeckeSkeleton.LowEnergy.InactiveCore
import HeckeSkeleton.LowEnergy.WindowTuples
import HeckeSkeleton.LowEnergy.ActualFrozenCharges
import HeckeGeneral.Analysis.FrequencyRowCounting
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Product-form marked coefficients with repeated primes

Slots may have overlapping windows and may select the same prime.  The
reflection prefactor is taken once for each prime in the actual support.
We aggregate tuples by that support before estimating their mass.  The
finite fibre multiplicity depends only on the maximum number of slots;
the sum over all supports is bounded by an elementary Euler product.

The final constant is chosen before the exterior-prime set, slot type,
windows, dyadic scales, coefficient bound and support restrictions.  The
only arithmetic input is the proved linear count of actual ideals.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralInactiveMass

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.LowEnergy.ActualFrozenCharges
open scoped Classical BigOperators NumberField

/-- A harmless uniform bound which also handles the empty slot type. -/
def fibreBound (rmax : ℕ) : ℝ := (rmax + 1 : ℝ) ^ rmax

theorem fibreBound_one_le (rmax : ℕ) : 1 ≤ fibreBound rmax := by
  change 1 ≤ (rmax + 1 : ℝ) ^ rmax
  exact one_le_pow₀ (by have h : (0 : ℝ) ≤ rmax := Nat.cast_nonneg rmax; linarith)

section FiniteTuples

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

def tupleSupport (p : ι → α) : Finset α := Finset.univ.image p

def slotProduct (a : ι → α → ℂ) (p : ι → α) : ℂ := ∏ i, a i (p i)

/-- All repeated occurrences of an active prime are selected together. -/
def activeSlots (p : ι → α) (Q : Finset α) : Finset ι :=
  Finset.univ.filter (fun i => p i ∈ Q)

theorem activeSlots_image (p : ι → α) (Q : Finset α)
    (hQ : Q ⊆ tupleSupport p) : (activeSlots p Q).image p = Q := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hi).2
  · intro hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hQ hq)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hi.symm ▸ hq⟩, hi⟩

theorem inactiveSlots_image (p : ι → α) (Q : Finset α) :
    (Finset.univ \ activeSlots p Q).image p = tupleSupport p \ Q := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem p (Finset.mem_univ i), ?_⟩
    intro hQ
    exact (Finset.mem_sdiff.mp hi).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩)
  · intro hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hq).1
    refine Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, hi⟩
    intro hmem
    exact (Finset.mem_sdiff.mp hq).2 (hi ▸ (Finset.mem_filter.mp hmem).2)

theorem active_inactive_support_disjoint (p : ι → α) (Q : Finset α)
    (hQ : Q ⊆ tupleSupport p) :
    Disjoint ((activeSlots p Q).image p)
      ((Finset.univ \ activeSlots p Q).image p) := by
  rw [activeSlots_image p Q hQ, inactiveSlots_image]
  exact disjoint_sdiff_self_right

theorem activeSlots_unique (p : ι → α) (I : Finset ι)
    (hdisjoint : Disjoint (I.image p) ((Finset.univ \ I).image p)) :
    activeSlots p (I.image p) = I := by
  ext i
  constructor
  · intro hi
    by_contra hnot
    exact Finset.disjoint_left.mp hdisjoint (Finset.mem_filter.mp hi).2
      (Finset.mem_image_of_mem p (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩))
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image_of_mem p hi⟩

theorem tupleSupport_restrict (p : ι → α) (I : Finset ι) :
    tupleSupport (fun i : I => p i) = I.image p := by
  ext q
  simp only [tupleSupport, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, i.property, hi⟩
  · rintro ⟨i, hi, hq⟩
    exact ⟨⟨i, hi⟩, hq⟩

theorem forall_tupleSupport_iff (p : ι → α) (P : α → Prop) :
    (∀ q ∈ tupleSupport p, P q) ↔ ∀ i, P (p i) := by
  simp [tupleSupport]

/-- Product-form whole-index marks only test the distinct support. -/
theorem slotProduct_support_mask (a : ι → α → ℂ) (p : ι → α)
    (P : α → Prop) [DecidablePred P] :
    (∏ i, if P (p i) then a i (p i) else 0) =
      slotProduct a p * (if ∀ q ∈ tupleSupport p, P q then 1 else 0) := by
  by_cases hall : ∀ i, P (p i)
  · rw [if_pos ((forall_tupleSupport_iff p P).mpr hall), mul_one]
    simp only [hall, if_true, slotProduct]
  · have hs : ¬∀ q ∈ tupleSupport p, P q :=
      fun h => hall ((forall_tupleSupport_iff p P).mp h)
    rw [if_neg hs, mul_zero]
    obtain ⟨i, hi⟩ := not_forall.mp hall
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem sum_slotProduct_support_mask (W : ι → Finset α) (a : ι → α → ℂ)
    (P : α → Prop) [DecidablePred P] :
    (∑ p ∈ Fintype.piFinset W,
      slotProduct a p * (if ∀ q ∈ tupleSupport p, P q then 1 else 0)) =
      ∏ i, ∑ q ∈ W i, if P q then a i q else 0 := by
  calc
    _ = ∑ p ∈ Fintype.piFinset W, ∏ i, if P (p i) then a i (p i) else 0 :=
      Finset.sum_congr rfl (fun p _ => (slotProduct_support_mask a p P).symm)
    _ = _ := (Finset.prod_univ_sum W (fun i q => if P q then a i q else 0)).symm

/-- The coefficient is the sum of all tuples with this support. -/
def aggregateCoefficient (s : Finset (ι → α)) (a : ι → α → ℂ)
    (Q : Finset α) : ℂ :=
  ∑ p ∈ s.filter (fun p => tupleSupport p = Q), slotProduct a p

theorem support_card_le (p : ι → α) : (tupleSupport p).card ≤ Fintype.card ι := by
  simpa only [tupleSupport, Finset.card_univ] using
    (Finset.card_image_le (s := (Finset.univ : Finset ι)) (f := p))

/-- Every fibre embeds into all functions from the slots to its support.
No injectivity of the tuple or disjointness of windows is asserted. -/
theorem support_fibre_card_le (rmax : ℕ) (hslots : Fintype.card ι ≤ rmax)
    (s : Finset (ι → α)) (Q : Finset α) :
    (s.filter (fun p => tupleSupport p = Q)).card ≤ (rmax + 1) ^ rmax := by
  by_cases hne : (s.filter (fun p => tupleSupport p = Q)).Nonempty
  · obtain ⟨p, hp⟩ := hne
    have hQ : Q.card ≤ rmax := by
      rw [← (Finset.mem_filter.mp hp).2]
      exact (support_card_le p).trans hslots
    have hsub : s.filter (fun p => tupleSupport p = Q) ⊆
        Fintype.piFinset (fun _ : ι => Q) := by
      intro p hp
      apply Fintype.mem_piFinset.mpr
      intro i
      rw [← (Finset.mem_filter.mp hp).2]
      exact Finset.mem_image_of_mem p (Finset.mem_univ i)
    calc
      _ ≤ (Fintype.piFinset (fun _ : ι => Q)).card := Finset.card_le_card hsub
      _ = Q.card ^ Fintype.card ι := by simp
      _ ≤ (rmax + 1) ^ Fintype.card ι := pow_le_pow_left' (by omega) _
      _ ≤ (rmax + 1) ^ rmax := pow_le_pow_right' (by omega) hslots
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

theorem support_fibre_card_real_le (rmax : ℕ) (hslots : Fintype.card ι ≤ rmax)
    (s : Finset (ι → α)) (Q : Finset α) :
    ((s.filter (fun p => tupleSupport p = Q)).card : ℝ) ≤ fibreBound rmax := by
  dsimp [fibreBound]
  exact_mod_cast support_fibre_card_le rmax hslots s Q

theorem slotProduct_norm_le (rmax : ℕ) (hslots : Fintype.card ι ≤ rmax)
    (a : ι → α → ℂ) (p : ι → α) {A : ℝ} (hA : 1 ≤ A)
    (ha : ∀ i, ‖a i (p i)‖ ≤ A) : ‖slotProduct a p‖ ≤ A ^ rmax := by
  calc
    _ = ∏ i, ‖a i (p i)‖ := by rw [slotProduct, norm_prod]
    _ ≤ ∏ _i : ι, A :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => ha i)
    _ = A ^ Fintype.card ι := by simp
    _ ≤ A ^ rmax := pow_le_pow_right₀ hA hslots

theorem aggregateCoefficient_norm_le (rmax : ℕ) (hslots : Fintype.card ι ≤ rmax)
    (s : Finset (ι → α)) (a : ι → α → ℂ) {A : ℝ} (hA : 1 ≤ A)
    (ha : ∀ p ∈ s, ∀ i, ‖a i (p i)‖ ≤ A) (Q : Finset α) :
    ‖aggregateCoefficient s a Q‖ ≤ fibreBound rmax * A ^ rmax := by
  calc
    _ ≤ ∑ p ∈ s.filter (fun p => tupleSupport p = Q), ‖slotProduct a p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ s.filter (fun p => tupleSupport p = Q), A ^ rmax :=
      Finset.sum_le_sum (fun p hp =>
        slotProduct_norm_le rmax hslots a p hA (ha p (Finset.mem_filter.mp hp).1))
    _ = ((s.filter (fun p => tupleSupport p = Q)).card : ℝ) * A ^ rmax := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ fibreBound rmax * A ^ rmax :=
      mul_le_mul_of_nonneg_right (support_fibre_card_real_le rmax hslots s Q)
        (pow_nonneg (zero_le_one.trans hA) _)

/-- Finite regrouping is exact before applying a norm. -/
theorem sum_aggregateCoefficient (s : Finset (ι → α)) (a : ι → α → ℂ)
    (kernel : Finset α → ℂ) :
    (∑ p ∈ s, slotProduct a p * kernel (tupleSupport p)) =
      ∑ Q ∈ s.image tupleSupport, aggregateCoefficient s a Q * kernel Q := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := s) (t := s.image tupleSupport) (g := tupleSupport)
    (fun p hp => Finset.mem_image_of_mem tupleSupport hp)
    (fun p => slotProduct a p * kernel (tupleSupport p))]
  apply Finset.sum_congr rfl
  intro Q _
  rw [aggregateCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem sum_biUnion_le (W : ι → Finset α) (w : α → ℝ) (hw : ∀ q, 0 ≤ w q) :
    (∑ q ∈ Finset.univ.biUnion W, w q) ≤ ∑ i, ∑ q ∈ W i, w q := by
  have h (t : Finset ι) : (∑ q ∈ t.biUnion W, w q) ≤ ∑ i ∈ t, ∑ q ∈ W i, w q := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      have hu := Finset.sum_union_inter (s₁ := W i) (s₂ := t.biUnion W) (f := w)
      have hnon : 0 ≤ ∑ q ∈ W i ∩ t.biUnion W, w q :=
        Finset.sum_nonneg (fun q _ => hw q)
      linarith
  exact h Finset.univ

theorem sum_support_weights_le_exp (U : Finset α) (w : α → ℝ)
    (hw : ∀ q, 0 ≤ w q) :
    (∑ Q ∈ U.powerset, ∏ q ∈ Q, w q) ≤ Real.exp (∑ q ∈ U, w q) := by
  rw [← Finset.prod_one_add, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro q _
    exact add_nonneg zero_le_one (hw q)
  · intro q _
    simpa only [add_comm] using Real.add_one_le_exp (w q)

/-- The distinct-prime weight is estimated after grouping by the support.
In particular a repeated prime is charged only once. -/
theorem support_tuple_mass_le (rmax : ℕ) (hslots : Fintype.card ι ≤ rmax)
    (s : Finset (ι → α)) (U : Finset α)
    (hsupport : ∀ p ∈ s, tupleSupport p ⊆ U)
    (w : α → ℝ) (hw : ∀ q, 0 ≤ w q) :
    (∑ p ∈ s, ∏ q ∈ tupleSupport p, w q) ≤
      fibreBound rmax * Real.exp (∑ q ∈ U, w q) := by
  have hweight (Q : Finset α) : 0 ≤ ∏ q ∈ Q, w q :=
    Finset.prod_nonneg (fun q _ => hw q)
  have hsub : s.image tupleSupport ⊆ U.powerset := by
    intro Q hQ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hQ
    exact Finset.mem_powerset.mpr (hsupport p hp)
  calc
    _ = ∑ Q ∈ s.image tupleSupport,
        ((s.filter (fun p => tupleSupport p = Q)).card : ℝ) * ∏ q ∈ Q, w q := by
      symm
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        (Finset.sum_fiberwise_of_maps_to'
          (s := s) (t := s.image tupleSupport) (g := tupleSupport)
          (fun p hp => Finset.mem_image_of_mem tupleSupport hp)
          (fun Q => ∏ q ∈ Q, w q))
    _ ≤ ∑ Q ∈ s.image tupleSupport, fibreBound rmax * ∏ q ∈ Q, w q :=
      Finset.sum_le_sum (fun Q _ => mul_le_mul_of_nonneg_right
        (support_fibre_card_real_le rmax hslots s Q) (hweight Q))
    _ = fibreBound rmax * ∑ Q ∈ s.image tupleSupport, ∏ q ∈ Q, w q :=
      (Finset.mul_sum ..).symm
    _ ≤ fibreBound rmax * ∑ Q ∈ U.powerset, ∏ q ∈ Q, w q :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun Q _ _ => hweight Q))
        (zero_le_one.trans (fibreBound_one_le rmax))
    _ ≤ fibreBound rmax * Real.exp (∑ q ∈ U, w q) :=
      mul_le_mul_of_nonneg_left (sum_support_weights_le_exp U w hw)
        (zero_le_one.trans (fibreBound_one_le rmax))

end FiniteTuples

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def primeInverseNorm (p : ExteriorPrime K S) : ℝ := (p.val.asIdeal.absNorm : ℝ)⁻¹

theorem primeInverseNorm_nonneg (p : ExteriorPrime K S) : 0 ≤ primeInverseNorm K S p :=
  inv_nonneg.mpr (Nat.cast_nonneg _)

/-- This is the literal reflection prefactor, indexed by distinct primes. -/
def distinctPrefactor (Q : Finset (ExteriorPrime K S)) : ℂ :=
  ∏ q ∈ Q, (q.val.asIdeal.absNorm : ℂ)⁻¹

theorem distinctPrefactor_norm (Q : Finset (ExteriorPrime K S)) :
    ‖distinctPrefactor K S Q‖ = ∏ q ∈ Q, primeInverseNorm K S q := by
  simp only [distinctPrefactor, norm_prod, norm_inv, RCLike.norm_natCast, primeInverseNorm]

theorem distinctPrefactor_norm_eq_ideal (Q : Finset (ExteriorPrime K S)) :
    ‖distinctPrefactor K S Q‖ = (exteriorNorm K S (primeSetIdeal K S Q))⁻¹ := by
  rw [distinctPrefactor_norm, primeSetIdeal_norm]
  simp only [primeInverseNorm, Finset.prod_inv_distrib]

section ArithmeticTuples

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def inactiveCoefficient (a : ι → ExteriorPrime K S → ℂ)
    (p : ι → ExteriorPrime K S) : ℂ :=
  slotProduct a p * distinctPrefactor K S (tupleSupport p)

def activeIdeal (p : ι → ExteriorPrime K S) : ExteriorIdeal K S :=
  primeSetIdeal K S (tupleSupport p)

/-- Exact push-forward of any finite tuple coefficient to its actual ideal. -/
def idealFiberCoefficient (s : Finset (ι → ExteriorPrime K S))
    (coefficient : (ι → ExteriorPrime K S) → ℂ) (P : ExteriorIdeal K S) : ℂ :=
  ∑ p ∈ s.filter (fun p => activeIdeal K S p = P), coefficient p

theorem sum_idealFiberCoefficient (s : Finset (ι → ExteriorPrime K S))
    (coefficient : (ι → ExteriorPrime K S) → ℂ) (kernel : ExteriorIdeal K S → ℂ) :
    (∑ p ∈ s, coefficient p * kernel (activeIdeal K S p)) =
      ∑ P ∈ s.image (activeIdeal K S), idealFiberCoefficient K S s coefficient P * kernel P := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := s) (t := s.image (activeIdeal K S)) (g := activeIdeal K S)
    (fun p hp => Finset.mem_image_of_mem (activeIdeal K S) hp)
    (fun p => coefficient p * kernel (activeIdeal K S p))]
  apply Finset.sum_congr rfl
  intro P _
  rw [idealFiberCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

def activeCoefficient (s : Finset (ι → ExteriorPrime K S))
    (a : ι → ExteriorPrime K S → ℂ) (P : ExteriorIdeal K S) : ℂ :=
  ∑ p ∈ s.filter (fun p => activeIdeal K S p = P), slotProduct a p

theorem activeCoefficient_primeSetIdeal (s : Finset (ι → ExteriorPrime K S))
    (a : ι → ExteriorPrime K S → ℂ) (Q : Finset (ExteriorPrime K S)) :
    activeCoefficient K S s a (primeSetIdeal K S Q) = aggregateCoefficient s a Q := by
  simp only [activeCoefficient, aggregateCoefficient, activeIdeal,
    (WindowTuples.primeSetIdeal_injective K S).eq_iff]

theorem activeCoefficient_norm_le (rmax : ℕ) (hslots : Fintype.card ι ≤ rmax)
    (s : Finset (ι → ExteriorPrime K S)) (a : ι → ExteriorPrime K S → ℂ)
    {A : ℝ} (hA : 1 ≤ A) (ha : ∀ p ∈ s, ∀ i, ‖a i (p i)‖ ≤ A)
    (P : ExteriorIdeal K S) :
    ‖activeCoefficient K S s a P‖ ≤ fibreBound rmax * A ^ rmax := by
  by_cases hne : (s.filter (fun p => activeIdeal K S p = P)).Nonempty
  · obtain ⟨p, hp⟩ := hne
    rw [← (Finset.mem_filter.mp hp).2]
    change ‖activeCoefficient K S s a (primeSetIdeal K S (tupleSupport p))‖ ≤ _
    rw [activeCoefficient_primeSetIdeal]
    exact aggregateCoefficient_norm_le rmax hslots s a hA ha (tupleSupport p)
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [activeCoefficient, hz, Finset.sum_empty, norm_zero]
    exact mul_nonneg (zero_le_one.trans (fibreBound_one_le rmax))
      (pow_nonneg (zero_le_one.trans hA) _)

/-- Ideal aggregation sums the actual fibres, including all collisions. -/
theorem sum_activeCoefficient (s : Finset (ι → ExteriorPrime K S))
    (a : ι → ExteriorPrime K S → ℂ) (kernel : ExteriorIdeal K S → ℂ) :
    (∑ p ∈ s, slotProduct a p * kernel (activeIdeal K S p)) =
      ∑ P ∈ s.image (activeIdeal K S), activeCoefficient K S s a P * kernel P := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := s) (t := s.image (activeIdeal K S)) (g := activeIdeal K S)
    (fun p hp => Finset.mem_image_of_mem (activeIdeal K S) hp)
    (fun p => slotProduct a p * kernel (activeIdeal K S p))]
  apply Finset.sum_congr rfl
  intro P _
  rw [activeCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem inactive_mass_le_of_union_mass (rmax : ℕ) (hslots : Fintype.card ι ≤ rmax)
    (s : Finset (ι → ExteriorPrime K S)) (U : Finset (ExteriorPrime K S))
    (hsupport : ∀ p ∈ s, tupleSupport p ⊆ U)
    (a : ι → ExteriorPrime K S → ℂ) {A H : ℝ} (hA : 1 ≤ A)
    (ha : ∀ p ∈ s, ∀ i, ‖a i (p i)‖ ≤ A)
    (hU : (∑ q ∈ U, primeInverseNorm K S q) ≤ H) :
    (∑ p ∈ s, ‖inactiveCoefficient K S a p‖) ≤
      (fibreBound rmax * Real.exp H) * A ^ rmax := by
  have hw (p : ι → ExteriorPrime K S) :
      0 ≤ ∏ q ∈ tupleSupport p, primeInverseNorm K S q :=
    Finset.prod_nonneg (fun q _ => primeInverseNorm_nonneg K S q)
  calc
    _ = ∑ p ∈ s, ‖slotProduct a p‖ *
        ∏ q ∈ tupleSupport p, primeInverseNorm K S q := by
      simp only [inactiveCoefficient, norm_mul, distinctPrefactor_norm]
    _ ≤ ∑ p ∈ s, A ^ rmax * ∏ q ∈ tupleSupport p, primeInverseNorm K S q :=
      Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_right
        (slotProduct_norm_le rmax hslots a p hA (ha p hp)) (hw p))
    _ = A ^ rmax * ∑ p ∈ s, ∏ q ∈ tupleSupport p, primeInverseNorm K S q :=
      (Finset.mul_sum ..).symm
    _ ≤ A ^ rmax * (fibreBound rmax *
        Real.exp (∑ q ∈ U, primeInverseNorm K S q)) :=
      mul_le_mul_of_nonneg_left
        (support_tuple_mass_le rmax hslots s U hsupport (primeInverseNorm K S)
          (primeInverseNorm_nonneg K S)) (pow_nonneg (zero_le_one.trans hA) _)
    _ ≤ A ^ rmax * (fibreBound rmax * Real.exp H) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hU)
          (zero_le_one.trans (fibreBound_one_le rmax)))
        (pow_nonneg (zero_le_one.trans hA) _)
    _ = _ := by ring

end ArithmeticTuples

/-- Every finite prime window injects into the genuine ideal norm ball. -/
theorem window_card_le {Clin X : ℝ}
    (hcount : ∀ U : ℝ, 1 ≤ U → ((dyadicIdealSupport K (U / 2)).card : ℝ) ≤ Clin * U)
    (W : Finset (ExteriorPrime K S)) (hX : 1 ≤ X)
    (hupper : ∀ p ∈ W, (p.val.asIdeal.absNorm : ℝ) ≤ 2 * X) :
    (W.card : ℝ) ≤ Clin * (2 * X) := by
  have hc : W.card ≤ (dyadicIdealSupport K X).card := by
    apply Finset.card_le_card_of_injOn (fun p : ExteriorPrime K S =>
      (⟨p.val.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.val.ne_bot⟩ : NonzeroIdeal K))
    · intro p hp
      rw [Finset.mem_coe] at hp ⊢
      rw [mem_dyadicIdealSupport_iff K (by linarith)]
      exact hupper p hp
    · intro p _ p' _ h
      exact Subtype.ext (HeightOneSpectrum.asIdeal_injective (congrArg Subtype.val h))
  have hscale : X = 2 * X / 2 := by ring
  calc
    (W.card : ℝ) ≤ ((dyadicIdealSupport K X).card : ℝ) := by exact_mod_cast hc
    _ = ((dyadicIdealSupport K (2 * X / 2)).card : ℝ) := by rw [← hscale]
    _ ≤ Clin * (2 * X) := hcount _ (by linarith)

theorem window_inverse_mass_le {Clin X : ℝ}
    (hcount : ∀ U : ℝ, 1 ≤ U → ((dyadicIdealSupport K (U / 2)).card : ℝ) ≤ Clin * U)
    (W : Finset (ExteriorPrime K S)) (hX : 1 ≤ X)
    (hbounds : ∀ p ∈ W,
      X ≤ (p.val.asIdeal.absNorm : ℝ) ∧ (p.val.asIdeal.absNorm : ℝ) ≤ 2 * X) :
    (∑ p ∈ W, primeInverseNorm K S p) ≤ 2 * Clin := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hterm (p : ExteriorPrime K S) (hp : p ∈ W) : primeInverseNorm K S p ≤ X⁻¹ := by
    simpa only [primeInverseNorm, one_div] using
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hX0 (hbounds p hp).1)
  calc
    _ ≤ ∑ _p ∈ W, X⁻¹ := Finset.sum_le_sum (fun p hp => hterm p hp)
    _ = (W.card : ℝ) * X⁻¹ := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Clin * (2 * X)) * X⁻¹ := mul_le_mul_of_nonneg_right
      (window_card_le K S hcount W hX (fun p hp => (hbounds p hp).2))
      (inv_nonneg.mpr hX0.le)
    _ = 2 * Clin := by field_simp [hX0.ne'] <;> ring

/-- Uniform inactive L1 mass for arbitrary product-form windows, including
overlaps, repeated primes, empty slots and arbitrary extra tuple masks.
The constant precedes S, the slot type, every window and every scale. -/
theorem exists_uniform_mass_constant (rmax : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (T : Set (HeightOneSpectrum (𝓞 K))) [Fintype T]
        {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ rmax →
      ∀ (W : ι → Finset (ExteriorPrime K T)) (X : ι → ℝ),
        (∀ i, 1 ≤ X i) →
        (∀ i, ∀ p ∈ W i,
          X i ≤ (p.val.asIdeal.absNorm : ℝ) ∧ (p.val.asIdeal.absNorm : ℝ) ≤ 2 * X i) →
      ∀ (A : ℝ), 1 ≤ A → ∀ (a : ι → ExteriorPrime K T → ℂ),
        (∀ i, ∀ p ∈ W i, ‖a i p‖ ≤ A) →
      ∀ (s : Finset (ι → ExteriorPrime K T)), s ⊆ Fintype.piFinset W →
        (∑ p ∈ s, ‖inactiveCoefficient K T a p‖) ≤ C * A ^ rmax := by
  obtain ⟨Clin, hClin, hcount⟩ := dyadicIdealSupport_linear_count K
  refine ⟨fibreBound rmax * Real.exp ((rmax : ℝ) * (2 * Clin)), ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (fibreBound_one_le rmax)
      (Real.one_le_exp_iff.mpr (by positivity))
  intro T _ ι _ _ hslots W X hX hnorm A hA a ha s hs
  let U := Finset.univ.biUnion W
  have hsupport : ∀ p ∈ s, tupleSupport p ⊆ U := by
    intro p hp q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Fintype.mem_piFinset.mp (hs hp) i⟩
  have hU : (∑ q ∈ U, primeInverseNorm K T q) ≤ (rmax : ℝ) * (2 * Clin) := by
    calc
      _ ≤ ∑ i, ∑ q ∈ W i, primeInverseNorm K T q :=
        sum_biUnion_le W (primeInverseNorm K T) (primeInverseNorm_nonneg K T)
      _ ≤ ∑ _i : ι, 2 * Clin := Finset.sum_le_sum (fun i _ =>
        window_inverse_mass_le K T hcount (W i) (hX i) (hnorm i))
      _ = (Fintype.card ι : ℝ) * (2 * Clin) := by simp
      _ ≤ (rmax : ℝ) * (2 * Clin) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hslots) (by positivity)
  exact inactive_mass_le_of_union_mass K T rmax hslots s U hsupport a hA
    (fun p hp i => ha i (p i) (Fintype.mem_piFinset.mp (hs hp) i)) hU

/-- The same fixed constant retains a row-dependent phase or any other
contraction without modifying the distinct-prime prefactor. -/
theorem exists_uniform_contracted_mass_constant (rmax : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (T : Set (HeightOneSpectrum (𝓞 K))) [Fintype T]
        {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ rmax →
      ∀ (W : ι → Finset (ExteriorPrime K T)) (X : ι → ℝ),
        (∀ i, 1 ≤ X i) →
        (∀ i, ∀ p ∈ W i,
          X i ≤ (p.val.asIdeal.absNorm : ℝ) ∧ (p.val.asIdeal.absNorm : ℝ) ≤ 2 * X i) →
      ∀ (A : ℝ), 1 ≤ A → ∀ (a : ι → ExteriorPrime K T → ℂ),
        (∀ i, ∀ p ∈ W i, ‖a i p‖ ≤ A) →
      ∀ (s : Finset (ι → ExteriorPrime K T)), s ⊆ Fintype.piFinset W →
      ∀ (phase : (ι → ExteriorPrime K T) → ℂ), (∀ p ∈ s, ‖phase p‖ ≤ 1) →
        (∑ p ∈ s, ‖inactiveCoefficient K T a p * phase p‖) ≤ C * A ^ rmax := by
  obtain ⟨C, hC, hm⟩ := exists_uniform_mass_constant K rmax
  refine ⟨C, hC, ?_⟩
  intro T _ ι _ _ hslots W X hX hnorm A hA a ha s hs phase hphase
  calc
    _ ≤ ∑ p ∈ s, ‖inactiveCoefficient K T a p‖ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hphase p hp)
    _ ≤ C * A ^ rmax := hm T hslots W X hX hnorm A hA a ha s hs

#print axioms support_fibre_card_le
#print axioms activeSlots_image
#print axioms inactiveSlots_image
#print axioms activeSlots_unique
#print axioms sum_slotProduct_support_mask
#print axioms aggregateCoefficient_norm_le
#print axioms sum_aggregateCoefficient
#print axioms support_tuple_mass_le
#print axioms activeCoefficient_norm_le
#print axioms sum_idealFiberCoefficient
#print axioms sum_activeCoefficient
#print axioms exists_uniform_mass_constant
#print axioms exists_uniform_contracted_mass_constant

end HeckeSkeleton.LowEnergy.GeneralInactiveMass
