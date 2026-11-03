import HeckeSkeleton.LowHybrid.ArithmeticLosses
import HeckeSkeleton.LowHybrid.CanonicalSupport
import HeckeSkeleton.LowFrozenCube.RowCoordinates

/-!
# Counting the actual frozen powerful and supported row factors

Linear ideal counting bounds a finite product region by a harmonic sum.
The canonical square-times-cube decomposition maps every powerful ideal
injectively into such a region of scale sqrt K. This gives sqrt K times a
logarithmic loss, which is sufficient for the arbitrary-epsilon ledger.
The supported squarefree factors have the exact finite powerset bound.
-/

namespace HeckeSkeleton.LowFrozenCube

open scoped BigOperators Classical
open HeckeSkeleton.LowHybrid
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates

noncomputable section

/-- The natural-norm count also controls any nonnegative real cutoff. -/
theorem card_le_real_scale_of_linear_counting
    {I : Type*} (q : I → ℕ) (normI : I → ℝ)
    (hnorm : ∀ i, normI i = (q i : ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hcount : LinearNormCounting q C) (X : ℝ) (hX : 0 ≤ X)
    (s : Finset I) (hs : ∀ i ∈ s, normI i ≤ X) :
    (s.card : ℝ) ≤ C * X := by
  have hs' : ∀ i ∈ s, q i ≤ Nat.floor X := by
    intro i hi
    apply Nat.le_floor
    simpa only [hnorm] using hs i hi
  exact (hcount (Nat.floor X) s hs').trans
    (mul_le_mul_of_nonneg_left (Nat.floor_le hX) hC)

/-- Count pairs in a multiplicative norm region by grouping over the
second component. The remaining sum is the genuine harmonic sum. -/
theorem product_pair_count_le_harmonic
    {I : Type*} (q : I → ℕ) (normI : I → ℝ)
    (hnorm : ∀ i, normI i = (q i : ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hq : ∀ i, 1 ≤ q i) (hcount : LinearNormCounting q C)
    (R : ℝ) (hR : 1 ≤ R) (pairs : Finset (I × I))
    (hpairs : ∀ u ∈ pairs, normI u.1 * normI u.2 ≤ R) :
    (pairs.card : ℝ) ≤ C * R * harmonicEnvelope C R := by
  let vs : Finset I := pairs.image Prod.snd
  let fibre (v : I) : Finset (I × I) := pairs.filter fun u => u.2 = v
  let us (v : I) : Finset I := (fibre v).image Prod.fst
  have hn : ∀ i, 1 ≤ normI i := one_le_real_norm_of_natural q normI hnorm hq
  have hpos (i : I) : 0 < normI i := lt_of_lt_of_le zero_lt_one (hn i)
  have hfcard (v : I) : (fibre v).card = (us v).card := by
    symm
    apply Finset.card_image_of_injOn
    intro u hu w hw huw
    apply Prod.ext huw
    exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hw).2.symm
  have hub (v : I) : ∀ u ∈ us v, normI u ≤ R / normI v := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    apply (le_div_iff₀ (hpos v)).mpr
    have h := hpairs u (Finset.mem_filter.mp hu).1
    simpa only [(Finset.mem_filter.mp hu).2] using h
  have hfc (v : I) : ((fibre v).card : ℝ) ≤ (C * R) * (1 / normI v) := by
    rw [hfcard v]
    calc
      ((us v).card : ℝ) ≤ C * (R / normI v) :=
        card_le_real_scale_of_linear_counting q normI hnorm C hC hcount
          (R / normI v) (div_nonneg (le_trans zero_le_one hR) (le_of_lt (hpos v)))
          (us v) (hub v)
      _ = _ := by ring
  have hvb : ∀ v ∈ vs, normI v ≤ R := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact (le_mul_of_one_le_left (le_of_lt (hpos u.2)) (hn u.1)).trans (hpairs u hu)
  have hcard : (pairs.card : ℝ) = ∑ v ∈ vs, ((fibre v).card : ℝ) := by
    dsimp only [vs, fibre]
    exact_mod_cast Finset.card_eq_sum_card_image (fun u : I × I => u.2) pairs
  calc
    (pairs.card : ℝ) = ∑ v ∈ vs, ((fibre v).card : ℝ) := hcard
    _ ≤ ∑ v ∈ vs, (C * R) * (1 / normI v) := Finset.sum_le_sum (fun v _ => hfc v)
    _ = (C * R) * ∑ v ∈ vs, 1 / normI v := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (reciprocal_sum_le_harmonicEnvelope q normI hnorm C hC hq hcount R hR vs hvb)
      (mul_nonneg hC (le_trans zero_le_one hR))

section PrimeCoordinates

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

/-- The square-times-cube coordinates are injective on any actual set of
powerful elements, by their exact reconstruction. -/
theorem powerful_pair_injOn (s : Finset A)
    (hs : ∀ a ∈ s, ∀ p, valuation coords a p = 0 ∨ 2 ≤ valuation coords a p) :
    Set.InjOn
      (fun a => (powerfulSquareFactor coords a, powerfulCubeFactor coords a)) s := by
  intro a ha b hb hab
  have hu := congrArg Prod.fst hab
  have hv := congrArg Prod.snd hab
  change powerfulSquareFactor coords a = powerfulSquareFactor coords b at hu
  change powerfulCubeFactor coords a = powerfulCubeFactor coords b at hv
  calc
    a = powerfulSquareFactor coords a ^ 2 * powerfulCubeFactor coords a ^ 3 :=
      powerful_factorization coords a (hs a ha)
    _ = powerfulSquareFactor coords b ^ 2 * powerfulCubeFactor coords b ^ 3 := by rw [hu, hv]
    _ = b := (powerful_factorization coords b (hs b hb)).symm

/-- The product of the square and cube factors has norm at most sqrt K. -/
theorem powerful_pair_norm_le_sqrt
    (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a) (a : A) (K : ℝ)
    (ha : ∀ p, valuation coords a p = 0 ∨ 2 ≤ valuation coords a p)
    (hK : normI a ≤ K) :
    normI (powerfulSquareFactor coords a) * normI (powerfulCubeFactor coords a) ≤
      Real.sqrt K := by
  have heq : normI a =
      normI (powerfulSquareFactor coords a) ^ 2 *
        normI (powerfulCubeFactor coords a) ^ 3 := by
    simpa only [map_mul, map_pow] using congrArg normI (powerful_factorization coords a ha)
  apply Real.le_sqrt_of_sq_le
  calc
    (normI (powerfulSquareFactor coords a) * normI (powerfulCubeFactor coords a)) ^ 2 =
        normI (powerfulSquareFactor coords a) ^ 2 *
          normI (powerfulCubeFactor coords a) ^ 2 := mul_pow _ _ _
    _ ≤ normI (powerfulSquareFactor coords a) ^ 2 *
        normI (powerfulCubeFactor coords a) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hn _) (by omega)) (sq_nonneg _)
    _ = normI a := heq.symm
    _ ≤ K := hK

/-- A genuine count of powerful elements. Its logarithmic factor is
absorbed by epsilon when the frozen powerful blocks are summed. -/
theorem powerful_count_le_sqrt_harmonic
    (normI : A →* ℝ) (q : A → ℕ) (hnorm : ∀ a, normI a = (q a : ℝ))
    (C : ℝ) (hC : 0 ≤ C) (hq : ∀ a, 1 ≤ q a) (hcount : LinearNormCounting q C)
    (K : ℝ) (hK : 1 ≤ K) (s : Finset A)
    (hs : ∀ a ∈ s, (∀ p, valuation coords a p = 0 ∨ 2 ≤ valuation coords a p) ∧
      normI a ≤ K) :
    (s.card : ℝ) ≤ C * Real.sqrt K * harmonicEnvelope C K := by
  let rep : A → A × A := fun a => (powerfulSquareFactor coords a, powerfulCubeFactor coords a)
  let pairs : Finset (A × A) := s.image rep
  have hn := one_le_real_norm_of_natural q normI hnorm hq
  have hrepr : Set.InjOn rep s := powerful_pair_injOn coords s (fun a ha => (hs a ha).1)
  have hcard : (pairs.card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast Finset.card_image_of_injOn hrepr
  have hbound : ∀ u ∈ pairs, normI u.1 * normI u.2 ≤ Real.sqrt K := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    exact powerful_pair_norm_le_sqrt coords normI hn a K (hs a ha).1 (hs a ha).2
  have hsqrt : 1 ≤ Real.sqrt K := Real.one_le_sqrt.mpr hK
  have hsqrtK : Real.sqrt K ≤ K := Real.sqrt_le_self_iff.mpr (Or.inr hK)
  have hH : harmonicEnvelope C (Real.sqrt K) ≤ harmonicEnvelope C K := by
    apply mul_le_mul_of_nonneg_left _ hC
    exact add_le_add (le_refl 1)
      (Real.log_le_log (lt_of_lt_of_le zero_lt_one hsqrt) hsqrtK)
  calc
    (s.card : ℝ) = (pairs.card : ℝ) := hcard.symm
    _ ≤ C * Real.sqrt K * harmonicEnvelope C (Real.sqrt K) :=
      product_pair_count_le_harmonic q normI hnorm C hC hq hcount
        (Real.sqrt K) hsqrt pairs hbound
    _ ≤ _ := mul_le_mul_of_nonneg_left hH (mul_nonneg hC (Real.sqrt_nonneg K))

/-- The powerful count adds one half of its logarithmic norm scale and
an arbitrarily small loss; its constant is uniform in the chosen set. -/
theorem powerful_count_small_power
    (normI : A →* ℝ) (q : A → ℕ) (hnorm : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hC : 0 < Ccount) (hq : ∀ a, 1 ≤ q a)
    (hcount : LinearNormCounting q Ccount) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ s : Finset A,
      (∀ a ∈ s, (∀ p, valuation coords a p = 0 ∨ 2 ≤ valuation coords a p) ∧
        normI a ≤ K) → (s.card : ℝ) ≤ C * K ^ (1 / 2 + eps) := by
  obtain ⟨CH, hCH, hb⟩ := harmonicEnvelope_subpower Ccount hC eps heps
  refine ⟨Ccount * CH, mul_pos hC hCH, ?_⟩
  intro K hK s hs
  calc
    (s.card : ℝ) ≤ Ccount * Real.sqrt K * harmonicEnvelope Ccount K :=
      powerful_count_le_sqrt_harmonic coords normI q hnorm Ccount (le_of_lt hC) hq hcount K hK s hs
    _ ≤ Ccount * Real.sqrt K * (CH * K ^ eps) :=
      mul_le_mul_of_nonneg_left (hb K hK) (mul_nonneg (le_of_lt hC) (Real.sqrt_nonneg K))
    _ = (Ccount * CH) * K ^ (1 / 2 + eps) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_add (lt_of_lt_of_le zero_lt_one hK)]
      ring

/-- Supported squarefree row factors are a subset of the powerset image,
so their number is bounded by exactly 2 to the support cardinality. -/
theorem supported_squarefree_count_le
    (support : Finset ι) (s : Finset A)
    (hs : ∀ a ∈ s, PrimeArithmetic.Squarefree coords a ∧ Supported coords support a) :
    s.card ≤ 2 ^ support.card := by
  have hsub : s ⊆ support.powerset.image (PrimeArithmetic.fromSupport coords) := by
    intro a ha
    refine Finset.mem_image.mpr ⟨PrimeArithmetic.support coords a, ?_,
      PrimeArithmetic.fromSupport_support_of_squarefree coords (hs a ha).1⟩
    apply Finset.mem_powerset.mpr
    intro p hp
    by_contra hnot
    exact Finsupp.mem_support_iff.mp hp ((hs a ha).2 p hnot)
  calc
    s.card ≤ (support.powerset.image (PrimeArithmetic.fromSupport coords)).card :=
      Finset.card_le_card hsub
    _ = 2 ^ support.card := by
      rw [Finset.card_image_of_injective _ (PrimeArithmetic.fromSupport_injective coords),
        Finset.card_powerset]

end PrimeCoordinates

#print axioms product_pair_count_le_harmonic
#print axioms powerful_pair_norm_le_sqrt
#print axioms powerful_count_le_sqrt_harmonic
#print axioms powerful_count_small_power
#print axioms supported_squarefree_count_le

end
end HeckeSkeleton.LowFrozenCube
