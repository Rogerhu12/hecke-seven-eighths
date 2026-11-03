import HeckeSkeleton.LowFrozenCube.PowerfulCounting

/-!
# Uniform counts of the actual frozen row indices

The powerful count and the supported squarefree count combine without an
energy assumption. The final theorem applies directly to the finite image
of the original rows under their two canonical frozen factors.
-/

namespace HeckeSkeleton.LowFrozenCube

open scoped BigOperators Classical
open HeckeSkeleton.LowHybrid
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates

noncomputable section

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

/-- The supported choices are actual squarefree divisors of the radical
represented by the support, so the divisor theorem controls their count. -/
theorem supported_squarefree_count_small_power
    (normI : A →* ℝ) (q : A → ℕ) (hnorm : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hq : ∀ a, 1 ≤ q a) (hcount : LinearNormCounting q Ccount)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ support : Finset ι, ∀ s : Finset A,
      (∀ a ∈ s, PrimeArithmetic.Squarefree coords a ∧ Supported coords support a) →
      (s.card : ℝ) ≤ C * normI (PrimeArithmetic.fromSupport coords support) ^ eps := by
  obtain ⟨C, hC, hb⟩ := PrimeArithmetic.divisor_count_subpower coords normI
    (one_le_real_norm_of_natural q normI hnorm hq)
    (finite_real_norms_of_linear_counting q normI hnorm Ccount hcount) eps heps
  refine ⟨C, hC, ?_⟩
  intro support s hs
  have hnat : s.card ≤
      (PrimeArithmetic.divisors coords (PrimeArithmetic.fromSupport coords support)).card := by
    rw [PrimeArithmetic.card_divisors, PrimeArithmetic.support_fromSupport]
    exact supported_squarefree_count_le coords support s hs
  exact (show (s.card : ℝ) ≤
      ((PrimeArithmetic.divisors coords (PrimeArithmetic.fromSupport coords support)).card : ℝ)
    from Nat.cast_le.mpr hnat).trans (hb _)

/-- Any actual finite collection of frozen factor pairs is controlled by
the product of its two projections. The one-half exponent is paid once. -/
theorem frozen_pair_count_small_power
    (normI : A →* ℝ) (q : A → ℕ) (hnorm : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hq : ∀ a, 1 ≤ q a)
    (hcount : LinearNormCounting q Ccount) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ support : Finset ι,
      ∀ pairs : Finset (A × A),
        (∀ u ∈ pairs,
          (∀ p, valuation coords u.1 p = 0 ∨ 2 ≤ valuation coords u.1 p) ∧
          normI u.1 ≤ K ∧ PrimeArithmetic.Squarefree coords u.2 ∧
          Supported coords support u.2) →
        (pairs.card : ℝ) ≤ C * Real.sqrt K *
          (K * normI (PrimeArithmetic.fromSupport coords support)) ^ eps := by
  obtain ⟨Cp, hCp, hpow⟩ := powerful_count_small_power coords normI q hnorm
    Ccount hCcount hq hcount eps heps
  obtain ⟨Cd, hCd, hsup⟩ := supported_squarefree_count_small_power coords normI q hnorm
    Ccount hq hcount eps heps
  refine ⟨Cp * Cd, mul_pos hCp hCd, ?_⟩
  intro K hK support pairs hpairs
  let ps : Finset A := pairs.image Prod.fst
  let ss : Finset A := pairs.image Prod.snd
  have hps : ∀ a ∈ ps,
      (∀ p, valuation coords a p = 0 ∨ 2 ≤ valuation coords a p) ∧ normI a ≤ K := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨(hpairs u hu).1, (hpairs u hu).2.1⟩
  have hss : ∀ a ∈ ss, PrimeArithmetic.Squarefree coords a ∧ Supported coords support a := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    exact (hpairs u hu).2.2
  have hsub : pairs ⊆ ps ×ˢ ss := by
    intro u hu
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst hu, Finset.mem_image_of_mem Prod.snd hu⟩
  have hcard : (pairs.card : ℝ) ≤ (ps.card : ℝ) * (ss.card : ℝ) := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_product] at h
    exact_mod_cast h
  have hn := one_le_real_norm_of_natural q normI hnorm hq
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hr0 : 0 ≤ normI (PrimeArithmetic.fromSupport coords support) :=
    le_trans zero_le_one (hn _)
  calc
    (pairs.card : ℝ) ≤ (ps.card : ℝ) * (ss.card : ℝ) := hcard
    _ ≤ (Cp * K ^ (1 / 2 + eps)) *
        (Cd * normI (PrimeArithmetic.fromSupport coords support) ^ eps) :=
      mul_le_mul (hpow K hK ps hps) (hsup support ss hss) (Nat.cast_nonneg _)
        (mul_nonneg (le_of_lt hCp) (Real.rpow_nonneg hK0 _))
    _ = (Cp * Cd) * Real.sqrt K *
        (K * normI (PrimeArithmetic.fromSupport coords support)) ^ eps := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow hK0 hr0,
        Real.rpow_add (lt_of_lt_of_le zero_lt_one hK)]
      ring

/-- The actual frozen block indices extracted from the original finite row set. -/
def frozenRowPairs (support : Finset ι) (rows : Finset A) : Finset (A × A) :=
  rows.image fun k => (powerfulRowFactor coords k, supportedRowFactor coords support k)

/-- The frozen row count used when summing a powerful-part dyad, with its
constant chosen before the dyad, support, and original rows. -/
theorem frozen_row_pair_count_small_power
    (normI : A →* ℝ) (q : A → ℕ) (hnorm : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hq : ∀ a, 1 ≤ q a)
    (hcount : LinearNormCounting q Ccount) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ support : Finset ι,
      ∀ rows : Finset A,
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ K) →
        ((frozenRowPairs coords support rows).card : ℝ) ≤ C * Real.sqrt K *
          (K * normI (PrimeArithmetic.fromSupport coords support)) ^ eps := by
  obtain ⟨C, hC, hb⟩ := frozen_pair_count_small_power coords normI q hnorm
    Ccount hCcount hq hcount eps heps
  refine ⟨C, hC, ?_⟩
  intro K hK support rows hrows
  apply hb K hK support (frozenRowPairs coords support rows)
  intro u hu
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
  exact ⟨powerfulRowFactor_powerful coords k, hrows k hk,
    supportedRowFactor_squarefree coords support k,
    supportedRowFactor_supported coords support k⟩

#print axioms supported_squarefree_count_small_power
#print axioms frozen_pair_count_small_power
#print axioms frozen_row_pair_count_small_power

end
end HeckeSkeleton.LowFrozenCube
