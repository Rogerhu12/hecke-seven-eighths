import HeckeSkeleton.LowHybrid.ArithmeticLosses
import HeckeSkeleton.LowHybrid.CountingPositivity

/-!
# Fixed local multiplicities are uniform small-power losses

The local slicing argument can contribute any fixed nonnegative base to
the power of the number of prime factors. The same finite-small-prime
argument used for squarefree divisor counts handles that factor directly.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators Classical
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates

noncomputable section

theorem support_power_base_le_product
    {P : Type*} (q : P → ℝ) (bad s : Finset P) (base eta : ℝ)
    (hbase : 1 ≤ base) (heta : 0 ≤ eta) (hq : ∀ p, 1 ≤ q p)
    (hgood : ∀ p, p ∉ bad → base ≤ q p ^ eta) :
    base ^ s.card ≤ base ^ bad.card * ∏ p ∈ s, q p ^ eta := by
  let cost : P → ℝ := fun p => if p ∈ bad then base else 1
  have hb0 : 0 ≤ base := le_trans zero_le_one hbase
  have hpoint (p : P) : base ≤ cost p * q p ^ eta := by
    by_cases hp : p ∈ bad
    · simp only [cost, if_pos hp]
      exact le_mul_of_one_le_right hb0 (Real.one_le_rpow (hq p) heta)
    · simpa only [cost, if_neg hp, one_mul] using hgood p hp
  have hcost : (∏ p ∈ s, cost p) ≤ base ^ bad.card := by
    calc
      (∏ p ∈ s, cost p) = base ^ (s ∩ bad).card := by
        simp only [cost, Finset.prod_ite_mem, Finset.prod_const]
      _ ≤ _ := pow_le_pow_right₀ hbase (Finset.card_le_card Finset.inter_subset_right)
  have hprod0 : 0 ≤ ∏ p ∈ s, q p ^ eta :=
    Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (le_trans zero_le_one (hq p)) eta)
  calc
    base ^ s.card = ∏ _p ∈ s, base := by simp
    _ ≤ ∏ p ∈ s, cost p * q p ^ eta :=
      Finset.prod_le_prod₀ (fun _ _ => hb0) (fun p _ => hpoint p)
    _ = (∏ p ∈ s, cost p) * ∏ p ∈ s, q p ^ eta := Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_right hcost hprod0

theorem fixed_base_support_power_subpower_ge_one
    {P : Type*} (q : P → ℝ) (hq : ∀ p, 1 ≤ q p)
    (hfinite : ∀ X : ℝ, Set.Finite {p : P | q p ≤ X})
    (base : ℝ) (hbase : 1 ≤ base) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset P,
      base ^ s.card ≤ C * (∏ p ∈ s, q p) ^ eta := by
  let bad := (hfinite (base ^ (1 / eta))).toFinset
  have hb0 : 0 ≤ base := le_trans zero_le_one hbase
  have hgood (p : P) (hp : p ∉ bad) : base ≤ q p ^ eta := by
    have hbasecut : base ^ (1 / eta) ≤ q p := by
      by_contra hnot
      exact hp ((hfinite _).mem_toFinset.mpr (le_of_lt (lt_of_not_ge hnot)))
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hb0 (1 / eta)) hbasecut (le_of_lt heta)
    have heq : (base ^ (1 / eta)) ^ eta = base := by
      rw [← Real.rpow_mul hb0]
      have he : (1 / eta) * eta = 1 := by field_simp [ne_of_gt heta]
      rw [he, Real.rpow_one]
    simpa only [heq] using h
  refine ⟨base ^ bad.card, pow_pos (lt_of_lt_of_le zero_lt_one hbase) _, ?_⟩
  intro s
  have h := support_power_base_le_product q bad s base eta hbase (le_of_lt heta) hq hgood
  rw [Real.finsetProd_rpow s q (fun p _ => le_trans zero_le_one (hq p)) eta] at h
  exact h

/-- Arbitrary fixed nonnegative bases are covered by replacing the base
with max 1 base before choosing the small-prime cutoff. -/
theorem fixed_base_support_power_subpower
    {P : Type*} (q : P → ℝ) (hq : ∀ p, 1 ≤ q p)
    (hfinite : ∀ X : ℝ, Set.Finite {p : P | q p ≤ X})
    (base : ℝ) (hbase : 0 ≤ base) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset P,
      base ^ s.card ≤ C * (∏ p ∈ s, q p) ^ eta := by
  obtain ⟨C, hC, hb⟩ := fixed_base_support_power_subpower_ge_one q hq hfinite
    (max 1 base) (le_max_left _ _) eta heta
  refine ⟨C, hC, ?_⟩
  intro s
  exact (pow_le_pow_left₀ hbase (le_max_right _ _) s.card).trans (hb s)

/-- The actual fixed local multiplicity base^omega(a) is an arbitrarily
small norm power. Positivity and finite prime cutoffs are both consequences
of the single linear-counting premise and naturality of the norm. -/
theorem prime_support_power_subpower_of_counting
    {ι A : Type*} [CommMonoid A]
    (coords : A ≃* Multiplicative (ι →₀ ℕ))
    (normI : A →* ℝ) (q : A → ℕ) (hnorm : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hcount : LinearNormCounting q Ccount)
    (base : ℝ) (hbase : 0 ≤ base) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A,
      base ^ (PrimeArithmetic.support coords a).card ≤ C * normI a ^ eta := by
  have hn := one_le_real_norm_of_natural q normI hnorm
    (linear_norm_counting_norm_one_le q Ccount hcount)
  have hfinite := finite_real_norms_of_linear_counting q normI hnorm Ccount hcount
  obtain ⟨C, hC, hb⟩ := fixed_base_support_power_subpower
    (fun p => normI (primeElement coords p)) (fun p => hn _)
    (PrimeArithmetic.finite_prime_norms coords normI hfinite) base hbase eta heta
  refine ⟨C, hC, ?_⟩
  intro a
  calc
    base ^ (PrimeArithmetic.support coords a).card ≤
        C * (∏ p ∈ PrimeArithmetic.support coords a, normI (primeElement coords p)) ^ eta :=
      hb (PrimeArithmetic.support coords a)
    _ ≤ C * normI a ^ eta := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow
        (Finset.prod_nonneg (fun p _ => le_trans zero_le_one (hn _)))
        (PrimeArithmetic.prime_product_le_norm coords normI hn a) (le_of_lt heta))
      (le_of_lt hC)

#print axioms support_power_base_le_product
#print axioms fixed_base_support_power_subpower
#print axioms prime_support_power_subpower_of_counting

end
end HeckeSkeleton.LowHybrid
