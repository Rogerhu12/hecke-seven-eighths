module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Gcd of products of distinct prime-ideal powers

The common factor is the product with the minimum exponent at each
actual height-one prime.  The proof extracts that factor on both sides
and proves the two residual products coprime.
-/

@[expose] public section

noncomputable section
open scoped Classical BigOperators
open IsDedekindDomain

namespace HeckeSkeleton.Moments.EngineStep

variable {R ι : Type*} [CommRing R] [IsDedekindDomain R]
variable [Fintype ι] [DecidableEq ι]

theorem prime_ideal_power_product_gcd
    (p : ι → HeightOneSpectrum R) (hp : Function.Injective p) (m n : ι → ℕ) :
    gcd (∏ i, (p i).asIdeal ^ m i) (∏ i, (p i).asIdeal ^ n i) =
      ∏ i, (p i).asIdeal ^ min (m i) (n i) := by
  let d := ∏ i, (p i).asIdeal ^ min (m i) (n i)
  let a := ∏ i, (p i).asIdeal ^ (m i - min (m i) (n i))
  let b := ∏ i, (p i).asIdeal ^ (n i - min (m i) (n i))
  have hm : (∏ i, (p i).asIdeal ^ m i) = d * a := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_add, Nat.add_sub_of_le (min_le_left _ _)]
  have hn : (∏ i, (p i).asIdeal ^ n i) = d * b := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_add, Nat.add_sub_of_le (min_le_right _ _)]
  have hcop : IsCoprime a b := by
    apply IsCoprime.prod_left
    intro i _
    apply IsCoprime.prod_right
    intro j _
    by_cases hij : i = j
    · subst j
      rcases le_total (m i) (n i) with hmn | hnm
      · rw [min_eq_left hmn, Nat.sub_self, pow_zero]
        exact isCoprime_one_left
      · rw [min_eq_right hnm, Nat.sub_self, pow_zero]
        exact isCoprime_one_right
    · exact ((p i).isCoprime_of_ne (p j) (fun he => hij (hp he))).pow
  rw [hm, hn, gcd_mul_left, normalize_eq,
    Ideal.isCoprime_iff_gcd.mp hcop, mul_one]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.prime_ideal_power_product_gcd
