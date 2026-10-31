module

public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorIdeals.EulerWeights

@[expose] public section

/-!
# Powerful products from their actual prime multiplicities

These elementary ideal lemmas use the repository's `Powerful` predicate
and normalized prime factors.  They will be applied to the complete
original product after its exclusive first-transform factors vanish.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField DedekindZetaZeroFree UniqueFactorizationMonoid

namespace HeckeSkeleton.Moments.EngineStep

variable {K : Type} [Field K] [NumberField K]

theorem powerful_one : Powerful (1 : Ideal (𝓞 K)) := by
  intro p hp
  left
  change (normalizedFactors (1 : Ideal (𝓞 K))).count p = 0
  rw [normalizedFactors_one, Multiset.count_zero]

theorem powerful_mul {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hIp : Powerful I) (hJp : Powerful J) : Powerful (I * J) := by
  intro p hp
  have he : idealPrimeExponent p (I * J) =
      idealPrimeExponent p I + idealPrimeExponent p J := by
    simp only [idealPrimeExponent, normalizedFactors_mul hI hJ, Multiset.count_add]
  rw [he]
  rcases hIp p hp with hi | hi <;> rcases hJp p hp with hj | hj <;> omega

theorem powerful_pow (I : Ideal (𝓞 K)) (n : ℕ) (hn : n = 0 ∨ 2 ≤ n) :
    Powerful (I ^ n) := by
  rcases hn with rfl | hn
  · simpa only [pow_zero] using (powerful_one (K := K))
  intro p hp
  have he : idealPrimeExponent p (I ^ n) = n * idealPrimeExponent p I := by
    simp [idealPrimeExponent, normalizedFactors_pow]
  rw [he]
  by_cases hz : idealPrimeExponent p I = 0
  · exact Or.inl (by rw [hz, mul_zero])
  · right
    exact hn.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hz))

theorem powerful_finset_prod {ι : Type*} (S : Finset ι) (I : ι → Ideal (𝓞 K))
    (hI : ∀ i ∈ S, I i ≠ 0) (hIp : ∀ i ∈ S, Powerful (I i)) :
    Powerful (∏ i ∈ S, I i) := by
  induction S using Finset.induction_on with
  | empty => simpa using (powerful_one (K := K))
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    apply powerful_mul (hI i (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun j hj => hI j (Finset.mem_insert_of_mem hj)))
      (hIp i (Finset.mem_insert_self _ _))
    exact ih (fun j hj => hI j (Finset.mem_insert_of_mem hj))
      (fun j hj => hIp j (Finset.mem_insert_of_mem hj))

theorem powerful_finset_prime_powers {ι : Type*} (S : Finset ι)
    (p : ι → Ideal (𝓞 K)) (n : ι → ℕ)
    (hp : ∀ i ∈ S, p i ≠ 0) (hn : ∀ i ∈ S, n i = 0 ∨ 2 ≤ n i) :
    Powerful (∏ i ∈ S, p i ^ n i) :=
  powerful_finset_prod S _ (fun i hi => pow_ne_zero _ (hp i hi))
    (fun i hi => powerful_pow (p i) (n i) (hn i hi))

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.powerful_finset_prime_powers
