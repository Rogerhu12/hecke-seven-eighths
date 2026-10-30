import HeckeGeneral.Arithmetic.IdealFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Exact moving masks over actual prime ideals

A mask is first a function on actual ring elements: it need not descend to
an unrelated exterior modulus. Its inclusion-exclusion divisors are the
actual squarefree products of a finite set of height-one prime ideals.
The coefficient is Mathlib's unique-factorization Moebius function.
Only the final principal-ideal statements introduce a generator and turn
ideal membership into element divisibility.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.IdealMobiusMask

open IsDedekindDomain UniqueFactorizationMonoid
open scoped BigOperators Classical

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def primeProduct (S : Finset (HeightOneSpectrum R)) : Ideal R := ∏ p ∈ S, p.asIdeal

def membershipIndicator (I : Ideal R) (k : R) : ℂ := if k ∈ I then 1 else 0

def avoidanceMask (S : Finset (HeightOneSpectrum R)) (k : R) : ℂ :=
  if ∀ p ∈ S, k ∉ p.asIdeal then 1 else 0

theorem pairwise_coprime_primeIdeals (S : Finset (HeightOneSpectrum R)) :
    (S : Set (HeightOneSpectrum R)).Pairwise (fun p q => IsCoprime p.asIdeal q.asIdeal) := by
  intro p _ q _ hpq
  exact Ideal.isCoprime_of_isMaximal (fun h => hpq (HeightOneSpectrum.asIdeal_injective h))

theorem primeProduct_eq_iInf (S : Finset (HeightOneSpectrum R)) :
    primeProduct S = ⨅ p ∈ S, p.asIdeal :=
  Ideal.prod_eq_iInf_of_pairwise_isCoprime (pairwise_coprime_primeIdeals S)

theorem mem_primeProduct (S : Finset (HeightOneSpectrum R)) (k : R) :
    k ∈ primeProduct S ↔ ∀ p ∈ S, k ∈ p.asIdeal := by
  rw [primeProduct_eq_iInf]
  simp

theorem primeProduct_ne_bot (S : Finset (HeightOneSpectrum R)) : primeProduct S ≠ ⊥ :=
  Finset.prod_ne_zero_iff.mpr (fun p _ => p.ne_bot)

theorem normalizedFactors_primeProduct (S : Finset (HeightOneSpectrum R)) :
    normalizedFactors (primeProduct S) = S.val.map HeightOneSpectrum.asIdeal := by
  have h : ∀ I ∈ S.val.map HeightOneSpectrum.asIdeal, Prime I := by
    intro I hI
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hI
    exact p.prime
  simpa only [primeProduct, Finset.prod_map_val] using normalizedFactors_prod_of_prime h

theorem squarefree_primeProduct (S : Finset (HeightOneSpectrum R)) :
    Squarefree (primeProduct S) := by
  rw [squarefree_iff_nodup_normalizedFactors (primeProduct_ne_bot S),
    normalizedFactors_primeProduct]
  exact S.nodup.map HeightOneSpectrum.asIdeal_injective

theorem moebius_primeProduct (S : Finset (HeightOneSpectrum R)) :
    moebius (primeProduct S) = (-1 : ℤ) ^ S.card := by
  rw [(squarefree_primeProduct S).moebius_eq, factors_eq_normalizedFactors,
    normalizedFactors_primeProduct, Multiset.card_map]
  rfl

omit [IsDedekindDomain R] in
@[simp] theorem membershipIndicator_top (k : R) : membershipIndicator (⊤ : Ideal R) k = 1 := by
  simp [membershipIndicator]

theorem membershipIndicator_primeProduct (S : Finset (HeightOneSpectrum R)) (k : R) :
    membershipIndicator (primeProduct S) k = ∏ p ∈ S, membershipIndicator p.asIdeal k := by
  by_cases h : ∀ p ∈ S, k ∈ p.asIdeal
  · have hp : ∏ p ∈ S, membershipIndicator p.asIdeal k = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      simp [membershipIndicator, h p hp]
    unfold membershipIndicator
    rw [ite_eq_left ((mem_primeProduct S k).mpr h)]
    exact hp.symm
  · have hneg := h
    push Not at h
    obtain ⟨p, hpS, hp'⟩ := h
    have hprod : ∏ p ∈ S, membershipIndicator p.asIdeal k = 0 := by
      apply Finset.prod_eq_zero hpS
      simp [membershipIndicator, hp']
    unfold membershipIndicator
    rw [ite_eq_right (fun hk => hneg ((mem_primeProduct S k).mp hk))]
    exact hprod.symm

omit [IsDedekindDomain R] in
theorem avoidanceMask_eq_product (S : Finset (HeightOneSpectrum R)) (k : R) :
    avoidanceMask S k = ∏ p ∈ S, (1 - membershipIndicator p.asIdeal k) := by
  by_cases h : ∀ p ∈ S, k ∉ p.asIdeal
  · have hp : ∏ p ∈ S, (1 - membershipIndicator p.asIdeal k) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      simp [membershipIndicator, h p hp]
    unfold avoidanceMask
    rw [ite_eq_left h]
    exact hp.symm
  · have hneg := h
    push Not at h
    obtain ⟨p, hpS, hp'⟩ := h
    have hprod : ∏ p ∈ S, (1 - membershipIndicator p.asIdeal k) = 0 := by
      apply Finset.prod_eq_zero hpS
      simp [membershipIndicator, hp']
    unfold avoidanceMask
    rw [ite_eq_right hneg]
    exact hprod.symm

/-- The exact squarefree-ideal Moebius expansion of the moving mask. -/
theorem avoidanceMask_moebius_expansion (S : Finset (HeightOneSpectrum R)) (k : R) :
    avoidanceMask S k = ∑ T ∈ S.powerset,
      (moebius (primeProduct T) : ℂ) * membershipIndicator (primeProduct T) k := by
  rw [avoidanceMask_eq_product]
  have h := Finset.prod_sub (fun _ : HeightOneSpectrum R => (1 : ℂ))
    (fun p => membershipIndicator p.asIdeal k) S
  simpa only [Finset.prod_const_one, mul_one, moebius_primeProduct,
    Int.cast_pow, Int.cast_neg, Int.cast_one, membershipIndicator_primeProduct] using h

/-- The mask may be inserted in a finite sum before any change of variables. -/
theorem masked_sum_expansion {ι : Type*} (A : Finset ι) (x : ι → R) (f : ι → ℂ)
    (S : Finset (HeightOneSpectrum R)) :
    (∑ i ∈ A, f i * avoidanceMask S (x i)) =
      ∑ T ∈ S.powerset, (moebius (primeProduct T) : ℂ) *
        ∑ i ∈ A with x i ∈ primeProduct T, f i := by
  simp_rw [avoidanceMask_moebius_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ∈ primeProduct T <;> simp [membershipIndicator, hi, mul_comm]

omit [IsDedekindDomain R] in
theorem membershipIndicator_add (I : Ideal R) (k z : R) (hz : z ∈ I) :
    membershipIndicator I (k + z) = membershipIndicator I k := by
  have h : k + z ∈ I ↔ k ∈ I := by
    constructor
    · intro hk
      simpa using I.sub_mem hk hz
    · intro hk
      exact I.add_mem hk hz
  simp only [membershipIndicator, h]

/-- Compatibility with an additive period must be proved, not inferred from
an unrelated exterior modulus. -/
theorem avoidanceMask_add_period (S : Finset (HeightOneSpectrum R)) (k z : R)
    (hz : z ∈ primeProduct S) : avoidanceMask S (k + z) = avoidanceMask S k := by
  rw [avoidanceMask_eq_product, avoidanceMask_eq_product]
  apply Finset.prod_congr rfl
  intro p hp
  rw [membershipIndicator_add _ _ _ ((mem_primeProduct S z).mp hz p hp)]

section Principal

variable [IsPrincipalIdealRing R]

/-- In a principal ring, the chosen generator actually generates the mask divisor. -/
def maskGenerator (S : Finset (HeightOneSpectrum R)) : R :=
  Submodule.IsPrincipal.generator (primeProduct S)

theorem maskGenerator_ne_zero (S : Finset (HeightOneSpectrum R)) : maskGenerator S ≠ 0 := by
  exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).not.mp (primeProduct_ne_bot S)

omit [IsDedekindDomain R] in
theorem maskGenerator_dvd_iff (S : Finset (HeightOneSpectrum R)) (k : R) :
    maskGenerator S ∣ k ↔ k ∈ primeProduct S :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).symm

theorem avoidanceMask_generator_expansion (S : Finset (HeightOneSpectrum R)) (k : R) :
    avoidanceMask S k = ∑ T ∈ S.powerset,
      (moebius (primeProduct T) : ℂ) * (if maskGenerator T ∣ k then 1 else 0) := by
  simpa only [membershipIndicator, ← maskGenerator_dvd_iff] using
    avoidanceMask_moebius_expansion S k

end Principal

end HeckeGeneral.Arithmetic.IdealMobiusMask
