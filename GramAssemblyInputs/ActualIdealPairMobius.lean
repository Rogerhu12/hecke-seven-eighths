import HeckeGeneral.Arithmetic.IdealMobiusMask

/-!
SOURCE CANDIDATE / not compiled. Exact two-column common-divisor Mobius
insertion on actual nonzero ideals of a Dedekind domain. A single finite
prime envelope is constructed from the actual finite outer family before
the divisor sum is interchanged. Each divisor acts on BOTH columns.
No PID, squarefreeness, or coprimality of the original columns is assumed.
The later change of variables I=d*M1, J=d*M2 is not asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Arithmetic.ActualIdealPairMobiusDraft

open IsDedekindDomain UniqueFactorizationMonoid IdealMobiusMask
open scoped Classical BigOperators nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Actual two-column divisibility, not a one-variable avoidance mask. -/
def commonIdealIndicator (D I J : Ideal R) : ℂ :=
  if D ∣ I ∧ D ∣ J then 1 else 0

def coprimeOnPrimeSet (P : Finset (HeightOneSpectrum R)) (I J : Ideal R) : ℂ :=
  if ∀ p ∈ P, ¬ (p.asIdeal ∣ I ∧ p.asIdeal ∣ J) then 1 else 0

theorem primeProduct_dvd_iff (P : Finset (HeightOneSpectrum R)) (I : Ideal R) :
    primeProduct P ∣ I ↔ ∀ p ∈ P, p.asIdeal ∣ I := by
  rw [Ideal.dvd_iff_le, primeProduct_eq_iInf]
  simp only [le_iInf_iff, ← Ideal.dvd_iff_le]

theorem commonIdealIndicator_primeProduct (P : Finset (HeightOneSpectrum R))
    (I J : Ideal R) :
    commonIdealIndicator (primeProduct P) I J =
      ∏ p ∈ P, commonIdealIndicator p.asIdeal I J := by
  have hpair : (primeProduct P ∣ I ∧ primeProduct P ∣ J) ↔
      ∀ p ∈ P, p.asIdeal ∣ I ∧ p.asIdeal ∣ J := by
    simp only [primeProduct_dvd_iff]
    constructor
    · rintro ⟨hI, hJ⟩ p hp
      exact ⟨hI p hp, hJ p hp⟩
    · intro h
      exact ⟨fun p hp => (h p hp).1, fun p hp => (h p hp).2⟩
  by_cases h : ∀ p ∈ P, p.asIdeal ∣ I ∧ p.asIdeal ∣ J
  · rw [commonIdealIndicator, if_pos (hpair.mpr h)]
    symm
    apply Finset.prod_eq_one
    intro p hp
    exact if_pos (h p hp)
  · obtain ⟨p, hp⟩ := not_forall.mp h
    have hpP : p ∈ P := by
      by_contra hn
      exact hp (fun hmem => (hn hmem).elim)
    have hpbad : ¬ (p.asIdeal ∣ I ∧ p.asIdeal ∣ J) :=
      fun hpIJ => hp (fun _ => hpIJ)
    rw [commonIdealIndicator, if_neg (fun hIJ => h (hpair.mp hIJ))]
    symm
    apply Finset.prod_eq_zero hpP
    exact if_neg hpbad

theorem coprimeOnPrimeSet_eq_product (P : Finset (HeightOneSpectrum R))
    (I J : Ideal R) :
    coprimeOnPrimeSet P I J = ∏ p ∈ P, (1 - commonIdealIndicator p.asIdeal I J) := by
  by_cases h : ∀ p ∈ P, ¬ (p.asIdeal ∣ I ∧ p.asIdeal ∣ J)
  · rw [coprimeOnPrimeSet, if_pos h]
    symm
    apply Finset.prod_eq_one
    intro p hp
    simp only [commonIdealIndicator, if_neg (h p hp), sub_zero]
  · have hp := h
    push_neg at hp
    obtain ⟨p, hpP, hpbad⟩ := hp
    rw [coprimeOnPrimeSet, if_neg h]
    symm
    apply Finset.prod_eq_zero hpP
    simp only [commonIdealIndicator, if_pos hpbad, sub_self]

/-- The actual squarefree ideal Mobius function weights simultaneous
divisibility of both original columns. Unit divisors are included. -/
theorem coprimeOnPrimeSet_mobius_expansion (P : Finset (HeightOneSpectrum R))
    (I J : Ideal R) :
    coprimeOnPrimeSet P I J = ∑ T ∈ P.powerset,
      (moebius (primeProduct T) : ℂ) * commonIdealIndicator (primeProduct T) I J := by
  rw [coprimeOnPrimeSet_eq_product]
  have h := Finset.prod_sub (fun _ : HeightOneSpectrum R => (1 : ℂ))
    (fun p => commonIdealIndicator p.asIdeal I J) P
  simpa only [Finset.prod_const_one, mul_one, moebius_primeProduct,
    Int.cast_pow, Int.cast_neg, Int.cast_one, commonIdealIndicator_primeProduct] using h

theorem ideal_isCoprime_iff_no_common_prime (I J : (Ideal R)⁰) :
    IsCoprime I.val J.val ↔
      ∀ p : HeightOneSpectrum R, ¬ (p.asIdeal ∣ I.val ∧ p.asIdeal ∣ J.val) := by
  constructor
  · intro h p hp
    have hle : I.val ⊔ J.val ≤ p.asIdeal :=
      sup_le (Ideal.dvd_iff_le.mp hp.1) (Ideal.dvd_iff_le.mp hp.2)
    rw [h.sup_eq] at hle
    exact p.isPrime.ne_top (top_le_iff.mp hle)
  · intro h
    apply Ideal.isCoprime_iff_sup_eq.mpr
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hM0 : M ≠ ⊥ := by
      intro hz
      exact (nonZeroDivisors.coe_ne_zero I)
        (le_bot_iff.mp ((le_sup_left.trans hle).trans_eq hz))
    let p : HeightOneSpectrum R := ⟨M, hM.isPrime, hM0⟩
    exact h p ⟨Ideal.dvd_iff_le.mpr (le_sup_left.trans hle),
      Ideal.dvd_iff_le.mpr (le_sup_right.trans hle)⟩

theorem mem_primeExponentSupport_iff (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    p ∈ (primeExponents I).support ↔ p.asIdeal ∣ I.val := by
  rw [Finsupp.mem_support_iff, primeExponents_apply]
  constructor
  · intro hp
    exact dvd_of_mem_normalizedFactors (Multiset.count_pos.mp (Nat.pos_of_ne_zero hp))
  · intro hp
    exact ne_of_gt (Multiset.count_pos.mpr
      ((mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero I)).mpr ⟨p.prime, hp⟩))

/-- Prime envelope from a finite actual ideal family. It is independent of
the second column and of the coefficient or frequency. -/
def finiteIdealPrimeEnvelope {ι : Type*} (A : Finset ι) (I : ι → (Ideal R)⁰) :
    Finset (HeightOneSpectrum R) := A.biUnion (fun i => (primeExponents (I i)).support)

theorem prime_mem_finiteIdealPrimeEnvelope {ι : Type*} (A : Finset ι)
    (I : ι → (Ideal R)⁰) (i : ι) (hi : i ∈ A) (p : HeightOneSpectrum R)
    (hp : p.asIdeal ∣ (I i).val) : p ∈ finiteIdealPrimeEnvelope A I := by
  exact Finset.mem_biUnion.mpr
    ⟨i, hi, (mem_primeExponentSupport_iff (I i) p).mpr hp⟩

theorem coprimeOnPrimeEnvelope_eq {ι : Type*} (A : Finset ι)
    (I : ι → (Ideal R)⁰) (i : ι) (hi : i ∈ A) (J : (Ideal R)⁰) :
    coprimeOnPrimeSet (finiteIdealPrimeEnvelope A I) (I i).val J.val =
      if IsCoprime (I i).val J.val then 1 else 0 := by
  have hiff : (∀ p ∈ finiteIdealPrimeEnvelope A I,
      ¬ (p.asIdeal ∣ (I i).val ∧ p.asIdeal ∣ J.val)) ↔ IsCoprime (I i).val J.val := by
    rw [ideal_isCoprime_iff_no_common_prime]
    constructor
    · intro h p hp
      exact h p (prime_mem_finiteIdealPrimeEnvelope A I i hi p hp.1) hp
    · intro h p _hp
      exact h p
  simp only [coprimeOnPrimeSet, hiff]

/-- Exact common-divisor insertion and finite interchange. The same actual
squarefree divisor divides both columns. No prescribed prime-envelope
coverage assumption is supplied: it was proved for this finite family. -/
theorem finite_coprime_pair_sum_mobius {ι : Type*} (A : Finset ι)
    (I J : ι → (Ideal R)⁰) (f : ι → ℂ) :
    (∑ i ∈ A, f i * (if IsCoprime (I i).val (J i).val then 1 else 0)) =
      ∑ T ∈ (finiteIdealPrimeEnvelope A I).powerset,
        (moebius (primeProduct T) : ℂ) *
          ∑ i ∈ A with primeProduct T ∣ (I i).val ∧ primeProduct T ∣ (J i).val, f i := by
  calc
    _ = ∑ i ∈ A, f i * coprimeOnPrimeSet (finiteIdealPrimeEnvelope A I)
        (I i).val (J i).val := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [coprimeOnPrimeEnvelope_eq A I i hi]
    _ = _ := by
      simp_rw [coprimeOnPrimeSet_mobius_expansion, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T _hT
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases h : primeProduct T ∣ (I i).val ∧ primeProduct T ∣ (J i).val <;>
        simp [commonIdealIndicator, h, mul_comm]

end HeckeGeneral.Arithmetic.ActualIdealPairMobiusDraft
