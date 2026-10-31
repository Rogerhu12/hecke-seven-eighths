import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Coefficient
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ChildTermDictionary

/-!
# Complete divisor allocation on the actual paired columns

Every prime of a squarefree divisor chooses a nonempty subset of all
factor occurrences.  Multiplying the actual inclusion-exclusion
identities gives the exact divisor filter, with the same whole complex
coefficient on every branch.  Two plain occurrences and every prime
slot use the same finite index set, including zero slots.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace HeckeSkeleton.Moments.EngineStep.WholeAllocation

open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

theorem squarefree_dvd_iff_support (D I : Ideal (𝓞 K)) (hD : Squarefree D) :
    D ∣ I ↔ ∀ p : primeSupport D, p.val ∣ I := by
  constructor
  · intro h p
    exact (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp p.property)).trans h
  · intro h
    by_cases hI : I = 0
    · simp [hI]
    · rw [← squarefree_support_product_self hD]
      apply support_product_dvd hI
      intro p hp
      exact (prime_mem_support_iff_dvd p I (support_prime hp) hI).mpr (h ⟨p, hp⟩)

theorem squarefree_indicator_product (D I : Ideal (𝓞 K)) (hD : Squarefree D) :
    divisibilityIndicator D I = ∏ p : primeSupport D, divisibilityIndicator p.val I := by
  by_cases hd : D ∣ I
  · rw [divisibilityIndicator, if_pos hd]
    symm
    apply Finset.prod_eq_one
    intro p _
    exact if_pos ((squarefree_dvd_iff_support D I hD).mp hd p)
  · rw [divisibilityIndicator, if_neg hd]
    symm
    obtain ⟨p, hp⟩ := not_forall.mp (fun h => hd ((squarefree_dvd_iff_support D I hD).mpr h))
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    exact if_neg hp

def occurrenceDivisor {k : ℕ} (D : Ideal (𝓞 K))
    (v : primeSupport D → Finset (Fin k)) (i : Fin k) : Ideal (𝓞 K) :=
  ∏ p ∈ Finset.univ.filter (fun p : primeSupport D => i ∈ v p), p.val

theorem occurrenceDivisor_dvd_iff {k : ℕ} (D : Ideal (𝓞 K))
    (v : primeSupport D → Finset (Fin k)) (i : Fin k) (I : Ideal (𝓞 K)) :
    occurrenceDivisor D v i ∣ I ↔ ∀ p, i ∈ v p → p.val ∣ I := by
  constructor
  · intro hd p hp
    exact (Finset.dvd_prod_of_mem (fun q : primeSupport D => q.val)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩)).trans hd
  · intro hd
    by_cases hI : I = 0
    · simp [hI]
    let T := (Finset.univ.filter (fun p : primeSupport D => i ∈ v p)).image Subtype.val
    have hT : T ⊆ primeSupport I := by
      intro P hP
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
      exact (prime_mem_support_iff_dvd p.val I (support_prime p.property) hI).mpr
        (hd p (Finset.mem_filter.mp hp).2)
    have he : occurrenceDivisor D v i = ∏ P ∈ T, P := by
      dsimp only [T, occurrenceDivisor]
      rw [Finset.prod_image]
      · rfl
      · intro p _ q _ hpq
        exact Subtype.ext hpq
    rw [he]
    exact support_product_dvd hI hT

theorem selected_prime_slot_eq {k : ℕ} (D : Ideal (𝓞 K))
    (v : primeSupport D → Finset (Fin k)) (i : Fin k)
    (p : primeSupport D) (r : HeightOneSpectrum (𝓞 K))
    (hi : i ∈ v p) (hd : occurrenceDivisor D v i ∣ r.asIdeal) :
    p.val = r.asIdeal := by
  exact associated_iff_eq.mp ((support_prime p.property).associated_of_dvd r.prime
    ((occurrenceDivisor_dvd_iff D v i r.asIdeal).mp hd p hi))

theorem incidence_product {k : ℕ} (D : Ideal (𝓞 K))
    (v : primeSupport D → Finset (Fin k)) (a : Fin k → Ideal (𝓞 K)) :
    (∏ p : primeSupport D, ∏ i ∈ v p, divisibilityIndicator p.val (a i)) =
      if ∀ i, occurrenceDivisor D v i ∣ a i then 1 else 0 := by
  by_cases h : ∀ i, occurrenceDivisor D v i ∣ a i
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro p _
    apply Finset.prod_eq_one
    intro i hi
    exact if_pos ((occurrenceDivisor_dvd_iff D v i (a i)).mp (h i) p hi)
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    have hn : ¬∀ p, i ∈ v p → p.val ∣ a i :=
      fun hp => hi ((occurrenceDivisor_dvd_iff D v i (a i)).mpr hp)
    obtain ⟨p, hp⟩ := not_forall.mp hn
    have hpi : i ∈ v p := by tauto
    have hpd : ¬p.val ∣ a i := by tauto
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    apply Finset.prod_eq_zero hpi
    exact if_neg hpd

theorem complete_divisor_allocation (D : Ideal (𝓞 K)) (hD : Squarefree D)
    (k : ℕ) (a : Fin k → Ideal (𝓞 K)) :
    divisibilityIndicator D (∏ i, a i) =
      ∑ v ∈ AllocationMass.idealAllocations D k,
        AllocationMass.sign (primeSupport D) v *
          (if ∀ i, occurrenceDivisor D v i ∣ a i then 1 else 0) := by
  rw [squarefree_indicator_product D _ hD]
  have hlocal (p : primeSupport D) :
      divisibilityIndicator p.val (∏ i, a i) =
        ∑ J ∈ AllocationMass.choices k,
          (-1 : ℂ) ^ (J.card + 1) * ∏ i ∈ J, divisibilityIndicator p.val (a i) :=
    divisor_allocation Finset.univ p.val (support_prime p.property) a
  simp_rw [hlocal]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.prod_mul_distrib, incidence_product]
  rfl

theorem whole_polynomial_allocation {X : Type*} (D : Ideal (𝓞 K))
    (hD : Squarefree D) (k : ℕ) (columns : Finset X)
    (a : X → Fin k → Ideal (𝓞 K)) (C : X → ℂ) :
    (∑ x ∈ columns with D ∣ ∏ i, a x i, C x) =
      ∑ v ∈ AllocationMass.idealAllocations D k, AllocationMass.sign (primeSupport D) v *
        ∑ x ∈ columns with ∀ i, occurrenceDivisor D v i ∣ a x i, C x := by
  have hterm (x : X) :
      (if D ∣ ∏ i, a x i then C x else 0) =
        ∑ v ∈ AllocationMass.idealAllocations D k, AllocationMass.sign (primeSupport D) v *
          (if ∀ i, occurrenceDivisor D v i ∣ a x i then C x else 0) := by
    have ht := congrArg (fun z : ℂ => z * C x) (complete_divisor_allocation D hD k (a x))
    simpa only [divisibilityIndicator, ite_mul, one_mul, zero_mul,
      Finset.sum_mul, mul_assoc, mul_ite, mul_one, mul_zero] using ht
  rw [Finset.sum_filter]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_filter, Finset.mul_sum]

section Paired

variable {X Y P : Type*} {k : ℕ}

def pairedOccurrences (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K))
    (A : P → Ideal (𝓞 K)) (x : (X × Y) × (Fin k → P)) : Fin (k + 2) → Ideal (𝓞 K) :=
  Fin.cons (I x.1.1) (Fin.cons (J x.1.2) (fun i => A (x.2 i)))

theorem paired_occurrences_product (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K))
    (A : P → Ideal (𝓞 K)) (x : (X × Y) × (Fin k → P)) :
    (∏ i, pairedOccurrences I J A x i) = I x.1.1 * J x.1.2 * ∏ i, A (x.2 i) := by
  simp only [pairedOccurrences, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

def pairedAllocatedColumns (D : Ideal (𝓞 K))
    (v : primeSupport D → Finset (Fin (k + 2)))
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K)) :
    Finset ((X × Y) × (Fin k → P)) :=
  childCartesianColumns
    (S₁.filter (fun x => occurrenceDivisor D v 0 ∣ I x))
    (S₂.filter (fun y => occurrenceDivisor D v (Fin.succ 0) ∣ J y))
    (fun i => (S i).filter (fun p => occurrenceDivisor D v i.succ.succ ∣ A p))

theorem paired_allocated_columns_eq_filter (D : Ideal (𝓞 K))
    (v : primeSupport D → Finset (Fin (k + 2)))
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K)) :
    pairedAllocatedColumns D v S₁ S₂ S I J A =
      (childCartesianColumns S₁ S₂ S).filter
        (fun x => ∀ i, occurrenceDivisor D v i ∣ pairedOccurrences I J A x i) := by
  ext x
  simp only [pairedAllocatedColumns, childCartesianColumns, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_filter, Fintype.mem_piFinset,
    pairedOccurrences, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  tauto

theorem whole_paired_divisor_allocation (D : Ideal (𝓞 K)) (hD : Squarefree D)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (C : (X × Y) × (Fin k → P) → ℂ) :
    (∑ x ∈ childCartesianColumns S₁ S₂ S with D ∣ I x.1.1 * J x.1.2 * ∏ i, A (x.2 i), C x) =
      ∑ v ∈ AllocationMass.idealAllocations D (k + 2), AllocationMass.sign (primeSupport D) v *
        ∑ x ∈ pairedAllocatedColumns D v S₁ S₂ S I J A, C x := by
  simpa only [paired_occurrences_product, ← paired_allocated_columns_eq_filter] using
    whole_polynomial_allocation D hD (k + 2) (childCartesianColumns S₁ S₂ S)
      (pairedOccurrences I J A) C

theorem moebius_paired_divisor_allocation (D : Ideal (𝓞 K))
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (C : (X × Y) × (Fin k → P) → ℂ) :
    (moebius D : ℂ) *
      (∑ x ∈ childCartesianColumns S₁ S₂ S with D ∣ I x.1.1 * J x.1.2 * ∏ i, A (x.2 i), C x) =
      (moebius D : ℂ) * ∑ v ∈ AllocationMass.idealAllocations D (k + 2),
        AllocationMass.sign (primeSupport D) v *
          ∑ x ∈ pairedAllocatedColumns D v S₁ S₂ S I J A, C x := by
  by_cases hD : Squarefree D
  · rw [whole_paired_divisor_allocation D hD]
  · rw [moebius_of_not_squarefree hD, Int.cast_zero, zero_mul, zero_mul]

theorem paired_columns_empty_of_double_slot (D : Ideal (𝓞 K))
    (v : primeSupport D → Finset (Fin (k + 2)))
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K))
    (i : Fin k) (p q : primeSupport D) (hpq : p ≠ q)
    (hp : i.succ.succ ∈ v p) (hq : i.succ.succ ∈ v q) :
    pairedAllocatedColumns D v S₁ S₂ S I J HeightOneSpectrum.asIdeal = ∅ := by
  ext x
  constructor
  · intro hx
    exfalso
    rw [paired_allocated_columns_eq_filter] at hx
    have hd := (Finset.mem_filter.mp hx).2 i.succ.succ
    change occurrenceDivisor D v i.succ.succ ∣ (x.2 i).asIdeal at hd
    have hpe := selected_prime_slot_eq D v i.succ.succ p (x.2 i) hp hd
    have hqe := selected_prime_slot_eq D v i.succ.succ q (x.2 i) hq hd
    exact hpq (Subtype.ext (hpe.trans hqe.symm))
  · simp

end Paired
end HeckeSkeleton.Moments.EngineStep.WholeAllocation

#print axioms HeckeSkeleton.Moments.EngineStep.WholeAllocation.complete_divisor_allocation
#print axioms HeckeSkeleton.Moments.EngineStep.WholeAllocation.whole_paired_divisor_allocation
#print axioms HeckeSkeleton.Moments.EngineStep.WholeAllocation.paired_columns_empty_of_double_slot
