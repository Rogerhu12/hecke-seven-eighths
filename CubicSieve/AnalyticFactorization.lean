import HeckeGeneral.Analysis.GlobalThetaData
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
Actual cubic extraction of ideals, adapted from openai/math fd4aeeb2,
DirichletL/CubicSieve/Factorization.lean. The two residual parts are squarefree;
the cube part is unrestricted. All prime factors remain outside the original S.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.AnalyticFactorization
open UniqueFactorizationMonoid
open scoped Classical BigOperators

section Generic

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]

def firstPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 1), p

def secondPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 2), p

def cubePart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset, p ^ ((normalizedFactors x).count p / 3)

theorem count_mod_three (k : ℕ) :
    k = (if k % 3 = 1 then 1 else 0) +
      2 * (if k % 3 = 2 then 1 else 0) + 3 * (k / 3) := by
  have h := Nat.mod_add_div k 3
  have hlt := Nat.mod_lt k (by decide : 0 < 3)
  split_ifs <;> omega

omit [Subsingleton Mˣ] in
private theorem residual_squarefree (x : M) (r : ℕ) :
    Squarefree (∏ p ∈ (normalizedFactors x).toFinset.filter
      (fun p => (normalizedFactors x).count p % 3 = r), p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hp' : p ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hq' : q ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    apply (irreducible_of_normalized_factor p hp').isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hpq (normalizedFactors_eq_of_dvd x p hp' q hq' hd)
  · intro p hp
    exact (irreducible_of_normalized_factor p
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1)).squarefree

omit [Subsingleton Mˣ] in
theorem firstPart_squarefree (x : M) : Squarefree (firstPart x) :=
  residual_squarefree x 1

omit [Subsingleton Mˣ] in
theorem secondPart_squarefree (x : M) : Squarefree (secondPart x) :=
  residual_squarefree x 2

omit [Subsingleton Mˣ] in
theorem residual_parts_isRelPrime (x : M) : IsRelPrime (firstPart x) (secondPart x) := by
  unfold firstPart secondPart
  apply IsRelPrime.prod_left
  intro p hp
  apply IsRelPrime.prod_right
  intro q hq
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  apply (irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp'.1)).isRelPrime_iff_not_dvd.mpr
  intro hd
  have heq := normalizedFactors_eq_of_dvd x p (Multiset.mem_toFinset.mp hp'.1)
    q (Multiset.mem_toFinset.mp hq'.1) hd
  subst q
  omega

theorem cubic_factorization (x : M) (hx : x ≠ 0) :
    x = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
  have hp : (∏ p ∈ (normalizedFactors x).toFinset,
      p ^ (normalizedFactors x).count p) = x := by
    rw [← Finset.prod_multiset_count]
    exact associated_iff_eq.mp (prod_normalizedFactors hx)
  have hper (p : M) : p ^ (normalizedFactors x).count p =
      (if (normalizedFactors x).count p % 3 = 1 then p else 1) *
      (if (normalizedFactors x).count p % 3 = 2 then p else 1) ^ 2 *
      (p ^ ((normalizedFactors x).count p / 3)) ^ 3 := by
    conv_lhs => rw [count_mod_three ((normalizedFactors x).count p)]
    rw [pow_add, pow_add, Nat.mul_comm 3, pow_mul]
    split_ifs <;> simp [pow_mul]
  calc
    x = ∏ p ∈ (normalizedFactors x).toFinset,
        p ^ (normalizedFactors x).count p := hp.symm
    _ = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
      simp_rw [hper]
      simp only [Finset.prod_mul_distrib, Finset.prod_pow]
      simp only [firstPart, secondPart, cubePart, Finset.prod_filter]

theorem extraction_injective_on_nonzero :
    Set.InjOn (fun x : M => (firstPart x, secondPart x, cubePart x)) {x | x ≠ 0} := by
  intro x hx y hy h
  have h1 := congrArg (fun t : M × M × M => t.1) h
  have h2 := congrArg (fun t : M × M × M => t.2.1) h
  have h3 := congrArg (fun t : M × M × M => t.2.2) h
  dsimp only at h1 h2 h3
  rw [cubic_factorization x hx, cubic_factorization y hy, h1, h2, h3]


end Generic

section Exterior

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open scoped nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

omit [Fintype S] in
private theorem ideal_parts_ne_zero (I : ExteriorIdeal K S) :
    firstPart I.val.val ≠ 0 ∧ secondPart I.val.val ≠ 0 ∧ cubePart I.val.val ≠ 0 := by
  have hI := nonZeroDivisors.coe_ne_zero I.val
  have he := cubic_factorization I.val.val hI
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff,
    pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)] at hI
  exact ⟨hI.1.1, hI.1.2, hI.2⟩

omit [Fintype S] in
private theorem firstPart_dvd_ideal (I : ExteriorIdeal K S) : firstPart I.val.val ∣ I.val.val := by
  refine ⟨secondPart I.val.val ^ 2 * cubePart I.val.val ^ 3, ?_⟩
  simpa only [mul_assoc] using cubic_factorization I.val.val (nonZeroDivisors.coe_ne_zero I.val)

omit [Fintype S] in
private theorem secondPart_dvd_ideal (I : ExteriorIdeal K S) : secondPart I.val.val ∣ I.val.val := by
  refine ⟨firstPart I.val.val * secondPart I.val.val * cubePart I.val.val ^ 3, ?_⟩
  calc
    I.val.val = firstPart I.val.val * secondPart I.val.val ^ 2 * cubePart I.val.val ^ 3 :=
      cubic_factorization I.val.val (nonZeroDivisors.coe_ne_zero I.val)
    _ = _ := by simp only [pow_two]; ac_rfl

omit [Fintype S] in
private theorem cubePart_dvd_ideal (I : ExteriorIdeal K S) : cubePart I.val.val ∣ I.val.val := by
  refine ⟨firstPart I.val.val * secondPart I.val.val ^ 2 * cubePart I.val.val ^ 2, ?_⟩
  calc
    I.val.val = firstPart I.val.val * secondPart I.val.val ^ 2 * cubePart I.val.val ^ 3 :=
      cubic_factorization I.val.val (nonZeroDivisors.coe_ne_zero I.val)
    _ = _ := by simp only [pow_succ, pow_zero, one_mul]; ac_rfl

def exteriorFirst (I : ExteriorIdeal K S) : ExteriorIdeal K S :=
  ⟨⟨firstPart I.val.val, mem_nonZeroDivisors_of_ne_zero (ideal_parts_ne_zero K S I).1⟩,
    fun p hp => I.property p (dvd_trans hp (firstPart_dvd_ideal K S I))⟩

def exteriorSecond (I : ExteriorIdeal K S) : ExteriorIdeal K S :=
  ⟨⟨secondPart I.val.val, mem_nonZeroDivisors_of_ne_zero (ideal_parts_ne_zero K S I).2.1⟩,
    fun p hp => I.property p (dvd_trans hp (secondPart_dvd_ideal K S I))⟩

def exteriorCube (I : ExteriorIdeal K S) : ExteriorIdeal K S :=
  ⟨⟨cubePart I.val.val, mem_nonZeroDivisors_of_ne_zero (ideal_parts_ne_zero K S I).2.2⟩,
    fun p hp => I.property p (dvd_trans hp (cubePart_dvd_ideal K S I))⟩

def compose (A B C : ExteriorIdeal K S) : ExteriorIdeal K S :=
  exteriorMul K S (exteriorMul K S A (exteriorMul K S B B))
    (exteriorMul K S C (exteriorMul K S C C))

theorem exteriorFirst_squarefree (I : ExteriorIdeal K S) :
    Squarefree (exteriorFirst K S I).val.val := firstPart_squarefree _

theorem exteriorSecond_squarefree (I : ExteriorIdeal K S) :
    Squarefree (exteriorSecond K S I).val.val := secondPart_squarefree _

theorem exterior_parts_coprime (I : ExteriorIdeal K S) :
    IsCoprime (exteriorFirst K S I).val.val (exteriorSecond K S I).val.val := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hsup
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hsup
  have hu : IsUnit M := residual_parts_isRelPrime I.val.val
    (Ideal.dvd_iff_le.mpr (le_sup_left.trans hle))
    (Ideal.dvd_iff_le.mpr (le_sup_right.trans hle))
  exact hM.isPrime.ne_top (Ideal.isUnit_iff.mp hu)

theorem exterior_factorization (I : ExteriorIdeal K S) :
    compose K S (exteriorFirst K S I) (exteriorSecond K S I) (exteriorCube K S I) = I := by
  apply Subtype.ext
  apply Subtype.ext
  change (firstPart I.val.val * (secondPart I.val.val * secondPart I.val.val)) *
    (cubePart I.val.val * (cubePart I.val.val * cubePart I.val.val)) = I.val.val
  simpa only [pow_succ, pow_two, pow_one, pow_zero, one_mul, mul_one, mul_assoc] using
    (cubic_factorization I.val.val (nonZeroDivisors.coe_ne_zero I.val)).symm

theorem exterior_extraction_injective : Function.Injective
    (fun I : ExteriorIdeal K S =>
      (exteriorFirst K S I, exteriorSecond K S I, exteriorCube K S I)) := by
  intro I J h
  have he := congrArg (fun t : ExteriorIdeal K S × ExteriorIdeal K S × ExteriorIdeal K S =>
    compose K S t.1 t.2.1 t.2.2) h
  simpa only [exterior_factorization] using he

/-- Absolute ideal norms retain the exact cubic extraction scale. -/
theorem exterior_norm_factorization (I : ExteriorIdeal K S) :
    exteriorNorm K S I = exteriorNorm K S (exteriorFirst K S I) *
      exteriorNorm K S (exteriorSecond K S I) ^ 2 *
      exteriorNorm K S (exteriorCube K S I) ^ 3 := by
  have hn := congrArg Ideal.absNorm
    (cubic_factorization I.val.val (nonZeroDivisors.coe_ne_zero I.val))
  simp only [map_mul, map_pow] at hn
  change (I.val.val.absNorm : ℝ) = (Ideal.absNorm (firstPart I.val.val) : ℝ) *
    (Ideal.absNorm (secondPart I.val.val) : ℝ) ^ 2 *
    (Ideal.absNorm (cubePart I.val.val) : ℝ) ^ 3
  exact_mod_cast hn

end Exterior

end CubicSieve.AnalyticFactorization
