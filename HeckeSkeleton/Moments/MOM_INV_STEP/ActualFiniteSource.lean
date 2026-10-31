import HeckeSkeleton.Moments.MOM_INV_STEP.LocalSource
import Mathlib.Algebra.Squarefree.Basic

/-!
# The actual ideal pair on one finite prime support

This file expands the repository's literal ideal evaluation on a common
finite support before reducing exponents. A support block contains only
actual prime ideals and the exterior/away-six conditions. It contains no
Poisson identity or asserted Fourier factorization.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualFiniteSource

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open AlgebraicNumberTheory.PowerResidueSymbols CubeAlgebra LocalDigits
open scoped BigOperators Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

/-- The multiplicity used by the literal sextic ideal evaluation agrees
with the repository's finitely supported ideal valuation vector. -/
theorem ideal_multiplicity_eq_primeExponents (I : (Ideal (𝓞 K))⁰)
    (p : HeightOneSpectrum (𝓞 K)) :
    idealPrimeMultiplicity K p I.val = primeExponents I p := by
  have hiff (k : ℕ) : p.asIdeal ^ k ∣ I.val ↔ k ≤ idealPrimeMultiplicity K p I.val := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact Associates.prime_pow_dvd_iff_le
      (Associates.mk_ne_zero.mpr (nonZeroDivisors.coe_ne_zero I)) p.associates_irreducible
  symm
  rw [primeExponents_apply]
  apply UniqueFactorizationMonoid.count_normalizedFactors_eq p.irreducible (normalize_eq _)
    ((hiff _).mpr le_rfl)
  intro hd
  have h := (hiff _).mp hd
  omega

/-- A squarefree actual ideal has the literal zero/one multiplicities
used by the conductor-digit table. -/
theorem squarefree_prime_multiplicity (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hI_sq : Squarefree I) (p : HeightOneSpectrum (𝓞 K)) :
    idealPrimeMultiplicity K p I = bit (decide (p.asIdeal ∣ I)) := by
  have hle : idealPrimeMultiplicity K p I ≤ 1 := by
    by_contra hgt
    have hc : 2 ≤ (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
      change 2 ≤ idealPrimeMultiplicity K p I
      omega
    have hpow : p.asIdeal ^ 2 ∣ I := by
      rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
      exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI)
        p.associates_irreducible).mpr hc
    exact p.irreducible.not_isUnit (hI_sq p.asIdeal (by simpa only [pow_two] using hpow))
  by_cases hd : p.asIdeal ∣ I
  · have hpos : 0 < idealPrimeMultiplicity K p I := by
      exact Nat.pos_of_ne_zero ((Associates.count_ne_zero_iff_dvd hI p.irreducible).mpr hd)
    have he : idealPrimeMultiplicity K p I = 1 := by omega
    simp [hd, bit, he]
  · rw [idealPrimeMultiplicity_eq_zero_of_not_dvd K p I hI hd]
    simp [hd, bit]

theorem supported_prime_positive (b₁ b₂ n₁ n₂ : Ideal (𝓞 K))
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ b₁ ∨ p.asIdeal ∣ b₂ ∨ p.asIdeal ∣ n₁ ∨ p.asIdeal ∣ n₂) :
    0 < bit (decide (p.asIdeal ∣ n₁)) + bit (decide (p.asIdeal ∣ n₂)) +
      idealPrimeMultiplicity K p b₁ + idealPrimeMultiplicity K p b₂ := by
  rcases hp with hp | hp | hp | hp
  · have hpos : 0 < idealPrimeMultiplicity K p b₁ :=
      Nat.pos_of_ne_zero ((Associates.count_ne_zero_iff_dvd hb₁ p.irreducible).mpr hp)
    omega
  · have hpos : 0 < idealPrimeMultiplicity K p b₂ :=
      Nat.pos_of_ne_zero ((Associates.count_ne_zero_iff_dvd hb₂ p.irreducible).mpr hp)
    omega
  · have he : bit (decide (p.asIdeal ∣ n₁)) = 1 := by simp [bit, hp]
    omega
  · have he : bit (decide (p.asIdeal ∣ n₂)) = 1 := by simp [bit, hp]
    omega

structure PrimeBlock where
  support : Finset (HeightOneSpectrum (𝓞 K))
  outside : ∀ p ∈ support, p ∉ S
  awaySix : ∀ p ∈ support, (6 : 𝓞 K) ∉ p.asIdeal

namespace PrimeBlock

def Covers (B : PrimeBlock K S) (I : Ideal (𝓞 K)) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∈ B.support

/-- The actual finite support of the four nonzero ideals in an expanded
source pair. Exteriority and avoidance of six are the only input data. -/
def ofFour (b₁ b₂ n₁ n₂ : Ideal (𝓞 K))
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hS : ∀ p : HeightOneSpectrum (𝓞 K),
      p.asIdeal ∣ b₁ ∨ p.asIdeal ∣ b₂ ∨ p.asIdeal ∣ n₁ ∨ p.asIdeal ∣ n₂ → p ∉ S)
    (h6 : ∀ p : HeightOneSpectrum (𝓞 K),
      p.asIdeal ∣ b₁ ∨ p.asIdeal ∣ b₂ ∨ p.asIdeal ∣ n₁ ∨ p.asIdeal ∣ n₂ →
        (6 : 𝓞 K) ∉ p.asIdeal) : PrimeBlock K S where
  support := (idealPrimeDivisors_finite K b₁ hb₁).toFinset ∪
    ((idealPrimeDivisors_finite K b₂ hb₂).toFinset ∪
      ((idealPrimeDivisors_finite K n₁ hn₁).toFinset ∪
        (idealPrimeDivisors_finite K n₂ hn₂).toFinset))
  outside := by
    intro p hp
    apply hS p
    simpa only [Finset.mem_union, Set.Finite.mem_toFinset, mem_idealPrimeDivisors] using hp
  awaySix := by
    intro p hp
    apply h6 p
    simpa only [Finset.mem_union, Set.Finite.mem_toFinset, mem_idealPrimeDivisors] using hp

theorem mem_ofFour_support (b₁ b₂ n₁ n₂ : Ideal (𝓞 K))
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hS : ∀ p : HeightOneSpectrum (𝓞 K),
      p.asIdeal ∣ b₁ ∨ p.asIdeal ∣ b₂ ∨ p.asIdeal ∣ n₁ ∨ p.asIdeal ∣ n₂ → p ∉ S)
    (h6 : ∀ p : HeightOneSpectrum (𝓞 K),
      p.asIdeal ∣ b₁ ∨ p.asIdeal ∣ b₂ ∨ p.asIdeal ∣ n₁ ∨ p.asIdeal ∣ n₂ →
        (6 : 𝓞 K) ∉ p.asIdeal) (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ (ofFour K S b₁ b₂ n₁ n₂ hb₁ hb₂ hn₁ hn₂ hS h6).support ↔
      p.asIdeal ∣ b₁ ∨ p.asIdeal ∣ b₂ ∨ p.asIdeal ∣ n₁ ∨ p.asIdeal ∣ n₂ := by
  simp only [ofFour, Finset.mem_union, Set.Finite.mem_toFinset, mem_idealPrimeDivisors]

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

def row (B : PrimeBlock K S) (p : B.support) (a : S.integer K) : ℂ :=
  sIntegerSexticEvaluation K S p.val (B.outside p.val p.property)
    ζ hζ σ (B.awaySix p.val p.property) a

@[simp] theorem row_pow (B : PrimeBlock K S) (p : B.support)
    (a : S.integer K) (n : ℕ) :
    row K S ζ hζ σ B p (a ^ n) = row K S ζ hζ σ B p a ^ n := by
  simp only [row, sIntegerSexticEvaluation, map_pow]

/-- This is precisely the existing ideal evaluation; the common support
only supplies its prime-local hypotheses. -/
def idealRow (B : PrimeBlock K S) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hcover : Covers K S B I) (a : S.integer K) : ℂ :=
  sIntegerSexticIdealEvaluation K S ζ hζ σ I hI
    (fun p hp => B.outside p (hcover p hp))
    (fun p hp => B.awaySix p (hcover p hp)) a

theorem idealRow_eq_product (B : PrimeBlock K S) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hcover : Covers K S B I) (a : S.integer K) :
    idealRow K S ζ hζ σ B I hI hcover a =
      ∏ p : B.support, row K S ζ hζ σ B p a ^ idealPrimeMultiplicity K p.val I := by
  letI : Fintype (idealPrimeDivisors K I) := (idealPrimeDivisors_finite K I hI).fintype
  let e : idealPrimeDivisors K I → B.support :=
    fun p => ⟨p.val, hcover p.val p.property⟩
  have he : Function.Injective e := by
    intro p q hpq
    exact Subtype.ext (congrArg Subtype.val hpq)
  unfold idealRow sIntegerSexticIdealEvaluation
  apply Fintype.prod_of_injective e he
  · intro p hp
    have hnot : ¬ p.val.asIdeal ∣ I := by
      intro hd
      apply hp
      exact ⟨⟨p.val, hd⟩, Subtype.ext rfl⟩
    rw [idealPrimeMultiplicity_eq_zero_of_not_dvd K p.val I hI hnot, pow_zero]
  · intro p
    rfl

/-- Actual denominator multiplicativity, proved on the common support of
the product ideal and valid also when the numerator has bad reduction. -/
theorem actual_ideal_mul_denominator (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I ∨ p.asIdeal ∣ J → p ∉ S)
    (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I ∨ p.asIdeal ∣ J →
      (6 : 𝓞 K) ∉ p.asIdeal) (a : S.integer K) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ (I * J) (mul_ne_zero hI hJ)
      (fun p hp => hS p (p.prime.dvd_mul.mp hp))
      (fun p hp => h6 p (p.prime.dvd_mul.mp hp)) a =
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI
      (fun p hp => hS p (Or.inl hp)) (fun p hp => h6 p (Or.inl hp)) a *
    sIntegerSexticIdealEvaluation K S ζ hζ σ J hJ
      (fun p hp => hS p (Or.inr hp)) (fun p hp => h6 p (Or.inr hp)) a := by
  let B : PrimeBlock K S := {
    support := (idealPrimeDivisors_finite K (I * J) (mul_ne_zero hI hJ)).toFinset
    outside := by
      intro p hp
      apply hS p
      apply p.prime.dvd_mul.mp
      exact (Set.Finite.mem_toFinset _).mp hp
    awaySix := by
      intro p hp
      apply h6 p
      apply p.prime.dvd_mul.mp
      exact (Set.Finite.mem_toFinset _).mp hp }
  have hc : Covers K S B (I * J) := by
    intro p hp
    exact (Set.Finite.mem_toFinset _).mpr hp
  have hcI : Covers K S B I := fun p hp => hc p (dvd_mul_of_dvd_left hp J)
  have hcJ : Covers K S B J := fun p hp => hc p (dvd_mul_of_dvd_right hp I)
  change idealRow K S ζ hζ σ B (I * J) (mul_ne_zero hI hJ) hc a =
    idealRow K S ζ hζ σ B I hI hcI a * idealRow K S ζ hζ σ B J hJ hcJ a
  rw [idealRow_eq_product, idealRow_eq_product, idealRow_eq_product]
  simp only [idealPrimeMultiplicity_mul K _ I J hI hJ, pow_add, Finset.prod_mul_distrib]

/-- The exact expanded source pair, before any primitive-conductor
reduction. All four ideal evaluations share their literal local factors. -/
theorem actual_pair_source_product
    (B : PrimeBlock K S) (b₁ b₂ n₁ n₂ : Ideal (𝓞 K))
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hcb₁ : Covers K S B b₁) (hcb₂ : Covers K S B b₂)
    (hcn₁ : Covers K S B n₁) (hcn₂ : Covers K S B n₂) (a : S.integer K) :
    (idealRow K S ζ hζ σ B b₁ hb₁ hcb₁ (a ^ 3) *
      idealRow K S ζ hζ σ B n₁ hn₁ hcn₁ a) *
      star (idealRow K S ζ hζ σ B b₂ hb₂ hcb₂ (a ^ 3) *
        idealRow K S ζ hζ σ B n₂ hn₂ hcn₂ a) =
    ∏ p : B.support,
      row K S ζ hζ σ B p a ^
        (idealPrimeMultiplicity K p.val n₁ + 3 * idealPrimeMultiplicity K p.val b₁) *
      star (row K S ζ hζ σ B p a ^
        (idealPrimeMultiplicity K p.val n₂ + 3 * idealPrimeMultiplicity K p.val b₂)) := by
  simp only [idealRow_eq_product, row_pow, star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpow (z : ℂ) (m n : ℕ) : (z ^ 3) ^ m * z ^ n = z ^ (n + 3 * m) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hpow, hpow]

/-- Primitive digit and complementary mask for the actual pair. The two
squarefree multiplicity identities are explicit arithmetic conditions on
the actual ideals, not a supplied transform formula. -/
theorem actual_pair_source_split
    (B : PrimeBlock K S) (b₁ b₂ n₁ n₂ : Ideal (𝓞 K))
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hcb₁ : Covers K S B b₁) (hcb₂ : Covers K S B b₂)
    (hcn₁ : Covers K S B n₁) (hcn₂ : Covers K S B n₂)
    (ε₁ ε₂ : B.support → Bool)
    (he₁ : ∀ p, idealPrimeMultiplicity K p.val n₁ = bit (ε₁ p))
    (he₂ : ∀ p, idealPrimeMultiplicity K p.val n₂ = bit (ε₂ p))
    (hsupport : ∀ p : B.support, 0 < bit (ε₁ p) + bit (ε₂ p) +
      idealPrimeMultiplicity K p.val b₁ + idealPrimeMultiplicity K p.val b₂)
    (a : S.integer K) :
    let t := fun p : B.support => conductorExponent
      (parity (idealPrimeMultiplicity K p.val b₁ + idealPrimeMultiplicity K p.val b₂))
      (ε₁ p) (ε₂ p)
    (idealRow K S ζ hζ σ B b₁ hb₁ hcb₁ (a ^ 3) *
      idealRow K S ζ hζ σ B n₁ hn₁ hcn₁ a) *
      star (idealRow K S ζ hζ σ B b₂ hb₂ hcb₂ (a ^ 3) *
        idealRow K S ζ hζ σ B n₂ hn₂ hcn₂ a) =
    (if ∃ p : B.support, t p = 0 ∧
        sIntegerSexticResidueMap K S p.val (B.outside p.val p.property) a = 0
      then 0 else 1) *
      ∏ p ∈ Finset.univ.filter (fun p : B.support => t p ≠ 0),
        (sexticResidueCharacter K ζ hζ σ p.val (B.awaySix p.val p.property) ^ (t p).val)
          (sIntegerSexticResidueMap K S p.val (B.outside p.val p.property) a) := by
  dsimp only
  rw [actual_pair_source_product K S ζ hζ σ B b₁ b₂ n₁ n₂
    hb₁ hb₂ hn₁ hn₂ hcb₁ hcb₂ hcn₁ hcn₂ a]
  simp_rw [he₁, he₂]
  letI : ∀ p : B.support, Field (𝓞 K ⧸ p.val.asIdeal) := fun p => Ideal.Quotient.field _
  letI : ∀ p : B.support, Fintype (𝓞 K ⧸ p.val.asIdeal) := fun p => Fintype.ofFinite _
  have h6 (p : B.support) :
      sexticResidueCharacter K ζ hζ σ p.val (B.awaySix p.val p.property) ^ 6 = 1 := by
    rw [← sexticResidueCharacter_order K ζ hζ σ p.val (B.awaySix p.val p.property)]
    exact pow_orderOf_eq_one _
  simpa only [Finset.mem_univ, true_and] using finite_source_split Finset.univ
    (fun p : B.support => sexticResidueCharacter K ζ hζ σ p.val (B.awaySix p.val p.property))
    h6 ε₁ ε₂ (fun p => idealPrimeMultiplicity K p.val b₁)
    (fun p => idealPrimeMultiplicity K p.val b₂) (fun p _ => hsupport p)
    (fun p => sIntegerSexticResidueMap K S p.val (B.outside p.val p.property) a)

end PrimeBlock

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualFiniteSource

end
