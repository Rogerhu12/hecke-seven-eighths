import HeckeGeneral.Arithmetic.IdealFactorization
import HeckeGeneral.Analysis.GlobalThetaData
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Lean.Elab.Tactic.Omega

/-!
Actual nonzero exterior ideal pairs, reindexed by their common prime powers
and their coprime residual ideals. This uses factorization of ideals only.
No principal ideal property or multiplicativity of chosen generators enters.
SOURCE CANDIDATE ONLY: no native compilation has been run for this file.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Global.ActualIdealGcdDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic
open scoped Classical BigOperators nonZeroDivisors

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem prime_dvd_iff_exponent_pos (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    p.asIdeal ∣ I.val ↔ 0 < primeExponents I p := by
  rw [primeExponents_apply, Multiset.count_pos,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff
      (nonZeroDivisors.coe_ne_zero I)]
  exact ⟨fun h => ⟨p.prime, h⟩, fun h => h.2⟩

theorem ideals_isCoprime_iff_no_common_prime (I J : (Ideal R)⁰) :
    IsCoprime I.val J.val ↔
      ∀ p : HeightOneSpectrum R, ¬ (p.asIdeal ∣ I.val ∧ p.asIdeal ∣ J.val) := by
  constructor
  · intro h p hp
    exact p.prime.not_isUnit (h.isUnit_of_dvd' hp.1 hp.2)
  · intro h
    have hrel : IsRelPrime I.val J.val :=
      (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors
        (nonZeroDivisors.coe_ne_zero I)).mpr (by
          intro P hPI hPJ hP
          exact h (HeightOneSpectrum.ofPrime hP) ⟨hPI, hPJ⟩)
    apply Ideal.isCoprime_iff_gcd.mpr
    simpa only [Ideal.one_eq_top] using
      (Ideal.isUnit_iff.mp (gcd_isUnit_iff_isRelPrime.mpr hrel))

theorem ideals_isCoprime_iff_exponents (I J : (Ideal R)⁰) :
    IsCoprime I.val J.val ↔
      ∀ p : HeightOneSpectrum R, primeExponents I p = 0 ∨ primeExponents J p = 0 := by
  rw [ideals_isCoprime_iff_no_common_prime]
  constructor
  · intro h p
    have hp := h p
    rw [prime_dvd_iff_exponent_pos I p, prime_dvd_iff_exponent_pos J p] at hp
    omega
  · intro h p hp
    have hI := (prime_dvd_iff_exponent_pos I p).mp hp.1
    have hJ := (prime_dvd_iff_exponent_pos J p).mp hp.2
    rcases h p with h0 | h0 <;> omega

end Dedekind

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "E" => ExteriorIdeal K S

theorem exterior_exponents_injective :
    Function.Injective (fun I : E => primeExponents I.val) := by
  intro I J h
  apply Subtype.ext
  exact (primeExponentEquiv (R := 𝓞 K)).injective h

@[simp] theorem exteriorMul_exponents (I J : E) :
    primeExponents (exteriorMul K S I J).val =
      primeExponents I.val + primeExponents J.val :=
  primeExponents_mul I.val J.val

/-- An exponent subvector of an exterior ideal is again exterior. -/
def boundedExponentIdeal (I : E) (e : HeightOneSpectrum (𝓞 K) →₀ ℕ)
    (he : ∀ p, e p ≤ primeExponents I.val p) : E :=
  ⟨idealOfPrimeExponents e, by
    intro p hp
    have hpos := (prime_dvd_iff_exponent_pos (idealOfPrimeExponents e) p).mp hp
    rw [primeExponents_idealOfPrimeExponents] at hpos
    exact I.property p ((prime_dvd_iff_exponent_pos I.val p).mpr
      (lt_of_lt_of_le hpos (he p)))⟩

@[simp] theorem boundedExponentIdeal_exponents (I : E)
    (e : HeightOneSpectrum (𝓞 K) →₀ ℕ) (he : ∀ p, e p ≤ primeExponents I.val p) :
    primeExponents (boundedExponentIdeal K S I e he).val = e :=
  primeExponents_idealOfPrimeExponents e

def commonPart (I J : E) : E :=
  boundedExponentIdeal K S I (primeExponents I.val ⊓ primeExponents J.val)
    (fun p => by
      change min (primeExponents I.val p) (primeExponents J.val p) ≤ _
      exact Nat.min_le_left _ _)

def leftResidual (I J : E) : E :=
  boundedExponentIdeal K S I
    (primeExponents I.val - (primeExponents I.val ⊓ primeExponents J.val))
    (fun p => by
      change primeExponents I.val p -
        min (primeExponents I.val p) (primeExponents J.val p) ≤ _
      exact Nat.sub_le _ _)

def rightResidual (I J : E) : E :=
  boundedExponentIdeal K S J
    (primeExponents J.val - (primeExponents I.val ⊓ primeExponents J.val))
    (fun p => by
      change primeExponents J.val p -
        min (primeExponents I.val p) (primeExponents J.val p) ≤ _
      exact Nat.sub_le _ _)

@[simp] theorem commonPart_exponents (I J : E) :
    primeExponents (commonPart K S I J).val =
      primeExponents I.val ⊓ primeExponents J.val :=
  primeExponents_idealOfPrimeExponents _

@[simp] theorem leftResidual_exponents (I J : E) :
    primeExponents (leftResidual K S I J).val =
      primeExponents I.val - (primeExponents I.val ⊓ primeExponents J.val) :=
  primeExponents_idealOfPrimeExponents _

@[simp] theorem rightResidual_exponents (I J : E) :
    primeExponents (rightResidual K S I J).val =
      primeExponents J.val - (primeExponents I.val ⊓ primeExponents J.val) :=
  primeExponents_idealOfPrimeExponents _

theorem commonPart_mul_leftResidual (I J : E) :
    exteriorMul K S (commonPart K S I J) (leftResidual K S I J) = I := by
  apply exterior_exponents_injective K S
  ext p
  simp only [exteriorMul_exponents, commonPart_exponents, leftResidual_exponents,
    Finsupp.add_apply, Finsupp.inf_apply, Finsupp.tsub_apply]
  change min (primeExponents I.val p) (primeExponents J.val p) +
    (primeExponents I.val p - min (primeExponents I.val p) (primeExponents J.val p)) = _
  omega

theorem commonPart_mul_rightResidual (I J : E) :
    exteriorMul K S (commonPart K S I J) (rightResidual K S I J) = J := by
  apply exterior_exponents_injective K S
  ext p
  simp only [exteriorMul_exponents, commonPart_exponents, rightResidual_exponents,
    Finsupp.add_apply, Finsupp.inf_apply, Finsupp.tsub_apply]
  change min (primeExponents I.val p) (primeExponents J.val p) +
    (primeExponents J.val p - min (primeExponents I.val p) (primeExponents J.val p)) = _
  omega

theorem commonPart_dvd_left (I J : E) :
    (commonPart K S I J).val.val ∣ I.val.val := by
  refine ⟨(leftResidual K S I J).val.val, ?_⟩
  exact (congrArg (fun X : E => X.val.val)
    (commonPart_mul_leftResidual K S I J)).symm

theorem commonPart_dvd_right (I J : E) :
    (commonPart K S I J).val.val ∣ J.val.val := by
  refine ⟨(rightResidual K S I J).val.val, ?_⟩
  exact (congrArg (fun X : E => X.val.val)
    (commonPart_mul_rightResidual K S I J)).symm

theorem residuals_isCoprime (I J : E) :
    IsCoprime (leftResidual K S I J).val.val (rightResidual K S I J).val.val := by
  apply (ideals_isCoprime_iff_exponents _ _).mpr
  intro p
  simp only [leftResidual_exponents, rightResidual_exponents,
    Finsupp.tsub_apply, Finsupp.inf_apply]
  change primeExponents I.val p - min (primeExponents I.val p) (primeExponents J.val p) = 0 ∨
    primeExponents J.val p - min (primeExponents I.val p) (primeExponents J.val p) = 0
  omega

/-- The factors are genuine nonzero exterior ideals; coprimality is proved. -/
abbrev CoprimeTriple :=
  {t : E × (E × E) // IsCoprime t.2.1.val.val t.2.2.val.val}

theorem commonPart_of_coprime_mul (C N₁ N₂ : E)
    (h : IsCoprime N₁.val.val N₂.val.val) :
    commonPart K S (exteriorMul K S C N₁) (exteriorMul K S C N₂) = C := by
  apply exterior_exponents_injective K S
  ext p
  have hp := (ideals_isCoprime_iff_exponents N₁.val N₂.val).mp h p
  simp only [commonPart_exponents, exteriorMul_exponents,
    Finsupp.inf_apply, Finsupp.add_apply]
  change min (primeExponents C.val p + primeExponents N₁.val p)
    (primeExponents C.val p + primeExponents N₂.val p) = primeExponents C.val p
  rcases hp with hp | hp <;> omega

theorem leftResidual_of_coprime_mul (C N₁ N₂ : E)
    (h : IsCoprime N₁.val.val N₂.val.val) :
    leftResidual K S (exteriorMul K S C N₁) (exteriorMul K S C N₂) = N₁ := by
  apply exterior_exponents_injective K S
  ext p
  have hp := (ideals_isCoprime_iff_exponents N₁.val N₂.val).mp h p
  simp only [leftResidual_exponents, exteriorMul_exponents,
    Finsupp.tsub_apply, Finsupp.inf_apply, Finsupp.add_apply]
  change (primeExponents C.val p + primeExponents N₁.val p) -
    min (primeExponents C.val p + primeExponents N₁.val p)
      (primeExponents C.val p + primeExponents N₂.val p) = primeExponents N₁.val p
  rcases hp with hp | hp <;> omega

theorem rightResidual_of_coprime_mul (C N₁ N₂ : E)
    (h : IsCoprime N₁.val.val N₂.val.val) :
    rightResidual K S (exteriorMul K S C N₁) (exteriorMul K S C N₂) = N₂ := by
  apply exterior_exponents_injective K S
  ext p
  have hp := (ideals_isCoprime_iff_exponents N₁.val N₂.val).mp h p
  simp only [rightResidual_exponents, exteriorMul_exponents,
    Finsupp.tsub_apply, Finsupp.inf_apply, Finsupp.add_apply]
  change (primeExponents C.val p + primeExponents N₂.val p) -
    min (primeExponents C.val p + primeExponents N₁.val p)
      (primeExponents C.val p + primeExponents N₂.val p) = primeExponents N₂.val p
  rcases hp with hp | hp <;> omega

/-- Any coprime residual factorization has exactly the min/sub factors above. -/
theorem coprime_factorization_unique (I J C N₁ N₂ : E)
    (h : IsCoprime N₁.val.val N₂.val.val)
    (hI : exteriorMul K S C N₁ = I) (hJ : exteriorMul K S C N₂ = J) :
    C = commonPart K S I J ∧ N₁ = leftResidual K S I J ∧
      N₂ = rightResidual K S I J := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hI, hJ] using (commonPart_of_coprime_mul K S C N₁ N₂ h).symm
  · simpa only [hI, hJ] using (leftResidual_of_coprime_mul K S C N₁ N₂ h).symm
  · simpa only [hI, hJ] using (rightResidual_of_coprime_mul K S C N₁ N₂ h).symm

/-- Exact gcd/residual reindexing of every pair, including the unit ideal. -/
def pairGcdEquiv : (E × E) ≃ CoprimeTriple K S where
  toFun ij := ⟨(commonPart K S ij.1 ij.2,
    (leftResidual K S ij.1 ij.2, rightResidual K S ij.1 ij.2)),
      residuals_isCoprime K S ij.1 ij.2⟩
  invFun t := (exteriorMul K S t.val.1 t.val.2.1,
    exteriorMul K S t.val.1 t.val.2.2)
  left_inv ij := by
    apply Prod.ext
    · exact commonPart_mul_leftResidual K S ij.1 ij.2
    · exact commonPart_mul_rightResidual K S ij.1 ij.2
  right_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · exact commonPart_of_coprime_mul K S t.val.1 t.val.2.1 t.val.2.2 t.property
    · apply Prod.ext
      · exact leftResidual_of_coprime_mul K S t.val.1 t.val.2.1 t.val.2.2 t.property
      · exact rightResidual_of_coprime_mul K S t.val.1 t.val.2.1 t.val.2.2 t.property

@[simp] theorem pairGcdEquiv_symm_apply (t : CoprimeTriple K S) :
    (pairGcdEquiv K S).symm t =
      (exteriorMul K S t.val.1 t.val.2.1, exteriorMul K S t.val.1 t.val.2.2) := rfl

/-- The complete support condition is on the reconstructed original ideals. -/
def finiteGcdTriples (A B : Finset E) : Finset (CoprimeTriple K S) :=
  (A.product B).image (pairGcdEquiv K S)

theorem mem_finiteGcdTriples (A B : Finset E) (t : CoprimeTriple K S) :
    t ∈ finiteGcdTriples K S A B ↔
      exteriorMul K S t.val.1 t.val.2.1 ∈ A ∧
      exteriorMul K S t.val.1 t.val.2.2 ∈ B := by
  change t ∈ (A.product B).image (pairGcdEquiv K S) ↔ _
  constructor
  · rintro h
    obtain ⟨ij, hij, ht⟩ := Finset.mem_image.mp h
    have hs : (pairGcdEquiv K S).symm t = ij := by
      rw [← ht, Equiv.symm_apply_apply]
    have hmem : (pairGcdEquiv K S).symm t ∈ A.product B := by
      rw [hs]
      exact hij
    exact Finset.mem_product.mp hmem
  · intro ht
    exact Finset.mem_image.mpr ⟨(pairGcdEquiv K S).symm t,
      Finset.mem_product.mpr ht, Equiv.apply_symm_apply _ t⟩

/-- Reindex the actual finite double sum; no analytic summability is needed. -/
theorem sum_pair_eq_sum_gcdTriples {M : Type*} [AddCommMonoid M]
    (A B : Finset E) (F : E → E → M) :
    (∑ I ∈ A, ∑ J ∈ B, F I J) =
      ∑ t ∈ finiteGcdTriples K S A B,
        F (exteriorMul K S t.val.1 t.val.2.1)
          (exteriorMul K S t.val.1 t.val.2.2) := by
  rw [← Finset.sum_product' A B F]
  apply Finset.sum_equiv (pairGcdEquiv K S)
  · intro ij
    constructor
    · intro hij
      exact Finset.mem_image.mpr ⟨ij, hij, rfl⟩
    · intro ht
      obtain ⟨ij', hij', heq⟩ := Finset.mem_image.mp ht
      exact (pairGcdEquiv K S).injective heq ▸ hij'
  · intro ij _
    change F ij.1 ij.2 =
      F (exteriorMul K S (commonPart K S ij.1 ij.2) (leftResidual K S ij.1 ij.2))
        (exteriorMul K S (commonPart K S ij.1 ij.2) (rightResidual K S ij.1 ij.2))
    rw [commonPart_mul_leftResidual, commonPart_mul_rightResidual]

end HeckeGeneral.ThetaSkeleton.Global.ActualIdealGcdDraft
