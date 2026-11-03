import HeckeGeneral.Arithmetic.IdealFactorization
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic.SplitIfs

/-!
# Powerful and residual parts of actual nonzero integral ideals

All objects in this file are actual nonzero ideals of a Dedekind domain.
They are reconstructed from the project's proved prime-exponent equivalence.
The module imports no analytic energy assertion and no theta-reflection input.

For a powerful ideal the canonical decomposition is `I = A^2 * B^3`, with B
squarefree.  The map to (A,B) is injective and is suitable for a Rankin count.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.IdealRows

open IsDedekindDomain UniqueFactorizationMonoid HeckeGeneral.Arithmetic
open scoped Classical BigOperators nonZeroDivisors NumberField

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The actual exponent detects prime divisibility, including unit ideals. -/
theorem exponent_ne_zero_iff_dvd (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    primeExponents I p ≠ 0 ↔ p.asIdeal ∣ I.val := by
  simp only [primeExponents_apply, Multiset.count_ne_zero,
    mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero I), p.prime, true_and]

theorem exponent_pow (I : (Ideal R)⁰) (n : ℕ) (p : HeightOneSpectrum R) :
    primeExponents (I ^ n) p = n * primeExponents I p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, primeExponents_mul, Finsupp.add_apply, ih, Nat.succ_mul]

/-- Squarefree actual ideals have only zero and one prime exponents. -/
theorem exponent_le_one_of_squarefree (I : (Ideal R)⁰)
    (hI : Squarefree I.val) (p : HeightOneSpectrum R) :
    primeExponents I p ≤ 1 :=
  Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors (nonZeroDivisors.coe_ne_zero I)).mp hI)
    p.asIdeal

/-- The converse is used on constructed ideals, so squarefreeness is proved. -/
theorem squarefree_of_exponent_le_one (I : (Ideal R)⁰)
    (hI : ∀ p : HeightOneSpectrum R, primeExponents I p ≤ 1) :
    Squarefree I.val := by
  apply (squarefree_iff_nodup_normalizedFactors (nonZeroDivisors.coe_ne_zero I)).mpr
  apply Multiset.nodup_iff_count_le_one.mpr
  intro P
  by_cases hP : P ∈ normalizedFactors I.val
  · let p : HeightOneSpectrum R := HeightOneSpectrum.ofPrime (prime_of_normalized_factor P hP)
    exact hI p
  · rw [Multiset.count_eq_zero_of_notMem hP]
    omega

/-- An actual ideal is powerful when every positive prime exponent is at least two. -/
def Powerful (I : (Ideal R)⁰) : Prop :=
  ∀ p : HeightOneSpectrum R, primeExponents I p = 0 ∨ 2 ≤ primeExponents I p

/-- All complete prime powers of exponent at least two. -/
def powerfulPart (I : (Ideal R)⁰) : (Ideal R)⁰ :=
  idealOfPrimeExponents ((primeExponents I).mapRange
    (fun e => if 2 ≤ e then e else 0) (by decide))

/-- Precisely the valuation-one primes, with their actual ideals retained. -/
def residualPart (I : (Ideal R)⁰) : (Ideal R)⁰ :=
  idealOfPrimeExponents ((primeExponents I).mapRange
    (fun e => if e = 1 then 1 else 0) (by decide))

@[simp] theorem exponent_powerfulPart (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    primeExponents (powerfulPart I) p =
      if 2 ≤ primeExponents I p then primeExponents I p else 0 := by
  simp only [powerfulPart, primeExponents_idealOfPrimeExponents, Finsupp.mapRange_apply]

@[simp] theorem exponent_residualPart (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    primeExponents (residualPart I) p = if primeExponents I p = 1 then 1 else 0 := by
  simp only [residualPart, primeExponents_idealOfPrimeExponents, Finsupp.mapRange_apply]

theorem powerfulPart_powerful (I : (Ideal R)⁰) : Powerful (powerfulPart I) := by
  intro p
  rw [exponent_powerfulPart]
  split_ifs with hp
  · exact Or.inr hp
  · exact Or.inl rfl

theorem residualPart_squarefree (I : (Ideal R)⁰) : Squarefree (residualPart I).val := by
  apply squarefree_of_exponent_le_one
  intro p
  rw [exponent_residualPart]
  split_ifs <;> omega

/-- No component is discarded: powerful times valuation-one part is the original ideal. -/
theorem powerful_residual_decomposition (I : (Ideal R)⁰) :
    powerfulPart I * residualPart I = I := by
  apply (primeExponentEquiv (R := R)).injective
  ext p
  change primeExponents (powerfulPart I * residualPart I) p = primeExponents I p
  rw [primeExponents_mul, Finsupp.add_apply, exponent_powerfulPart, exponent_residualPart]
  split_ifs <;> omega

/-- The two actual row parts have disjoint prime support. -/
theorem powerful_residual_coprime (I : (Ideal R)⁰) :
    IsCoprime (powerfulPart I).val (residualPart I).val := by
  apply Ideal.coprime_of_no_prime_ge
  intro P hpow hres hP
  have hP0 : P ≠ ⊥ := by
    intro hz
    exact nonZeroDivisors.coe_ne_zero (powerfulPart I) (le_bot_iff.mp (hz ▸ hpow))
  let p : HeightOneSpectrum R := ⟨P, hP, hP0⟩
  have hp : primeExponents (powerfulPart I) p ≠ 0 :=
    (exponent_ne_zero_iff_dvd _ p).mpr (Ideal.dvd_iff_le.mpr hpow)
  have hr : primeExponents (residualPart I) p ≠ 0 :=
    (exponent_ne_zero_iff_dvd _ p).mpr (Ideal.dvd_iff_le.mpr hres)
  rw [exponent_powerfulPart] at hp
  rw [exponent_residualPart] at hr
  split_ifs at hp hr <;> omega

theorem powerfulPart_dvd (I : (Ideal R)⁰) : (powerfulPart I).val ∣ I.val := by
  refine ⟨(residualPart I).val, ?_⟩
  exact (congrArg Subtype.val (powerful_residual_decomposition I)).symm

theorem residualPart_dvd (I : (Ideal R)⁰) : (residualPart I).val ∣ I.val := by
  refine ⟨(powerfulPart I).val, ?_⟩
  have h := congrArg Subtype.val (powerful_residual_decomposition I)
  simpa only [Submonoid.coe_mul, mul_comm] using h.symm

/-- The canonical square exponent in a powerful number is `e/2 - e%2`. -/
def squareExponent (e : ℕ) : ℕ := e / 2 - e % 2

/-- The cube exponent is the parity of the original exponent. -/
def cubeExponent (e : ℕ) : ℕ := e % 2

@[simp] theorem squareExponent_zero : squareExponent 0 = 0 := by decide
@[simp] theorem cubeExponent_zero : cubeExponent 0 = 0 := by decide

theorem powerful_exponent_decomposition (e : ℕ) (he : e = 0 ∨ 2 ≤ e) :
    2 * squareExponent e + 3 * cubeExponent e = e := by
  unfold squareExponent cubeExponent
  omega

/-- Squarefree cube exponents make the square/cube decomposition unique. -/
theorem powerful_exponent_unique (e a b : ℕ) (hb : b ≤ 1)
    (he : 2 * a + 3 * b = e) : a = squareExponent e ∧ b = cubeExponent e := by
  unfold squareExponent cubeExponent
  omega

def powerfulSquarePart (I : (Ideal R)⁰) : (Ideal R)⁰ :=
  idealOfPrimeExponents ((primeExponents I).mapRange squareExponent squareExponent_zero)

def powerfulCubePart (I : (Ideal R)⁰) : (Ideal R)⁰ :=
  idealOfPrimeExponents ((primeExponents I).mapRange cubeExponent cubeExponent_zero)

@[simp] theorem exponent_powerfulSquarePart (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    primeExponents (powerfulSquarePart I) p = squareExponent (primeExponents I p) := by
  simp only [powerfulSquarePart, primeExponents_idealOfPrimeExponents, Finsupp.mapRange_apply]

@[simp] theorem exponent_powerfulCubePart (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    primeExponents (powerfulCubePart I) p = cubeExponent (primeExponents I p) := by
  simp only [powerfulCubePart, primeExponents_idealOfPrimeExponents, Finsupp.mapRange_apply]

theorem powerfulCubePart_squarefree (I : (Ideal R)⁰) :
    Squarefree (powerfulCubePart I).val := by
  apply squarefree_of_exponent_le_one
  intro p
  rw [exponent_powerfulCubePart]
  unfold cubeExponent
  omega

/-- Canonical `A² B³` decomposition of every actual powerful ideal. -/
theorem powerful_decomposition (I : (Ideal R)⁰) (hI : Powerful I) :
    powerfulSquarePart I ^ 2 * powerfulCubePart I ^ 3 = I := by
  apply (primeExponentEquiv (R := R)).injective
  ext p
  change primeExponents (powerfulSquarePart I ^ 2 * powerfulCubePart I ^ 3) p =
    primeExponents I p
  rw [primeExponents_mul, Finsupp.add_apply, exponent_pow, exponent_pow,
    exponent_powerfulSquarePart, exponent_powerfulCubePart]
  exact powerful_exponent_decomposition _ (hI p)

/-- Uniqueness is proved at each actual prime, and then by ideal reconstruction. -/
theorem powerful_decomposition_unique (I A B : (Ideal R)⁰)
    (hB : Squarefree B.val) (hI : A ^ 2 * B ^ 3 = I) :
    A = powerfulSquarePart I ∧ B = powerfulCubePart I := by
  have hlocal (p : HeightOneSpectrum R) :
      primeExponents A p = squareExponent (primeExponents I p) ∧
        primeExponents B p = cubeExponent (primeExponents I p) := by
    apply powerful_exponent_unique _ _ _ (exponent_le_one_of_squarefree B hB p)
    have h := congrArg (fun J : (Ideal R)⁰ => primeExponents J p) hI
    simpa only [primeExponents_mul, Finsupp.add_apply, exponent_pow] using h
  constructor
  · apply (primeExponentEquiv (R := R)).injective
    ext p
    change primeExponents A p = primeExponents (powerfulSquarePart I) p
    rw [exponent_powerfulSquarePart]
    exact (hlocal p).1
  · apply (primeExponentEquiv (R := R)).injective
    ext p
    change primeExponents B p = primeExponents (powerfulCubePart I) p
    rw [exponent_powerfulCubePart]
    exact (hlocal p).2

/-- The countable pair injection used by the powerful-row Rankin bound. -/
def powerfulPair (I : {I : (Ideal R)⁰ // Powerful I}) : (Ideal R)⁰ × (Ideal R)⁰ :=
  (powerfulSquarePart I.val, powerfulCubePart I.val)

theorem powerfulPair_injective : Function.Injective (powerfulPair (R := R)) := by
  intro I J h
  apply Subtype.ext
  have hA := congrArg Prod.fst h
  have hB := congrArg Prod.snd h
  change powerfulSquarePart I.val = powerfulSquarePart J.val at hA
  change powerfulCubePart I.val = powerfulCubePart J.val at hB
  calc
    I.val = powerfulSquarePart I.val ^ 2 * powerfulCubePart I.val ^ 3 :=
      (powerful_decomposition I.val I.property).symm
    _ = powerfulSquarePart J.val ^ 2 * powerfulCubePart J.val ^ 3 := by rw [hA, hB]
    _ = J.val := powerful_decomposition J.val J.property

/-- Actual finite-support prime exponent vectors compare ideal divisibility. -/
theorem dvd_of_exponents_le (I J : (Ideal R)⁰)
    (h : ∀ p : HeightOneSpectrum R, primeExponents I p ≤ primeExponents J p) :
    I.val ∣ J.val := by
  let e := primeExponents J - primeExponents I
  have he : primeExponents I + e = primeExponents J := by
    ext p
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, e]
    exact Nat.add_sub_of_le (h p)
  refine ⟨(idealOfPrimeExponents e).val, ?_⟩
  have hr : I * idealOfPrimeExponents e = J := by
    apply (primeExponentEquiv (R := R)).injective
    change primeExponents (I * idealOfPrimeExponents e) = primeExponents J
    rw [primeExponents_mul, primeExponents_idealOfPrimeExponents, he]
  exact (congrArg Subtype.val hr).symm

set_option maxHeartbeats 800000 in
/-- An active radical supported on a powerful ideal costs at most half its
norm length: its square divides that ideal, with no asymptotic estimate. -/
theorem radical_sq_dvd_powerful (A I : (Ideal R)⁰)
    (hA : Squarefree A.val) (hI : Powerful I)
    (hsupport : ∀ p : HeightOneSpectrum R,
      p.asIdeal ∣ A.val → p.asIdeal ∣ I.val) : A.val ^ 2 ∣ I.val := by
  have hd : (A ^ 2).val ∣ I.val := dvd_of_exponents_le (A ^ 2) I (by
    intro p
    rw [exponent_pow]
    have hAp := exponent_le_one_of_squarefree A hA p
    by_cases hAz : primeExponents A p = 0
    · simp [hAz]
    · have hIp : primeExponents I p ≠ 0 :=
        (exponent_ne_zero_iff_dvd I p).mpr (hsupport p ((exponent_ne_zero_iff_dvd A p).mp hAz))
      have hI2 : 2 ≤ primeExponents I p := (hI p).resolve_left hIp
      omega)
  simpa only [SubmonoidClass.coe_pow] using hd

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Exact multiplicative norm identity for the powerful/squarefree row split. -/
theorem norm_powerful_residual_decomposition (I : (Ideal (𝓞 K))⁰) :
    (I.val.absNorm : ℝ) =
      ((powerfulPart I).val.absNorm : ℝ) * ((residualPart I).val.absNorm : ℝ) := by
  have h := congrArg (fun J : (Ideal (𝓞 K))⁰ => (J.val.absNorm : ℝ))
    (powerful_residual_decomposition I)
  simpa only [Submonoid.coe_mul, map_mul, Nat.cast_mul] using h.symm

/-- Exact norm identity for the canonical pair, ready for positive real powers. -/
theorem norm_powerful_decomposition (I : (Ideal (𝓞 K))⁰) (hI : Powerful I) :
    (I.val.absNorm : ℝ) =
      ((powerfulSquarePart I).val.absNorm : ℝ) ^ 2 *
        ((powerfulCubePart I).val.absNorm : ℝ) ^ 3 := by
  have h := congrArg (fun J : (Ideal (𝓞 K))⁰ => (J.val.absNorm : ℝ))
    (powerful_decomposition I hI)
  simpa only [Submonoid.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow,
    Nat.cast_mul, Nat.cast_pow] using h.symm

/-- The small-prime radical inequality behind `2 A₀ ≤ O` in the low ledger. -/
theorem norm_radical_sq_le_powerful (A I : (Ideal (𝓞 K))⁰)
    (hA : Squarefree A.val) (hI : Powerful I)
    (hsupport : ∀ p : HeightOneSpectrum (𝓞 K),
      p.asIdeal ∣ A.val → p.asIdeal ∣ I.val) :
    (A.val.absNorm : ℝ) ^ 2 ≤ (I.val.absNorm : ℝ) := by
  have hd := radical_sq_dvd_powerful A I hA hI hsupport
  have hn : Ideal.absNorm (A.val ^ 2) ∣ Ideal.absNorm I.val := map_dvd Ideal.absNorm hd
  have hpos : 0 < Ideal.absNorm I.val := Ideal.absNorm_pos_of_nonZeroDivisors I
  have hle := Nat.le_of_dvd hpos hn
  simpa only [map_pow, Nat.cast_pow] using (Nat.cast_le.mpr hle :
    (Ideal.absNorm (A.val ^ 2) : ℝ) ≤ (Ideal.absNorm I.val : ℝ))

end NumberField

#print axioms powerful_residual_decomposition
#print axioms powerful_residual_coprime
#print axioms powerful_decomposition
#print axioms powerful_decomposition_unique
#print axioms powerfulPair_injective
#print axioms radical_sq_dvd_powerful
#print axioms norm_radical_sq_le_powerful

end HeckeSkeleton.LowEnergy.IdealRows
