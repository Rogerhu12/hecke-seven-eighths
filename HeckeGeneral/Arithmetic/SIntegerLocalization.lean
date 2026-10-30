import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega

/-!
# Actual S-integers as a localization away from an integer

For a nonzero element `a` of a Dedekind domain, its prime support is finite.
The actual valuation-defined S-integers at that support form a localization
away from `a`. The denominator-clearing proof uses one common power of `a`,
chosen from the finitely many integral valuation exponents. This applies in
particular to the ring of integers of every number field; no principal-ideal
or finite-generation assumption is made.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open IsDedekindDomain
open scoped Classical

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The finite primes at which the integer `a` is not a unit. -/
def integerPrimeSupport (a : R) : Set (HeightOneSpectrum R) :=
  {v | a ∈ v.asIdeal}

omit [IsDedekindDomain R] in
@[simp]
theorem mem_integerPrimeSupport (a : R) (v : HeightOneSpectrum R) :
    v ∈ integerPrimeSupport a ↔ a ∈ v.asIdeal := Iff.rfl

/-- Nonzero integers have finite prime support, by ideal factorization. -/
theorem finite_integerPrimeSupport (a : R) (ha : a ≠ 0) :
    (integerPrimeSupport a).Finite := by
  have hI : Ideal.span ({a} : Set R) ≠ 0 := by
    intro h
    apply ha
    apply Ideal.span_singleton_eq_bot.mp
    simpa only [Ideal.zero_eq_bot] using h
  simpa only [integerPrimeSupport, Ideal.dvd_span_singleton] using
    (Ideal.finite_factors hI)

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The map from the original ring into its actual S-integers is injective. -/
theorem integerPrimeSupport_algebraMap_injective (a : R) :
    Function.Injective (algebraMap R ((integerPrimeSupport a).integer K)) := by
  intro b c hbc
  apply IsFractionRing.injective R K
  exact congrArg (fun z : (integerPrimeSupport a).integer K => (z : K)) hbc

/-- Inverting `a` preserves all the required valuations outside its support. -/
theorem inv_mem_integerPrimeSupport_integer (a : R) :
    (algebraMap R K a)⁻¹ ∈ (integerPrimeSupport a).integer K := by
  intro v hv
  change a ∉ v.asIdeal at hv
  have hva : v.valuation K (algebraMap R K a) = 1 :=
    v.valuation_eq_one_iff_notMem.mpr hv
  simp only [map_inv₀, hva, inv_one, le_refl]

/-- The actual S-integer image of a nonzero `a` is a unit. -/
theorem isUnit_algebraMap_integerPrimeSupport (a : R) (ha : a ≠ 0) :
    IsUnit (algebraMap R ((integerPrimeSupport a).integer K) a) := by
  have haK : algebraMap R K a ≠ 0 := by
    intro h
    apply ha
    apply IsFractionRing.injective R K
    simpa using h
  refine isUnit_iff_exists_inv.mpr
    ⟨⟨(algebraMap R K a)⁻¹, inv_mem_integerPrimeSupport_integer K a⟩, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel₀ haK

/-- A single power of `a` clears every denominator of an actual S-integer.
The exponent is chosen from the finite prime support, rather than supplied
as a localization hypothesis. -/
theorem integerPrimeSupport_clear_denominators (a : R) (ha : a ≠ 0)
    (x : (integerPrimeSupport a).integer K) :
    ∃ (n : ℕ) (b : R),
      x * algebraMap R ((integerPrimeSupport a).integer K) a ^ n =
        algebraMap R ((integerPrimeSupport a).integer K) b := by
  classical
  by_cases hx : (x : K) = 0
  · refine ⟨0, 0, Subtype.ext ?_⟩
    change (x : K) * (algebraMap R K a) ^ 0 = algebraMap R K 0
    simp [hx]
  have haK : algebraMap R K a ≠ 0 := by
    intro h
    apply ha
    apply IsFractionRing.injective R K
    simpa using h
  let t := (finite_integerPrimeSupport a ha).toFinset
  let n := t.sup fun v => (WithZero.log (v.valuation K (x : K))).toNat
  have h_integral : ∀ v : HeightOneSpectrum R,
      v.valuation K ((algebraMap R K a) ^ n * (x : K)) ≤ 1 := by
    intro v
    by_cases hv : v ∈ integerPrimeSupport a
    · have hvt : v ∈ t := by simpa only [t, Set.Finite.mem_toFinset] using hv
      have hxnNat : (WithZero.log (v.valuation K (x : K))).toNat ≤ n :=
        Finset.le_sup (f := fun w => (WithZero.log (w.valuation K (x : K))).toNat) hvt
      have hxn : WithZero.log (v.valuation K (x : K)) ≤ (n : ℤ) := by
        omega
      have hvx : v.valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
      have hva : v.valuation K (algebraMap R K a) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr haK
      have hval : v.valuation K (algebraMap R K a) < 1 :=
        (v.valuation_lt_one_iff_mem a).mpr hv
      have halog : WithZero.log (v.valuation K (algebraMap R K a)) ≤ -1 := by
        have hnegative : WithZero.log (v.valuation K (algebraMap R K a)) < 0 :=
          WithZero.exp_lt_one_iff.mp (by simpa only [WithZero.exp_log hva] using hval)
        omega
      have hmul : (n : ℤ) * WithZero.log (v.valuation K (algebraMap R K a)) ≤
          -(n : ℤ) := by
        calc
          _ ≤ (n : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left halog (Int.natCast_nonneg n)
          _ = -(n : ℤ) := by simp
      have hexponent :
          (n : ℤ) * WithZero.log (v.valuation K (algebraMap R K a)) +
            WithZero.log (v.valuation K (x : K)) ≤ 0 := by omega
      calc
        v.valuation K ((algebraMap R K a) ^ n * (x : K)) =
            v.valuation K (algebraMap R K a) ^ n * v.valuation K (x : K) := by
          rw [map_mul, map_pow]
        _ = WithZero.exp (WithZero.log (v.valuation K (algebraMap R K a))) ^ n *
            WithZero.exp (WithZero.log (v.valuation K (x : K))) := by
          rw [WithZero.exp_log hva, WithZero.exp_log hvx]
        _ = WithZero.exp
            ((n : ℤ) * WithZero.log (v.valuation K (algebraMap R K a)) +
              WithZero.log (v.valuation K (x : K))) := by
          have h := WithZero.exp_add
            (n • WithZero.log (v.valuation K (algebraMap R K a)))
            (WithZero.log (v.valuation K (x : K)))
          rw [WithZero.exp_nsmul] at h
          simpa only [nsmul_eq_mul] using h.symm
        _ ≤ 1 := WithZero.exp_le_one_iff.mpr hexponent
    · have hva : v.valuation K (algebraMap R K a) = 1 :=
        v.valuation_eq_one_iff_notMem.mpr hv
      simpa only [map_mul, map_pow, hva, one_pow, one_mul] using x.property v hv
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K
    ((algebraMap R K a) ^ n * (x : K)) h_integral
  refine ⟨n, b, Subtype.ext ?_⟩
  change (x : K) * (algebraMap R K a) ^ n = algebraMap R K b
  exact (mul_comm _ _).trans hb.symm

/-- The valuation-defined S-integers are the actual localization at powers
of `a`. This specializes to `R = 𝓞 K` for arbitrary number fields. -/
theorem integerPrimeSupport_isLocalizationAway (a : R) (ha : a ≠ 0) :
    IsLocalization.Away a ((integerPrimeSupport a).integer K) := by
  refine IsLocalization.Away.mk a
    (isUnit_algebraMap_integerPrimeSupport K a ha)
    (integerPrimeSupport_clear_denominators K a ha) ?_
  intro b c hbc
  have h : b = c := integerPrimeSupport_algebraMap_injective K a hbc
  exact ⟨0, by simp [h]⟩

end HeckeGeneral.Arithmetic
