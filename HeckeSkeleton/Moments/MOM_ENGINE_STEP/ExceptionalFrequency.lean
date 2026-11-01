import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GeneratedCorrelation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalRows

/-!
# The fourth-power base factor at actual multiplicity-one nonunit primes

The actual frequency extraction contributes exactly two copies of each
selected prime: one from the common gcd and one from the nonunit radical.
The primitive finite-character input prescribes the original row
valuation modulo six.  Combining these two facts with a sixth-power
classification of the residual row forces the base ideal to contain the
fourth power of the whole selected radical.

No exceptional-row count, base-norm saving, or frequency extraction is
an assumption of the final actual-correlation theorem.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def multiplicityOneNonunitPrimes (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) : Finset ι :=
  Finset.univ.filter (fun i => m i = 1 ∧ n i = 1 ∧
    nonunitFrequencySaving C (p i) (m i) (n i) h)

def multiplicityOneNonunitRadical (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) : A.Exterior :=
  primePowerProduct p (fun i => if i ∈ multiplicityOneNonunitPrimes C p m n h then 1 else 0)

/-- The exact two frozen copies are read from the actual ideal identity. -/
theorem multiplicity_one_nonunit_extracted_count
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p)
    (m n : ι → ℕ) (h : A.R) (Ih Ir : A.Exterior)
    (hextract : Ih.val = gcd (primePowerProduct p m).val (primePowerProduct p n).val *
      (nonunitFrequencyRadical C p m n h).val * Ir.val)
    (i : ι) (hi : i ∈ multiplicityOneNonunitPrimes C p m n h) :
    (normalizedFactors Ih.val).count (p i).val.asIdeal =
      2 + (normalizedFactors Ir.val).count (p i).val.asIdeal := by
  obtain ⟨hm, hn, hnonunit⟩ := (Finset.mem_filter.mp hi).2
  rw [← primePowerProduct_min_eq_gcd p hp m n] at hextract
  rw [hextract,
    normalizedFactors_mul
      (mul_ne_zero (primePowerProduct p (fun j => min (m j) (n j))).property.1
        (nonunitFrequencyRadical C p m n h).property.1) Ir.property.1,
    Multiset.count_add,
    normalizedFactors_mul (primePowerProduct p (fun j => min (m j) (n j))).property.1
      (nonunitFrequencyRadical C p m n h).property.1,
    Multiset.count_add, primePowerProduct_count p hp]
  change min (m i) (n i) +
    (normalizedFactors (primePowerProduct p (fun j =>
      if nonunitFrequencySaving C (p j) (m j) (n j) h then 1 else 0)).val).count
        (p i).val.asIdeal +
      (normalizedFactors Ir.val).count (p i).val.asIdeal = _
  rw [primePowerProduct_count p hp, if_pos hnonunit, hm, hn]
  omega

private theorem prime_pow_dvd_of_count_le (p : HeightOneSpectrum (𝓞 F))
    (I : Ideal (𝓞 F)) (hI : I ≠ 0) (r : ℕ)
    (hr : r ≤ (normalizedFactors I).count p.asIdeal) : p.asIdeal ^ r ∣ I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors
    (pow_ne_zero r p.ne_bot) hI).mpr
  rw [p.irreducible.normalizedFactors_pow, normalize_eq]
  exact Multiset.le_count_iff_replicate_le.mp hr

/-- The six-congruence is a primitive inducing-character classification.
All fourth-power divisibility and the base-norm loss are proved here. -/
theorem exceptional_frequency_base_fourth_power
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p)
    (m n : ι → ℕ) (h : A.R) (Ih Ir : A.Exterior)
    (hextract : Ih.val = gcd (primePowerProduct p m).val (primePowerProduct p n).val *
      (nonunitFrequencyRadical C p m n h).val * Ir.val)
    (hclass : ∀ i ∈ multiplicityOneNonunitPrimes C p m n h,
      6 ∣ (normalizedFactors Ih.val).count (p i).val.asIdeal)
    (base factor : Ideal (𝓞 F)) (hfactor : Ir.val = base * factor ^ 6) :
    (multiplicityOneNonunitRadical C p m n h).val ^ 4 ∣ base ∧
      (A.exteriorNorm (multiplicityOneNonunitRadical C p m n h)) ^ 4 ≤
        (Ideal.absNorm base : ℝ) := by
  have hprod : base * factor ^ 6 ≠ 0 := hfactor ▸ Ir.property.1
  have hbase : base ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hfactorpow : factor ^ 6 ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have hfour (i : ι) (hi : i ∈ multiplicityOneNonunitPrimes C p m n h) :
      4 ≤ (normalizedFactors base).count (p i).val.asIdeal := by
    have he := multiplicity_one_nonunit_extracted_count C p hp m n h Ih Ir hextract i hi
    have hmod := hclass i hi
    rw [hfactor, normalizedFactors_mul hbase hfactorpow, Multiset.count_add,
      normalizedFactors_pow] at he
    simp only [Multiset.count_nsmul] at he
    obtain ⟨j, hj⟩ := hmod
    omega
  have hdiv : (multiplicityOneNonunitRadical C p m n h).val ^ 4 ∣ base := by
    change (∏ i, (p i).val.asIdeal ^
      (if i ∈ multiplicityOneNonunitPrimes C p m n h then 1 else 0)) ^ 4 ∣ base
    rw [← Finset.prod_pow]
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      have hpij : (p i).val ≠ (p j).val := fun he => hij (hp (Subtype.ext he))
      exact (((p i).val.isCoprime_of_ne (p j).val hpij).pow).pow
    · intro i
      by_cases hi : i ∈ multiplicityOneNonunitPrimes C p m n h
      · rw [if_pos hi, pow_one]
        exact prime_pow_dvd_of_count_le (p i).val base hbase 4 (hfour i hi)
      · simp only [if_neg hi, pow_zero, one_pow, one_dvd]
  refine ⟨hdiv, ?_⟩
  change (Ideal.absNorm (multiplicityOneNonunitRadical C p m n h).val : ℝ) ^ 4 ≤
    (Ideal.absNorm base : ℝ)
  have hn : Ideal.absNorm ((multiplicityOneNonunitRadical C p m n h).val ^ 4) ≤
      Ideal.absNorm base :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (fun hz => hbase (Ideal.absNorm_eq_zero_iff.mp hz)))
      (map_dvd Ideal.absNorm hdiv)
  rw [map_pow] at hn
  exact_mod_cast hn

/-- The actual complete correlation constructs the extracted row first.
Every subsequent primitive sixth-power sector classification therefore
receives the proved fourth-power base factor. -/
theorem actual_exceptional_frequency_base_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (a b : A.R) (ha : A.Generates (primePowerProduct p m) a)
    (hb : A.Generates (primePowerProduct p n) b)
    (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h)
    (hne : generatedIdealCorrelation (σ := σ) (primePowerProduct p m) (primePowerProduct p n)
      a b ha hb h ≠ 0)
    (hclass : ∀ i ∈ multiplicityOneNonunitPrimes C p m n h,
      6 ∣ (normalizedFactors Ih.val).count (p i).val.asIdeal) :
    ∃ h' : A.R, ∃ Ir : A.Exterior,
      A.Generates Ir h' ∧
      h = primePowerProductGenerator C p (fun i => min (m i) (n i)) *
        nonunitFrequencyGenerator C p m n h * h' ∧
      A.exteriorNorm Ih =
        (Ideal.absNorm (gcd (primePowerProduct p m).val (primePowerProduct p n).val) : ℝ) *
          A.exteriorNorm (nonunitFrequencyRadical C p m n h) * A.exteriorNorm Ir ∧
      ∀ base factor : Ideal (𝓞 F), Ir.val = base * factor ^ 6 →
        (multiplicityOneNonunitRadical C p m n h).val ^ 4 ∣ base ∧
          (A.exteriorNorm (multiplicityOneNonunitRadical C p m n h)) ^ 4 ≤
            (Ideal.absNorm base : ℝ) := by
  obtain ⟨h', Ir, hgen, hfreq, hideal, hnorm⟩ :=
    actual_product_correlation_frequency_ideal_extract_of_generates
      C p hp m n a b ha hb Ih h hh hne
  refine ⟨h', Ir, hgen, hfreq, hnorm, ?_⟩
  intro base factor hfactor
  exact exceptional_frequency_base_fourth_power C p hp m n h Ih Ir hideal hclass
    base factor hfactor

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.exceptional_frequency_base_fourth_power
#print axioms HeckeSkeleton.Moments.EngineStep.actual_exceptional_frequency_base_bound

