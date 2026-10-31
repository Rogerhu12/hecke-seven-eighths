import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualSecondSaving
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteMovingRowRecipe
import HeckeGeneral.Characters.SIntegerSexticPowerMask

/-!
# The actual fixed moving factor after common-frequency extraction

The extracted factor is the original gcd generator times the nonunit
frequency generator.  Its exponent at a common prime is split into a
multiple of six and the literal remainder plus the nonunit indicator.
Nonvanishing of the complete correlation proves that the latter factor
has radical exactly the union of the unit and nonunit frequency primes.

The sixth-power part keeps its full coprimality mask.  The active part is
an original nonzero S-integer, and its finite character is computed using
the original probe, as in `OriginalMovingFactors`.  No assertion that
this character belongs to the original finite theta family is made.

The active element depends only on the finite nonunit indicator pattern.
Thus it can be fixed before the row and Fourier variables by passing to
that pattern's actual subtype; the equalities below hold on every member
of the subtype, not only on a selected summation support.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum
open HeckePort.Moments CommonSupportMass
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem moving_powerProduct_count {ι : Type*}
    (P : ι → Ideal (𝓞 K)) (hP : ∀ i, Prime (P i)) (n : ι → ℕ)
    (S : Finset ι) (Q : Ideal (𝓞 K)) :
    (normalizedFactors (∏ i ∈ S, P i ^ n i)).count Q =
      ∑ i ∈ S, if P i = Q then n i else 0 := by
  induction S using Finset.induction_on with
  | empty =>
    change (normalizedFactors (1 : Ideal (𝓞 K))).count Q = 0
    rw [normalizedFactors_one]
    rfl
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      normalizedFactors_mul (pow_ne_zero _ (hP a).ne_zero)
        (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hP i).ne_zero)),
      Multiset.count_add, ih, (hP a).irreducible.normalizedFactors_pow]
    simp only [normalize_eq, Multiset.count_replicate]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The support formula also covers zero exponents, which occur in the
actual sixth/active split. -/
theorem primePowerProduct_support_nonzero (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (n : ι → ℕ) :
    primeSupport (primePowerProduct p n).val =
      (Finset.univ.filter (fun i => n i ≠ 0)).image (fun i => (p i).val.asIdeal) := by
  ext Q
  change Q ∈ (normalizedFactors (primePowerProduct p n).val).toFinset ↔ _
  rw [Multiset.mem_toFinset, ← Multiset.count_pos]
  constructor
  · intro hQ
    by_contra hmem
    have hz (i : ι) : (if (p i).val.asIdeal = Q then n i else 0) = 0 := by
      split_ifs with he
      · by_contra hn
        exact hmem (Finset.mem_image.mpr
          ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hn⟩, he⟩)
      · rfl
    change 0 < (normalizedFactors (∏ i, (p i).val.asIdeal ^ n i)).count Q at hQ
    rw [moving_powerProduct_count _ (fun i => (p i).val.prime)] at hQ
    simp only [hz, Finset.sum_const_zero, lt_self_iff_false] at hQ
  · intro hQ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
    rw [primePowerProduct_count p hp n i]
    exact Nat.pos_of_ne_zero (Finset.mem_filter.mp hi).2

theorem commonRadical_primePowerProduct_indicator (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (n : ι → ℕ) :
    commonRadical (primePowerProduct p n).val (primePowerProduct p n).val =
      (primePowerProduct p (fun i => if n i ≠ 0 then 1 else 0)).val := by
  rw [commonRadical, primePowerProduct_support_nonzero p hp n,
    Finset.inter_self, Finset.prod_image (primePowerProduct_prime_injective p hp).injOn]
  change (∏ i ∈ Finset.univ.filter (fun i => n i ≠ 0), (p i).val.asIdeal) =
    ∏ i, (p i).val.asIdeal ^ (if n i ≠ 0 then 1 else 0)
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hn : n i ≠ 0 <;> simp [hn]

/-- The fixed finite pattern selects only the extra nonunit prime. -/
def actualNonunitPattern (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) : ι → Bool :=
  fun i => decide (nonunitFrequencySaving C (p i) (m i) (n i) h)

def secondActiveExponent (m n : ι → ℕ) (pattern : ι → Bool) (i : ι) : ℕ :=
  min (m i) (n i) % 6 + if pattern i then 1 else 0

def secondSixthRootIdeal (p : ι → ExteriorPrime A) (m n : ι → ℕ) : A.Exterior :=
  primePowerProduct p (fun i => min (m i) (n i) / 6)

def secondSixthRootGenerator (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) : A.R :=
  primePowerProductGenerator C p (fun i => min (m i) (n i) / 6)

def secondActiveFrequencyIdeal (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool) : A.Exterior :=
  primePowerProduct p (secondActiveExponent m n pattern)

def secondActiveFrequencyGenerator (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool) : A.R :=
  primePowerProductGenerator C p (secondActiveExponent m n pattern)

theorem secondSixthRootGenerator_generates (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    A.Generates (secondSixthRootIdeal p m n) (secondSixthRootGenerator C p m n) :=
  primePowerProduct_generates C p _

theorem secondActiveFrequencyGenerator_generates
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool) :
    A.Generates (secondActiveFrequencyIdeal p m n pattern)
      (secondActiveFrequencyGenerator C p m n pattern) :=
  primePowerProduct_generates C p _

/-- Exact original element identity, before applying any character. -/
theorem second_extracted_factor_sixth_active
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (h : A.R) :
    primePowerProductGenerator C p (fun i => min (m i) (n i)) *
        nonunitFrequencyGenerator C p m n h =
      secondSixthRootGenerator C p m n ^ 6 *
        secondActiveFrequencyGenerator C p m n (actualNonunitPattern C p m n h) := by
  unfold nonunitFrequencyGenerator secondSixthRootGenerator secondActiveFrequencyGenerator
  rw [← primePowerProductGenerator_add]
  have hexp :
      (fun i => min (m i) (n i) +
        if nonunitFrequencySaving C (p i) (m i) (n i) h then 1 else 0) =
      (fun i => (min (m i) (n i) / 6) * 6 +
        secondActiveExponent m n (actualNonunitPattern C p m n h) i) := by
    funext i
    simp only [secondActiveExponent, actualNonunitPattern, decide_eq_true_eq]
    omega
  rw [hexp, primePowerProductGenerator_add]
  congr 1
  simp only [primePowerProductGenerator, pow_mul, Finset.prod_pow]

/-- Unequal depths disappear from the moving support by the genuine
nonzero-correlation theorem, not an imposed divisibility hypothesis. -/
theorem secondActiveExponent_ne_zero_iff
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (h : A.R) (i : ι) (hm : 0 < m i) (hn : 0 < n i)
    (hne : actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0) :
    secondActiveExponent m n (actualNonunitPattern C p m n h) i ≠ 0 ↔
      unitFrequencySaving C (p i) (m i) (n i) h ∨
        nonunitFrequencySaving C (p i) (m i) (n i) h := by
  simp only [secondActiveExponent, actualNonunitPattern, decide_eq_true_eq]
  constructor
  · intro ha
    by_cases hv : nonunitFrequencySaving C (p i) (m i) (n i) h
    · exact Or.inr hv
    · have hrem : min (m i) (n i) % 6 ≠ 0 := by simpa only [if_neg hv, add_zero] using ha
      have heq : m i = n i := by
        by_contra heq
        exact hrem (Nat.mod_eq_zero_of_dvd
          (actualPrimePowerCorrelation_six_of_ne C (p i) (m i) (n i) h hm hn heq hne))
      left
      apply (actual_unitFrequencySaving_iff C (p i) (m i) (n i) h hne).mpr
      refine ⟨heq, ?_, hv⟩
      intro hsix
      apply hrem
      simpa only [min_eq_left heq.le] using Nat.mod_eq_zero_of_dvd hsix
  · rintro (hu | hv)
    · rw [if_neg (unit_nonunit_frequency_disjoint C (p i) (m i) (n i) h hu),
        add_zero, min_eq_left hu.1.le]
      exact fun hz => hu.2.1 (Nat.dvd_of_mod_eq_zero hz)
    · rw [if_pos hv]
      omega

/-- The original displayed active support is precisely T₂ times V₂.
The disjointness is proved from the original unit/nonunit alternatives. -/
theorem secondActiveFrequencyIdeal_radical
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R)
    (hne : ∀ i, actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0) :
    commonRadical
        (secondActiveFrequencyIdeal p m n (actualNonunitPattern C p m n h)).val
        (secondActiveFrequencyIdeal p m n (actualNonunitPattern C p m n h)).val =
      (unitFrequencyRadical C p m n h).val * (nonunitFrequencyRadical C p m n h).val := by
  rw [secondActiveFrequencyIdeal, commonRadical_primePowerProduct_indicator p hp]
  change (∏ i, (p i).val.asIdeal ^
      (if secondActiveExponent m n (actualNonunitPattern C p m n h) i ≠ 0 then 1 else 0)) =
    (∏ i, (p i).val.asIdeal ^
      (if unitFrequencySaving C (p i) (m i) (n i) h then 1 else 0)) *
    ∏ i, (p i).val.asIdeal ^
      (if nonunitFrequencySaving C (p i) (m i) (n i) h then 1 else 0)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [secondActiveExponent_ne_zero_iff C p m n h i (hm i) (hn i) (hne i)]
  by_cases hu : unitFrequencySaving C (p i) (m i) (n i) h
  · simp [hu, unit_nonunit_frequency_disjoint C (p i) (m i) (n i) h hu]
  · by_cases hv : nonunitFrequencySaving C (p i) (m i) (n i) h <;> simp [hu, hv]

/-- The contraction is the original generated ideal, independently of
the preferred generator used by the complete-row probe. -/
theorem generated_sIntegerModulusContraction (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) :
    sIntegerModulusContraction K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) a = I.val := by
  change (Ideal.span ({a} : Set A.R)).under (𝓞 K) = I.val
  rw [ha.2]
  exact SIntegerLocalization.under_map_exterior A.Sf I.val I.property.2

namespace OriginalMovingFactors

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- The orbit equivalence recovers the supplied element's actual ideal;
there is no compatibility field to assume. -/
theorem factorIdeal_eq_of_generates (D : OriginalMovingFactors A P R)
    (i : Fin D.count) (I : A.Exterior) (ha : A.Generates I (D.element i).val) :
    D.factorIdeal i = I := by
  apply Subtype.ext
  have he := congrArg
    (fun q => (actualSIntegerOrbitIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) q).val)
    (D.decomposition_orbit i)
  rw [decomposedIdealSectorOrbit_ideal] at he
  change (D.decomposition i).1.val.val =
    sIntegerModulusContraction K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (D.element i).val at he
  exact he.trans (generated_sIntegerModulusContraction I (D.element i).val ha)

def singleton (a : NonzeroRingElements A.R) (e : ℤ) : OriginalMovingFactors A P R where
  count := 1
  element _ := a
  power _ := e

theorem singleton_fullIdeal (I : A.Exterior) (a : A.R) (ha : A.Generates I a) (e : ℤ) :
    (singleton (P := P) (R := R) ⟨a, ha.1⟩ e).fullIdeal = I := by
  apply Subtype.ext
  change (∏ i : Fin 1, ((singleton (P := P) (R := R) ⟨a, ha.1⟩ e).factorIdeal i).val) = I.val
  rw [Fin.prod_univ_one]
  exact congrArg Subtype.val
    (factorIdeal_eq_of_generates (singleton (P := P) (R := R) ⟨a, ha.1⟩ e) 0 I ha)

theorem singleton_support (I : A.Exterior) (a : A.R) (ha : A.Generates I a) (e : ℤ) :
    (singleton (P := P) (R := R) ⟨a, ha.1⟩ e).support.val = commonRadical I.val I.val := by
  change commonRadical _ _ = _
  rw [singleton_fullIdeal I a ha e]

/-- Replacing a complete factor product by its displayed radical does
not change any of its coprimality zeros. -/
theorem coprime_support_iff_fullIdeal (D : OriginalMovingFactors A P R)
    (J : Ideal (𝓞 K)) : IsCoprime J D.support.val ↔ IsCoprime J D.fullIdeal.val := by
  rw [coprime_support_iff J D.support.val D.support.property.1,
    coprime_support_iff J D.fullIdeal.val D.fullIdeal.property.1, D.support_primes]

end OriginalMovingFactors

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- One actual factor is enough: its element is the literal active
prime-power product, and its exponent is one. -/
def secondOriginalMovingFactors (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool) :
    OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton
    ⟨secondActiveFrequencyGenerator C p m n pattern,
      (secondActiveFrequencyGenerator_generates C p m n pattern).1⟩ 1

theorem secondOriginalMovingFactors_support
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R)
    (hne : ∀ i, actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0) :
    (secondOriginalMovingFactors P R C p m n (actualNonunitPattern C p m n h)).support.val =
      (unitFrequencyRadical C p m n h).val * (nonunitFrequencyRadical C p m n h).val := by
  rw [secondOriginalMovingFactors,
    OriginalMovingFactors.singleton_support
      (secondActiveFrequencyIdeal p m n (actualNonunitPattern C p m n h))
      (secondActiveFrequencyGenerator C p m n (actualNonunitPattern C p m n h))
      (secondActiveFrequencyGenerator_generates C p m n (actualNonunitPattern C p m n h)) 1]
  exact secondActiveFrequencyIdeal_radical C p hp m n hm hn h hne

/-- The support cost is exactly the two original frequency lengths. -/
theorem secondOriginalMovingFactors_norm
    (C : A.GeneralArithmeticContext σ η hS) (Z : ℝ) (hZ : 1 < Z)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R)
    (hne : ∀ i, actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0) :
    A.exteriorNorm
        (secondOriginalMovingFactors P R C p m n (actualNonunitPattern C p m n h)).support =
      Z ^ (idealLogLength Z (unitFrequencyRadical C p m n h).val +
        idealLogLength Z (nonunitFrequencyRadical C p m n h).val) := by
  change (Ideal.absNorm _ : ℝ) = _
  rw [secondOriginalMovingFactors_support P R C p hp m n hm hn h hne,
    map_mul, Nat.cast_mul, Real.rpow_add (zero_lt_one.trans hZ),
    rpow_idealLogLength Z hZ _ (unitFrequencyRadical C p m n h).property.1,
    rpow_idealLogLength Z hZ _ (nonunitFrequencyRadical C p m n h).property.1]

/-- Equal actual nonunit patterns give literally the same moving list,
including its computed sectors, characters and full displayed support. -/
theorem secondOriginalMovingFactors_pattern_eq
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (h h' : A.R)
    (he : actualNonunitPattern C p m n h = actualNonunitPattern C p m n h') :
    secondOriginalMovingFactors P R C p m n (actualNonunitPattern C p m n h) =
      secondOriginalMovingFactors P R C p m n (actualNonunitPattern C p m n h') := by
  rw [he]

/-- The computed active character has the exact original coefficient,
including fixed-S/6 deletion and every displayed active prime. -/
theorem secondOriginalMovingFactors_evaluation
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool) (J : NonzeroIdeal K) :
    zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
        (secondActiveFrequencyGenerator C p m n pattern) =
      heckeIdealCoefficient K (secondOriginalMovingFactors P R C p m n pattern).character J *
        (if sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J ∧
          IsCoprime J.val (secondOriginalMovingFactors P R C p m n pattern).support.val
        then 1 else 0) := by
  let D := secondOriginalMovingFactors P R C p m n pattern
  let I := secondActiveFrequencyIdeal p m n pattern
  have hg := secondActiveFrequencyGenerator_generates C p m n pattern
  have hchar : D.character = D.factorCharacter 0 := by
    change (∏ i : Fin 1, D.factorCharacter i ^ (1 : ℤ)) = D.factorCharacter 0
    simp only [zpow_one, Fin.prod_univ_one]
  have hI : D.factorIdeal 0 = I := D.factorIdeal_eq_of_generates 0 I hg
  have hfull : D.fullIdeal = I :=
    OriginalMovingFactors.singleton_fullIdeal I _ hg 1
  have hmask :
      decomposedIdealRowMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          (D.decomposition 0).1 J =
        (if sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J ∧
          IsCoprime J.val D.support.val then 1 else 0) := by
    change (if sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J ∧
      IsCoprime J.val (D.factorIdeal 0).val then (1 : ℂ) else 0) = _
    rw [hI, D.coprime_support_iff_fullIdeal J.val, hfull]
  have hd := D.factor_evaluation 0 J
  change zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
      (secondActiveFrequencyGenerator C p m n pattern) =
    heckeIdealCoefficient K (D.factorCharacter 0) J *
      decomposedIdealRowMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (D.decomposition 0).1 J at hd
  rw [← hchar, hmask] at hd
  exact hd

theorem zeroExtendedSexticIdealEvaluation_original_mul
    (J : NonzeroIdeal K) (a b : A.R) :
    zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J (a * b) =
      zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J a *
      zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J b := by
  by_cases hJ : sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J
  · simp only [zeroExtendedSexticIdealEvaluation, dite_eq_left hJ,
      sIntegerSexticIdealEvaluation_mul]
  · simp [zeroExtendedSexticIdealEvaluation, hJ]

/-- The sixth part retains precisely its genuine original deletion.
The numerator need not be a unit of the S-integer ring. -/
theorem zeroExtendedSexticIdealEvaluation_generated_sixth_mul
    (J : NonzeroIdeal K) (I : A.Exterior) (a u : A.R) (ha : A.Generates I a) :
    zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J (a ^ 6 * u) =
      if IsCoprime J.val I.val then
        zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J u else 0 := by
  by_cases hJ : sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J
  · simp only [zeroExtendedSexticIdealEvaluation, dite_eq_left hJ]
    rw [sIntegerSexticIdealEvaluation_mul,
      sIntegerSexticIdealEvaluation_sixth_power_coprime_mask,
      generated_sIntegerModulusContraction I a ha]
    by_cases hc : IsCoprime J.val I.val <;> simp [hc]
  · simp [zeroExtendedSexticIdealEvaluation_eq_zero K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P.arithmetic.root6
      P.arithmetic.primitive6 P.arithmetic.embedding J _ hJ]

/-- Exact source-frequency phase, with the sixth mask still present. -/
theorem second_extracted_factor_evaluation
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (h u : A.R) (J : NonzeroIdeal K) :
    zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
        ((primePowerProductGenerator C p (fun i => min (m i) (n i)) *
          nonunitFrequencyGenerator C p m n h) * u) =
      if IsCoprime J.val (secondSixthRootIdeal p m n).val then
        zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
          (secondActiveFrequencyGenerator C p m n (actualNonunitPattern C p m n h) * u)
      else 0 := by
  rw [second_extracted_factor_sixth_active, mul_assoc]
  exact zeroExtendedSexticIdealEvaluation_generated_sixth_mul P J
    (secondSixthRootIdeal p m n) (secondSixthRootGenerator C p m n) _
    (secondSixthRootGenerator_generates C p m n)

/-- The literal quotient-row coefficient with the computed moving
character.  Both active zeros and sixth-root zeros remain in this identity. -/
theorem second_extracted_factor_character
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (h u : A.R) (J : NonzeroIdeal K) :
    let D := secondOriginalMovingFactors P R C p m n (actualNonunitPattern C p m n h)
    zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J
        ((primePowerProductGenerator C p (fun i => min (m i) (n i)) *
          nonunitFrequencyGenerator C p m n h) * u) =
      if IsCoprime J.val (secondSixthRootIdeal p m n).val then
        heckeIdealCoefficient K D.character J *
          (if sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J ∧
            IsCoprime J.val D.support.val then 1 else 0) *
          zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
            P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J u
      else 0 := by
  dsimp only
  rw [second_extracted_factor_evaluation P C p m n h u J,
    zeroExtendedSexticIdealEvaluation_original_mul P,
    secondOriginalMovingFactors_evaluation P R C p m n]

namespace ActualSecondCorrelationRows

variable {H : Type*} (S : ActualSecondCorrelationRows A σ H ι)

/-- This changes the index type, so a fixed pattern is an identity for
every child source index, including indices outside a finite row set. -/
abbrev NonunitClass (C : A.GeneralArithmeticContext σ η hS) (pattern : ι → Bool) :=
  {h : S.live //
    actualNonunitPattern C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val) = pattern}

theorem factor_sixth_active (C : A.GeneralArithmeticContext σ η hS) (h : H) :
    S.factor C h = secondSixthRootGenerator C S.primes S.leftMultiplicity S.rightMultiplicity ^ 6 *
      secondActiveFrequencyGenerator C S.primes S.leftMultiplicity S.rightMultiplicity
        (actualNonunitPattern C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h)) :=
  second_extracted_factor_sixth_active C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h)

theorem factor_nonunitClass (C : A.GeneralArithmeticContext σ η hS)
    (pattern : ι → Bool) (h : S.NonunitClass C pattern) :
    S.factor C h.val.val =
      secondSixthRootGenerator C S.primes S.leftMultiplicity S.rightMultiplicity ^ 6 *
        secondActiveFrequencyGenerator C S.primes S.leftMultiplicity S.rightMultiplicity pattern := by
  rw [S.factor_sixth_active C h.val.val, h.property]

/-- The local support premises are discharged by the actual live-row
correlation, including its original, possibly noncanonical generators. -/
theorem moving_support_live (C : A.GeneralArithmeticContext σ η hS)
    (hm : ∀ i, 0 < S.leftMultiplicity i) (hn : ∀ i, 0 < S.rightMultiplicity i)
    (h : S.live) :
    (secondOriginalMovingFactors P R C S.primes S.leftMultiplicity S.rightMultiplicity
        (actualNonunitPattern C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val))).support.val =
      (unitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val)).val *
        (nonunitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val)).val :=
  secondOriginalMovingFactors_support P R C S.primes S.primes_injective
    S.leftMultiplicity S.rightMultiplicity hm hn (S.frequency h.val)
    (S.live_local_correlation_nonzero C h)

end ActualSecondCorrelationRows

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.second_extracted_factor_sixth_active
#print axioms HeckeSkeleton.Moments.EngineStep.secondOriginalMovingFactors_support
#print axioms HeckeSkeleton.Moments.EngineStep.secondOriginalMovingFactors_norm
#print axioms HeckeSkeleton.Moments.EngineStep.second_extracted_factor_evaluation
#print axioms HeckeSkeleton.Moments.EngineStep.second_extracted_factor_character
