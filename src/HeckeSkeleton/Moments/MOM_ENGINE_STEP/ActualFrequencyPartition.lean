import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCorrelationBound
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PrimePowerGcd
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualPool
import DedekindZetaZeroFree.Theta.Unfolding.UnitOrbitNormSummability

/-!
# Actual common-frequency extraction

Nonvanishing of the complete correlation forces divisibility by its
genuine common gcd.  Equal nonprincipal depths split into unit and
nonunit divided-frequency primes.  At each nonunit prime one additional
prime power is extracted.  The resulting element and ideal identities
give the exact norm loss used for the new row length.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree LocalFiniteSums
open HeckePort.Moments HeckePort.Moments.CommonSupport

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

local instance partitionPrimePowerFinite (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    Finite (A.R ⧸ Ideal.span {generator C p ^ n}) :=
  LocalFiniteSums.residueFinite C p n

local instance partitionPrimePowerFintype (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    Fintype (A.R ⧸ Ideal.span {generator C p ^ n}) :=
  LocalFiniteSums.residueFintype C p n

theorem actualPrimePowerCorrelation_common_dvd
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (m n : ℕ) (h : A.R) (hne : actualPrimePowerCorrelation C p m n h ≠ 0) :
    generator C p ^ min m n ∣ h := by
  by_contra hnot
  apply hne
  unfold actualPrimePowerCorrelation generatedIdealCorrelation
  exact fullModulusCorrelation_eq_zero_of_common_not_dvd _ _
    (generator C p ^ min m n) h _ _
    (pow_dvd_pow _ (min_le_left _ _)) (pow_dvd_pow _ (min_le_right _ _)) hnot

/-- Nonunit equal-depth frequencies select the extra radical `V₂`. -/
def nonunitFrequencySaving (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (m n : ℕ) (h : A.R) : Prop :=
  m = n ∧ ¬6 ∣ m ∧ generator C p ^ (m + 1) ∣ h

theorem unit_nonunit_frequency_disjoint
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (m n : ℕ) (h : A.R) (hu : unitFrequencySaving C p m n h) :
    ¬nonunitFrequencySaving C p m n h := by
  obtain ⟨_, _, k, hk, hunit⟩ := hu
  intro hv
  apply hunit
  apply (mul_dvd_mul_iff_left (pow_ne_zero m (generator_generates C p).1)).mp
  simpa only [pow_succ, hk] using hv.2.2

/-- On a retained equal nonprincipal row, these are exhaustive and
disjoint alternatives for the original divided frequency. -/
theorem actual_equal_frequency_partition
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (n : ℕ) (hsix : ¬6 ∣ n) (h : A.R)
    (hne : actualPrimePowerCorrelation C p n n h ≠ 0) :
    unitFrequencySaving C p n n h ∨ nonunitFrequencySaving C p n n h := by
  have hd : generator C p ^ n ∣ h := by
    simpa only [min_self] using actualPrimePowerCorrelation_common_dvd C p n n h hne
  obtain ⟨k, hk⟩ := hd
  by_cases hunit : generator C p ∣ k
  · right
    refine ⟨rfl, hsix, ?_⟩
    rw [hk, pow_succ]
    exact mul_dvd_mul_left _ hunit
  · exact Or.inl ⟨rfl, hsix, k, hk, hunit⟩

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual minimum-power product is precisely the ideal gcd. -/
theorem primePowerProduct_min_eq_gcd
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ) :
    (primePowerProduct p (fun i => min (m i) (n i))).val =
      gcd (primePowerProduct p m).val (primePowerProduct p n).val := by
  symm
  exact prime_ideal_power_product_gcd (fun i => (p i).val)
    (fun _ _ he => hp (Subtype.ext he)) m n

theorem primePowerProduct_add (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    (primePowerProduct p (fun i => m i + n i)).val =
      (primePowerProduct p m).val * (primePowerProduct p n).val := by
  change (∏ i, (p i).val.asIdeal ^ (m i + n i)) =
    (∏ i, (p i).val.asIdeal ^ m i) * ∏ i, (p i).val.asIdeal ^ n i
  simp only [pow_add, Finset.prod_mul_distrib]

theorem primePowerProductGenerator_add (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    primePowerProductGenerator C p (fun i => m i + n i) =
      primePowerProductGenerator C p m * primePowerProductGenerator C p n := by
  simp only [primePowerProductGenerator, pow_add, Finset.prod_mul_distrib]

theorem actual_product_correlation_nonzero_local
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ) (h : A.R)
    (hne : generatedIdealCorrelation (σ := σ) (primePowerProduct p m) (primePowerProduct p n)
      (primePowerProductGenerator C p m) (primePowerProductGenerator C p n)
      (primePowerProduct_generates C p m) (primePowerProduct_generates C p n) h ≠ 0)
    (i : ι) : actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0 := by
  have he := actual_prime_power_product_correlation_norm C p hp m n h
  have hprod : (∏ i, ‖actualPrimePowerCorrelation C (p i) (m i) (n i) h‖) ≠ 0 := by
    rw [← he]
    exact norm_ne_zero_iff.mpr hne
  exact norm_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i))

def nonunitFrequencyRadical (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) : A.Exterior :=
  primePowerProduct p (fun i => if nonunitFrequencySaving C (p i) (m i) (n i) h then 1 else 0)

def nonunitFrequencyGenerator (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) : A.R :=
  primePowerProductGenerator C p
    (fun i => if nonunitFrequencySaving C (p i) (m i) (n i) h then 1 else 0)

theorem nonunitFrequencyGenerator_generates (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) :
    A.Generates (nonunitFrequencyRadical C p m n h) (nonunitFrequencyGenerator C p m n h) :=
  primePowerProduct_generates C p _

theorem nonunitFrequencyRadical_squarefree (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ) (h : A.R) :
    Squarefree (nonunitFrequencyRadical C p m n h).val := by
  change Squarefree (∏ i, (p i).val.asIdeal ^
    (if nonunitFrequencySaving C (p i) (m i) (n i) h then 1 else 0))
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    have hpij : (p i).val ≠ (p j).val := fun he => hij (hp (Subtype.ext he))
    exact (((p i).val.isCoprime_of_ne (p j).val hpij).pow).isRelPrime
  · intro i _
    split_ifs
    · simpa only [pow_one] using (p i).val.irreducible.squarefree
    · simp

/-- The full actual correlation forces the product of the true gcd
generator and every selected extra nonunit prime to divide the frequency. -/
theorem actual_product_correlation_frequency_dvd
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ) (h : A.R)
    (hne : generatedIdealCorrelation (σ := σ) (primePowerProduct p m) (primePowerProduct p n)
      (primePowerProductGenerator C p m) (primePowerProductGenerator C p n)
      (primePowerProduct_generates C p m) (primePowerProduct_generates C p n) h ≠ 0) :
    primePowerProductGenerator C p (fun i => min (m i) (n i)) *
      nonunitFrequencyGenerator C p m n h ∣ h := by
  change primePowerProductGenerator C p (fun i => min (m i) (n i)) *
    primePowerProductGenerator C p
      (fun i => if nonunitFrequencySaving C (p i) (m i) (n i) h then 1 else 0) ∣ h
  rw [← primePowerProductGenerator_add]
  change (∏ i, generator C (p i) ^ (min (m i) (n i) +
    if nonunitFrequencySaving C (p i) (m i) (n i) h then 1 else 0)) ∣ h
  apply Fintype.prod_dvd_of_coprime
  · intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp
      (primePowerGenerator_pairwise C p hp
        (fun i => min (m i) (n i) +
          if nonunitFrequencySaving C (p i) (m i) (n i) h then 1 else 0) hij)
  · intro i
    by_cases hv : nonunitFrequencySaving C (p i) (m i) (n i) h
    · rw [if_pos hv]
      simpa only [hv.1, min_self] using hv.2.2
    · rw [if_neg hv, add_zero]
      exact actualPrimePowerCorrelation_common_dvd C (p i) (m i) (n i) h
        (actual_product_correlation_nonzero_local C p hp m n h hne i)

/-- Literal element extraction precedes all absolute estimates. -/
theorem actual_product_correlation_frequency_extract
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ) (h : A.R)
    (hne : generatedIdealCorrelation (σ := σ) (primePowerProduct p m) (primePowerProduct p n)
      (primePowerProductGenerator C p m) (primePowerProductGenerator C p n)
      (primePowerProduct_generates C p m) (primePowerProduct_generates C p n) h ≠ 0) :
    ∃ h' : A.R, h =
      primePowerProductGenerator C p (fun i => min (m i) (n i)) *
        nonunitFrequencyGenerator C p m n h * h' :=
  actual_product_correlation_frequency_dvd C p hp m n h hne

/-- A nonzero generated frequency gives an actual residual exterior ideal
and an exact norm factorization.  No equality with an independently
chosen canonical generator is asserted or required. -/
theorem actual_product_correlation_frequency_ideal_extract
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h)
    (hne : generatedIdealCorrelation (σ := σ) (primePowerProduct p m) (primePowerProduct p n)
      (primePowerProductGenerator C p m) (primePowerProductGenerator C p n)
      (primePowerProduct_generates C p m) (primePowerProduct_generates C p n) h ≠ 0) :
    ∃ h' : A.R, ∃ Ih' : A.Exterior,
      A.Generates Ih' h' ∧
      h = primePowerProductGenerator C p (fun i => min (m i) (n i)) *
        nonunitFrequencyGenerator C p m n h * h' ∧
      Ih.val = gcd (primePowerProduct p m).val (primePowerProduct p n).val *
        (nonunitFrequencyRadical C p m n h).val * Ih'.val ∧
      A.exteriorNorm Ih =
        (Ideal.absNorm (gcd (primePowerProduct p m).val (primePowerProduct p n).val) : ℝ) *
          A.exteriorNorm (nonunitFrequencyRadical C p m n h) * A.exteriorNorm Ih' := by
  obtain ⟨h', hrow⟩ := actual_product_correlation_frequency_extract C p hp m n h hne
  have hh' : h' ≠ 0 := by
    intro hz
    exact hh.1 (by rw [hrow, hz, mul_zero])
  let Ih' := ProbeOrbitNormSum.principalExterior A ⟨h', hh'⟩
  have hgen' : A.Generates Ih' h' := ProbeOrbitNormSum.principalExterior_generates A ⟨h', hh'⟩
  let D := primePowerProduct p (fun i => min (m i) (n i))
  let V := nonunitFrequencyRadical C p m n h
  let d := primePowerProductGenerator C p (fun i => min (m i) (n i))
  let v := nonunitFrequencyGenerator C p m n h
  have hgen : A.Generates (ExteriorIdealEuler.mul (ExteriorIdealEuler.mul D V) Ih') h := by
    rw [hrow]
    exact generated_product (ExteriorIdealEuler.mul D V) Ih' _ rfl (d * v) h'
      (generated_product D V _ rfl d v (primePowerProduct_generates C p _)
        (nonunitFrequencyGenerator_generates C p m n h)) hgen'
  have hideal : Ih.val = gcd (primePowerProduct p m).val (primePowerProduct p n).val *
      V.val * Ih'.val := by
    have he := congrArg Subtype.val (generatedIdeal_unique hh hgen)
    change Ih.val = D.val * V.val * Ih'.val at he
    rwa [primePowerProduct_min_eq_gcd p hp m n] at he
  refine ⟨h', Ih', hgen', hrow, hideal, ?_⟩
  change (Ideal.absNorm Ih.val : ℝ) =
    (Ideal.absNorm (gcd (primePowerProduct p m).val (primePowerProduct p n).val) : ℝ) *
      (Ideal.absNorm V.val : ℝ) * (Ideal.absNorm Ih'.val : ℝ)
  rw [hideal, map_mul, map_mul, Nat.cast_mul, Nat.cast_mul]

end Product

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.primePowerProduct_min_eq_gcd
#print axioms HeckeSkeleton.Moments.EngineStep.actual_product_correlation_frequency_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.actual_product_correlation_frequency_ideal_extract
