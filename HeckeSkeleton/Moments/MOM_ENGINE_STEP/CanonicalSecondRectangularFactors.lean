import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPhaseCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstGaussData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalUnmaskedSecondStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonAtomBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalLogNormLocations
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMovingFactorAppend
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingOriginalArithmeticAtoms

/-!
# Original arithmetic factors in the second rectangles

The first divisor factors are evaluated using the same original allowed
generators and the original reciprocity law.  The active character is
not declared trivial: its prime exponents become the displayed fixed
moving factors of the child.  Both signs are retained, as is the actual
chosen generator of the second empty avoidance mask.

All identities in this file are identities of individual original
columns or their original ideal and prime occurrences.  They precede
the Cartesian product, centering, and every energy estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Active
open HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

namespace CanonicalSecondRectangularFactors

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The full original residue is multiplicative in the frequency on an
exterior ideal.  In particular the empty product has its genuine value. -/
def frequencyHom (I : A.Exterior) : A.R →* ℂ where
  toFun x := actualIdealResidue (A := A) (σ := σ) I.val x
  map_one' := actualIdealResidue_frequency_one I
  map_mul' x y := actualIdealResidue_frequency_mul I.val x y

/-- Multiplicativity in the whole ideal includes the original exterior
zeros, and will be used to distribute one actual phase to every occurrence. -/
def idealPhase (x : A.R) : Ideal (𝓞 K) →* ℂ where
  toFun I := actualIdealResidue (A := A) (σ := σ) I x
  map_one' := actualIdealResidue_one x
  map_mul' I J := actualIdealResidue_ideal_mul I J x

theorem prime_reciprocity
    (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (u : Kˣ) (hu : (u : K) = (a : K)) (hallowed : A.IsAllowed C.correction.B u)
    (p : ExteriorPrime A) (hcop : IsCoprime I.val (primeIdeal p).val) :
    σ (A.sexticResidue (primeIdeal p) a) =
      actualIdealResidue (A := A) (σ := σ) I.val (generator C p) := by
  rw [actualIdealResidue_exterior]
  exact (congrArg σ (C.reciprocity.1 I (primeIdeal p) a (generator C p)
    u (Units.mk0 (generator C p : K) (by exact_mod_cast (generator_generates C p).1))
    ha (generator_generates C p) hu rfl hallowed (generator_allowed C p)
    hcop.sup_eq)).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem active_prime_dvd (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (i : activeSupport Finset.univ m n) :
    (primeIdeal (p i.val)).val ∣ (firstActiveIdeal p m n).val := by
  change (p i.val).val.asIdeal ∣
    ∏ j : activeSupport Finset.univ m n, (p j.val).val.asIdeal ^ 1
  simp only [pow_one]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- The true active character on the original residual generator is
the product of the reciprocal original prime-generator values. -/
theorem active_character_reciprocity
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (u : Kˣ) (hu : (u : K) = (a : K)) (hallowed : A.IsAllowed C.correction.B u)
    (hcop : IsCoprime I.val (firstActiveIdeal p m n).val) :
    actualFirstActiveCharacter C p hp m n (Ideal.Quotient.mk _ a) =
      ∏ i : activeSupport Finset.univ m n,
        actualIdealResidue (A := A) (σ := σ) I.val (generator C (p i.val)) ^
          netExponent (m i.val) (n i.val) := by
  rw [actualFirstActiveCharacter_mk]
  apply Finset.prod_congr rfl
  intro i _
  rw [MulChar.pow_apply' _ (netExponent_ne_zero Finset.univ m n i),
    actual_prime_character_value C,
    prime_reciprocity C I a ha u hu hallowed (p i.val)
      (hcop.of_isCoprime_of_dvd_right (active_prime_dvd p m n i))]

theorem active_generator_residue
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (I : A.Exterior) :
    actualIdealResidue (A := A) (σ := σ) I.val (firstActiveGenerator C p m n) =
      ∏ i : activeSupport Finset.univ m n,
        actualIdealResidue (A := A) (σ := σ) I.val (generator C (p i.val)) := by
  change frequencyHom (σ := σ) I
    (∏ i : activeSupport Finset.univ m n, generator C (p i.val) ^ 1) = _
  simp only [map_prod, map_pow, pow_one, frequencyHom, MonoidHom.coe_mk,
    OneHom.coe_mk]

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

include hΓ in
theorem residue_star (I : A.Exterior) (a : A.R) (ha : A.Generates I a) (x : A.R) :
    star (actualIdealResidue (A := A) (σ := σ) I.val x) =
      (actualIdealResidue (A := A) (σ := σ) I.val x)⁻¹ := by
  letI := finite_sIntegerPrincipalResidue K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) a ha.1
  rw [actualIdealResidue_exterior, ← generatedOriginalColumn_character_mk hΓ I a ha x,
    MulChar.star_apply', MulChar.inv_apply_eq_inv']

include hΓ in
theorem residue_prime_ne_zero
    (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (p : ExteriorPrime A) (hcop : IsCoprime I.val (primeIdeal p).val) :
    actualIdealResidue (A := A) (σ := σ) I.val (generator C p) ≠ 0 := by
  rw [actualIdealResidue_exterior, ← generatedOriginalColumn_character_mk hΓ I a ha]
  apply MulChar.apply_ne_zero_iff.mpr
  exact isUnit_residue_of_coprime a (generator C p)
    (generated_elements_coprime I (primeIdeal p) a (generator C p)
      ha (generator_generates C p) hcop)

/-- The left first-transform factor contributes the actual exponent
`1 + netExponent` at every displayed active prime. -/
theorem first_left_factor
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (u : Kˣ) (hu : (u : K) = (a : K)) (hallowed : A.IsAllowed C.correction.B u)
    (hcop : IsCoprime I.val (firstActiveIdeal p m n).val) (δ : A.R) :
    firstLeftDivisorFactor (generatedOriginalColumn (σ := σ) hΓ I a ha)
        (actualActiveColumn hΓ C p hp m n) δ =
      actualIdealResidue (A := A) (σ := σ) I.val δ *
        ∏ i : activeSupport Finset.univ m n,
          actualIdealResidue (A := A) (σ := σ) I.val (generator C (p i.val)) ^
            (1 + (netExponent (m i.val) (n i.val) : ℤ)) := by
  simp only [firstLeftDivisorFactor, generatedOriginalColumn_character_mk,
    actualActiveColumn_character_mk]
  change (σ (A.sexticResidue I δ) *
    σ (A.sexticResidue I (firstActiveGenerator C p m n))) * _ = _
  rw [← actualIdealResidue_exterior I δ,
    ← actualIdealResidue_exterior I (firstActiveGenerator C p m n),
    active_character_reciprocity C p hp m n I a ha u hu hallowed hcop,
    active_generator_residue, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hz := residue_prime_ne_zero hΓ C I a ha (p i.val)
    (hcop.of_isCoprime_of_dvd_right (active_prime_dvd p m n i))
  rw [zpow_add₀ hz, zpow_one, zpow_natCast]

/-- The right first-transform factor keeps the inverse active phase.
Even a zero displayed exponent does not delete that prime's full mask. -/
theorem first_right_factor
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (u : Kˣ) (hu : (u : K) = (a : K)) (hallowed : A.IsAllowed C.correction.B u)
    (hcop : IsCoprime I.val (firstActiveIdeal p m n).val) (δ : A.R) :
    firstRightDivisorFactor (generatedOriginalColumn (σ := σ) hΓ I a ha)
        (actualActiveColumn hΓ C p hp m n) δ =
      actualIdealResidue (A := A) (σ := σ) I.val δ *
        ∏ i : activeSupport Finset.univ m n,
          actualIdealResidue (A := A) (σ := σ) I.val (generator C (p i.val)) ^
            (1 - (netExponent (m i.val) (n i.val) : ℤ)) := by
  simp only [firstRightDivisorFactor, generatedOriginalColumn_character_mk,
    actualActiveColumn_character_mk]
  change (σ (A.sexticResidue I δ) *
    σ (A.sexticResidue I (firstActiveGenerator C p m n))) * _ = _
  rw [← actualIdealResidue_exterior I δ,
    ← actualIdealResidue_exterior I (firstActiveGenerator C p m n),
    active_character_reciprocity C p hp m n I a ha u hu hallowed hcop,
    active_generator_residue, star_prod, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hz := residue_prime_ne_zero hΓ C I a ha (p i.val)
    (hcop.of_isCoprime_of_dvd_right (active_prime_dvd p m n i))
  rw [star_pow, residue_star hΓ I a ha, zpow_sub₀ hz,
    zpow_one, zpow_natCast, inv_pow, div_eq_mul_inv]

/-- The common-support construction itself proves every residual
column is outside the active support. No column mask is assumed. -/
theorem residual_active_coprimalities
    {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE) :
    (∀ i, IsCoprime (b.leftResidual i).val
      (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val) ∧
    (∀ j, IsCoprime (b.rightResidual j).val
      (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val) := by
  have hs : primeSupport DE.1 = primeSupport DE.2 := by
    rw [← b.common_left, ← b.common_right,
      primePowerProduct_support b.primes b.primes_injective b.leftMultiplicity b.left_positive,
      primePowerProduct_support b.primes b.primes_injective b.rightMultiplicity b.right_positive]
  have h := b.second_coprimalities hs
  have hd := firstActiveIdeal_dvd_common b.primes b.leftMultiplicity
    b.rightMultiplicity b.left_positive
  exact ⟨fun i => (h.1 i).symm.of_isCoprime_of_dvd_right hd,
    fun j => (h.2.2.1 j).symm.of_isCoprime_of_dvd_right hd⟩

/-- The actual inverse mask-generator phase, even for an empty mask.
Its value is never replaced by one merely because its generator is a unit. -/
theorem generated_divisor_phase (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) (δ : A.R) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).divisorPhase δ =
      (idealPhase (σ := σ) δ I.val)⁻¹ := by
  rw [OrbitalGaussColumn.divisorPhase, MulChar.inv_apply_eq_inv',
    generatedOriginalColumn_character_mk]
  exact congrArg Inv.inv (actualIdealResidue_exterior I δ).symm

/-- The full real ideal-norm power is multiplicative, also on zero
ideals. Only actual nonzero exterior ideals enter the later chart. -/
def normPower (δ : ℝ) : Ideal (𝓞 K) →* ℂ where
  toFun I := (((Ideal.absNorm I : ℝ) ^ δ : ℝ) : ℂ)
  map_one' := by simp
  map_mul' I J := by
    simp only [map_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg (Ideal.absNorm I))
        (Nat.cast_nonneg (Ideal.absNorm J)), Complex.ofReal_mul]

/-- The exact multiplicative weight of the second logarithmic chart.
The fixed original unit phase and the full norm tilt occur once each. -/
def secondWeight (δ : ℝ) (ε : A.R) : Ideal (𝓞 K) →* ℂ where
  toFun I := normPower δ I * (idealPhase (σ := σ) ε I)⁻¹
  map_one' := by simp only [map_one, inv_one, one_mul]
  map_mul' I J := by
    simp only [map_mul, mul_inv_rev]
    ring

theorem original_second_coefficient (c : ℂ) (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) (δ : ℝ) (ε : A.R) :
    (c * ((A.exteriorNorm I ^ δ : ℝ) : ℂ)) *
        (generatedOriginalColumn (σ := σ) hΓ I a ha).divisorPhase ε =
      c * secondWeight (σ := σ) δ ε I.val := by
  rw [generated_divisor_phase hΓ]
  change (c * normPower δ I.val) * (idealPhase (σ := σ) ε I.val)⁻¹ =
    c * (normPower δ I.val * (idealPhase (σ := σ) ε I.val)⁻¹)
  exact mul_assoc _ _ _

section Cartesian

variable {k : ℕ}

/-- Every original occurrence receives the same actual multiplicative
ideal factor. Repeated primes and the zero-slot case are covered. -/
theorem rectangle_mul_ideal_weight
    (M : Ideal (𝓞 K) →* ℂ)
    (left right : Ideal (𝓞 K) → ℂ)
    (slot : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) :
    childCartesianCoefficient left right slot i * M (allocationColumnIdeal i) =
      childCartesianCoefficient (fun I => left I * M I) (fun J => right J * M J)
        (fun j p => slot j p * M p.asIdeal) i := by
  simp only [childCartesianCoefficient, allocationColumnIdeal, map_mul, map_prod,
    Finset.prod_mul_distrib]
  ring

/-- The same multiplicative weight acts on both original rectangles;
the complete subtraction stays inside the later Fourier-column norm. -/
theorem centered_rectangle_mul_ideal_weight
    (M : Ideal (𝓞 K) →* ℂ)
    (left right comparisonLeft comparisonRight : Ideal (𝓞 K) → ℂ)
    (slot : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) :
    (childCartesianCoefficient left right slot i -
      childCartesianCoefficient comparisonLeft comparisonRight slot i) *
        M (allocationColumnIdeal i) =
      childCartesianCoefficient (fun I => left I * M I) (fun J => right J * M J)
        (fun j p => slot j p * M p.asIdeal) i -
      childCartesianCoefficient (fun I => comparisonLeft I * M I)
        (fun J => comparisonRight J * M J) (fun j p => slot j p * M p.asIdeal) i := by
  rw [sub_mul, rectangle_mul_ideal_weight, rectangle_mul_ideal_weight]

/-- The trivial ray parameter has the actual unit value on either side.
This does not assert that an arithmetic mask-generator phase is trivial. -/
theorem punit_phase (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
    (x : PUnit) : (side.phase PUnit χ x : ℂ) = 1 := by
  have hx : x = 1 := Subsingleton.elim _ _
  simp only [hx, map_one, Circle.coe_one]

end Cartesian

theorem unramified_zpow {χ : HeckeCharacter K} {p : HeightOneSpectrum (𝓞 K)}
    (hχ : UnramifiedAt K χ p) (n : ℤ) : UnramifiedAt K (χ ^ n) p := by
  cases n with
  | ofNat n => simpa only [zpow_natCast] using hχ.pow K n
  | negSucc n => simpa only [zpow_negSucc] using (hχ.pow K (n + 1)).inv K

theorem coefficient_pow (χ : HeckeCharacter K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hχ : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K χ p)
    (n : ℕ) : heckeIdealCoefficient K (χ ^ n) I = heckeIdealCoefficient K χ I ^ n := by
  induction n with
  | zero => simp only [pow_zero, CanonicalOriginalPhaseCalibration.coefficient_one]
  | succ n ih =>
    rw [pow_succ, CanonicalOriginalPhaseCalibration.coefficient_mul_right_unramified
      (χ ^ n) χ I hχ, ih, pow_succ]

theorem coefficient_inv (χ : HeckeCharacter K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hχ : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K χ p) :
    heckeIdealCoefficient K χ⁻¹ I = (heckeIdealCoefficient K χ I)⁻¹ := by
  have h := CanonicalOriginalPhaseCalibration.coefficient_mul_right_unramified
    χ χ⁻¹ I (fun p hp => (hχ p hp).inv K)
  rw [mul_inv_cancel, CanonicalOriginalPhaseCalibration.coefficient_one] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

theorem coefficient_zpow (χ : HeckeCharacter K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hχ : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K χ p)
    (n : ℤ) : heckeIdealCoefficient K (χ ^ n) I = heckeIdealCoefficient K χ I ^ n := by
  cases n with
  | ofNat n => simpa only [zpow_natCast] using coefficient_pow χ I hχ n
  | negSucc n =>
    simp only [zpow_negSucc]
    rw [coefficient_inv (χ ^ (n + 1)) I (fun p hp => (hχ p hp).pow K (n + 1)),
      coefficient_pow χ I hχ]

theorem coefficient_prod {J : Type*} (s : Finset J) (χ : J → HeckeCharacter K)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hχ : ∀ j ∈ s, ∀ p : HeightOneSpectrum (𝓞 K),
      p.asIdeal ∣ I.val → UnramifiedAt K (χ j) p) :
    heckeIdealCoefficient K (∏ j ∈ s, χ j) I =
      ∏ j ∈ s, heckeIdealCoefficient K (χ j) I := by
  revert hχ
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty, CanonicalOriginalPhaseCalibration.coefficient_one]
  | @insert j s hj ih =>
    intro hχ
    have hs : ∀ i ∈ s, ∀ p : HeightOneSpectrum (𝓞 K),
        p.asIdeal ∣ I.val → UnramifiedAt K (χ i) p :=
      fun i hi p hp => hχ i (Finset.mem_insert_of_mem hi) p hp
    rw [Finset.prod_insert hj, Finset.prod_insert hj,
      CanonicalOriginalPhaseCalibration.coefficient_mul_right_unramified
        (χ j) (∏ i ∈ s, χ i) I
        (fun p hp => UnramifiedAt.finset_prod K s χ p (fun i hi => hs i hi p hp)),
      ih hs]

end CanonicalSecondRectangularFactors

namespace OriginalMovingFactors

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (D : OriginalMovingFactors A P R)

/-- The displayed actual elements and integer exponents, before any
character replacement or cancellation of their displayed support. -/
def residueValue (I : Ideal (𝓞 K)) : ℂ :=
  ∏ i, actualIdealResidue (A := A) (σ := σ) I (D.element i).val ^ D.power i

def residueHom : Ideal (𝓞 K) →* ℂ where
  toFun := D.residueValue (σ := σ)
  map_one' := by
    simp only [residueValue, actualIdealResidue_one, one_zpow, Finset.prod_const_one]
  map_mul' I J := by
    simp only [residueValue, actualIdealResidue_ideal_mul, mul_zpow, Finset.prod_mul_distrib]

theorem append_residueValue (E : OriginalMovingFactors A P R) (I : Ideal (𝓞 K)) :
    (D.append E).residueValue (σ := σ) I =
      D.residueValue (σ := σ) I * E.residueValue (σ := σ) I := by
  change (∏ i : Fin (D.count + E.count),
    actualIdealResidue (A := A) (σ := σ) I ((D.append E).element i).val ^
      (D.append E).power i) =
    (∏ i, actualIdealResidue (A := A) (σ := σ) I (D.element i).val ^ D.power i) *
      ∏ i, actualIdealResidue (A := A) (σ := σ) I (E.element i).val ^ E.power i
  rw [Fin.prod_univ_add]
  simp only [append_element_left, append_element_right, append_power_left, append_power_right]

theorem factor_generates (i : Fin D.count) :
    A.Generates (D.factorIdeal i) (D.element i).val := by
  have hg := originalFrequencyIdeal_generates (D.element i).val (D.element i).property
  rw [D.factorIdeal_eq_of_generates i (originalFrequencyIdeal (D.element i).val) hg]
  exact hg

theorem factorIdeal_dvd (i : Fin D.count) : (D.factorIdeal i).val ∣ D.fullIdeal.val := by
  change (D.factorIdeal i).val ∣ ∏ j, (D.factorIdeal j).val
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem factor_evaluation_of_coprime (i : Fin D.count) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I)
    (hcop : IsCoprime I.val (D.factorIdeal i).val) :
    HeckeGeneral.Analysis.SquarefreeAmplification.zeroExtendedSexticIdealEvaluation K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P.arithmetic.root6
        P.arithmetic.primitive6 P.arithmetic.embedding I (D.element i).val =
      heckeIdealCoefficient K (D.factorCharacter i) I := by
  have h := D.factor_evaluation i I
  change HeckeGeneral.Analysis.SquarefreeAmplification.zeroExtendedSexticIdealEvaluation K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P.arithmetic.root6
      P.arithmetic.primitive6 P.arithmetic.embedding I (D.element i).val =
    heckeIdealCoefficient K (D.factorCharacter i) I *
      (if HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I ∧
        IsCoprime I.val (D.factorIdeal i).val then 1 else 0) at h
  simpa only [hI, hcop, and_self, if_true, mul_one] using h

/-- The original zero extension kills an actual factor sharing a prime
with the column. This statement also applies when its primitive
character alone has a smaller conductor. -/
theorem factor_residue_zero_of_not_coprime
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (i : Fin D.count) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hcop : ¬IsCoprime I.val (D.factorIdeal i).val) :
    actualIdealResidue (A := A) (σ := σ) I.val (D.element i).val = 0 := by
  rw [CanonicalOriginalPhaseCalibration.residue_eq_probe_evaluation P hroot hemb]
  have h := D.factor_evaluation i I
  change HeckeGeneral.Analysis.SquarefreeAmplification.zeroExtendedSexticIdealEvaluation K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P.arithmetic.root6
      P.arithmetic.primitive6 P.arithmetic.embedding I (D.element i).val =
    heckeIdealCoefficient K (D.factorCharacter i) I *
      (if HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I ∧
        IsCoprime I.val (D.factorIdeal i).val then 1 else 0) at h
  simpa only [hcop, and_false, if_false, mul_zero] using h

/-- Nonvanishing of the original symbol proves unramifiedness of each
computed factor character away from its actual full ideal. -/
theorem factorCharacter_unramified (i : Fin D.count)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal (D.factorIdeal i).val) :
    UnramifiedAt K (D.factorCharacter i) p := by
  by_contra hram
  have houtside := CanonicalOriginalPhaseCalibration.outside_prime P p hp
  have hne := CanonicalOriginalPhaseCalibration.original_evaluation_ne_zero P
    (D.factorIdeal i) (D.element i).val (D.factor_generates i)
    (CanonicalOriginalPhaseCalibration.primeIdeal p) houtside hcop
  rw [D.factor_evaluation_of_coprime i _ houtside hcop,
    CanonicalOriginalPhaseCalibration.coefficient_prime,
    primeCoefficient_of_ramified K (D.factorCharacter i) p hram] at hne
  exact hne rfl

theorem character_unramified (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal D.support.val) : UnramifiedAt K D.character p := by
  apply UnramifiedAt.finset_prod K Finset.univ _ p
  intro i _
  exact CanonicalSecondRectangularFactors.unramified_zpow
    (D.factorCharacter_unramified i p hp
      (((D.coprime_support_iff_fullIdeal p.asIdeal).mp hcop).
        of_isCoprime_of_dvd_right (D.factorIdeal_dvd i))) (D.power i)

/-- The actual moving coefficient is its displayed original residue
product on the complete live mask. All local hypotheses are proved
from the original factor ideals; none is a supplied dictionary. -/
theorem character_coefficient_of_coprime
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I)
    (hcop : IsCoprime I.val D.support.val) :
    heckeIdealCoefficient K D.character I = D.residueValue (σ := σ) I.val := by
  have hfull := (D.coprime_support_iff_fullIdeal I.val).mp hcop
  have hfactor (i : Fin D.count) : IsCoprime I.val (D.factorIdeal i).val :=
    hfull.of_isCoprime_of_dvd_right (D.factorIdeal_dvd i)
  have hu (i : Fin D.count) (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I.val) :
      UnramifiedAt K (D.factorCharacter i) p :=
    D.factorCharacter_unramified i p (hI p hp).1
      ((hfactor i).of_isCoprime_of_dvd_left hp)
  rw [character, CanonicalSecondRectangularFactors.coefficient_prod Finset.univ _ I
    (fun i _ p hp => CanonicalSecondRectangularFactors.unramified_zpow (hu i p hp) _)]
  unfold residueValue
  apply Finset.prod_congr rfl
  intro i _
  rw [CanonicalSecondRectangularFactors.coefficient_zpow _ I (hu i)]
  congr 1
  rw [CanonicalOriginalPhaseCalibration.residue_eq_probe_evaluation P hroot hemb]
  exact (D.factor_evaluation_of_coprime i I hI (hfactor i)).symm

/-- The original fixed background may be ramified. Only the computed
moving factors are split, on their already proved full live mask. -/
theorem background_coefficient_of_coprime
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (background : HeckeCharacter K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I)
    (hcop : IsCoprime I.val D.support.val) :
    heckeIdealCoefficient K (background * D.character) I =
      heckeIdealCoefficient K background I * D.residueValue (σ := σ) I.val := by
  rw [CanonicalOriginalPhaseCalibration.coefficient_mul_right_unramified
    background D.character I (fun p hp => D.character_unramified p (hI p hp).1
      (hcop.of_isCoprime_of_dvd_left hp)),
    D.character_coefficient_of_coprime hroot hemb I hI hcop]

/-- Coefficient factorization with the complete displayed moving mask.
The extra zero is explicit until a subsequent original-symbol identity
shows that it was already present. -/
theorem background_coefficient_masked
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (background : HeckeCharacter K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I) :
    heckeIdealCoefficient K (background * D.character) I *
        (if IsCoprime I.val D.support.val then (1 : ℂ) else 0) =
      heckeIdealCoefficient K background I * D.residueValue (σ := σ) I.val *
        (if IsCoprime I.val D.support.val then (1 : ℂ) else 0) := by
  by_cases hcop : IsCoprime I.val D.support.val
  · simp only [if_pos hcop, mul_one]
    exact D.background_coefficient_of_coprime hroot hemb background I hI hcop
  · simp only [if_neg hcop, mul_zero]

end OriginalMovingFactors

namespace CanonicalSecondRectangularFactors

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original active prime generators are recorded individually.
Both signs use the same displayed list, including exponent zero. -/
def firstActiveMovingFactors (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool) :
    OriginalMovingFactors A P R where
  count := Fintype.card (activeSupport Finset.univ m n)
  element i :=
    ⟨generator C (p ((Fintype.equivFin (activeSupport Finset.univ m n)).symm i).val),
      (generator_generates C _).1⟩
  power i :=
    let j := ((Fintype.equivFin (activeSupport Finset.univ m n)).symm i).val
    if right then 1 - (netExponent (m j) (n j) : ℤ)
      else 1 + (netExponent (m j) (n j) : ℤ)

theorem firstActiveMovingFactors_residue
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool) (I : Ideal (𝓞 K)) :
    (firstActiveMovingFactors P R C p m n right).residueValue (σ := σ) I =
      ∏ i : activeSupport Finset.univ m n,
        actualIdealResidue (A := A) (σ := σ) I (generator C (p i.val)) ^
          (if right then 1 - (netExponent (m i.val) (n i.val) : ℤ)
           else 1 + (netExponent (m i.val) (n i.val) : ℤ)) := by
  exact Fintype.prod_equiv (Fintype.equivFin (activeSupport Finset.univ m n)).symm
    _ _ (fun _ => rfl)

theorem firstActiveMovingFactors_fullIdeal
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool) :
    (firstActiveMovingFactors P R C p m n right).fullIdeal = firstActiveIdeal p m n := by
  let D := firstActiveMovingFactors P R C p m n right
  have hf (i : Fin D.count) : D.factorIdeal i =
      primeIdeal (p ((Fintype.equivFin (activeSupport Finset.univ m n)).symm i).val) :=
    D.factorIdeal_eq_of_generates i _ (generator_generates C _)
  apply Subtype.ext
  change (∏ i : Fin D.count, (D.factorIdeal i).val) =
    ∏ i : activeSupport Finset.univ m n, (p i.val).val.asIdeal ^ 1
  simp only [hf, pow_one]
  exact Fintype.prod_equiv (Fintype.equivFin (activeSupport Finset.univ m n)).symm
    _ _ (fun _ => rfl)

/-- The literal first physical mask generator precedes the original
active list. It is not replaced by an independently selected element. -/
def firstMovingFactors (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
    (δ : NonzeroRingElements A.R) : OriginalMovingFactors A P R :=
  (OriginalMovingFactors.singleton δ 1).append (firstActiveMovingFactors P R C p m n right)

theorem firstMovingFactors_residue
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
    (δ : NonzeroRingElements A.R) (I : Ideal (𝓞 K)) :
    (firstMovingFactors P R C p m n right δ).residueValue (σ := σ) I =
      actualIdealResidue (A := A) (σ := σ) I δ.val *
        ∏ i : activeSupport Finset.univ m n,
          actualIdealResidue (A := A) (σ := σ) I (generator C (p i.val)) ^
            (if right then 1 - (netExponent (m i.val) (n i.val) : ℤ)
             else 1 + (netExponent (m i.val) (n i.val) : ℤ)) := by
  rw [firstMovingFactors, OriginalMovingFactors.append_residueValue,
    firstActiveMovingFactors_residue]
  congr 1
  simp only [OriginalMovingFactors.residueValue, OriginalMovingFactors.singleton,
    Fin.prod_univ_one, zpow_one]

theorem firstMovingFactors_fullIdeal
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
    (Iδ : A.Exterior) (δ : A.R) (hδ : A.Generates Iδ δ) :
    (firstMovingFactors P R C p m n right ⟨δ, hδ.1⟩).fullIdeal =
      ExteriorIdealEuler.mul Iδ (firstActiveIdeal p m n) := by
  rw [firstMovingFactors, OriginalMovingFactors.append_fullIdeal,
    OriginalMovingFactors.singleton_fullIdeal Iδ δ hδ,
    firstActiveMovingFactors_fullIdeal]

theorem firstMovingFactors_coprime_support_iff
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
    (δ : NonzeroRingElements A.R) (Iδ : A.Exterior) (hδ : A.Generates Iδ δ.val)
    (I : Ideal (𝓞 K)) (hactive : IsCoprime I (firstActiveIdeal p m n).val) :
    IsCoprime I (firstMovingFactors P R C p m n right δ).support.val ↔
      IsCoprime I Iδ.val := by
  rw [(firstMovingFactors P R C p m n right δ).coprime_support_iff_fullIdeal I,
    firstMovingFactors_fullIdeal P R C p m n right Iδ δ.val hδ]
  change IsCoprime I (Iδ.val * (firstActiveIdeal p m n).val) ↔ _
  rw [IsCoprime.mul_right_iff]
  simp only [hactive, and_true]

/-- The first physical mask zero is already in the actual divisor
factor. The active factors, including any zero exponent, are coprime
to each original residual occurrence. -/
theorem firstMovingFactors_residue_mask
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
    (δ : NonzeroRingElements A.R) (Iδ : A.Exterior) (hδ : A.Generates Iδ δ.val)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hactive : IsCoprime I.val (firstActiveIdeal p m n).val) :
    (firstMovingFactors P R C p m n right δ).residueValue (σ := σ) I.val *
        (if IsCoprime I.val (firstMovingFactors P R C p m n right δ).support.val
          then (1 : ℂ) else 0) =
      (firstMovingFactors P R C p m n right δ).residueValue (σ := σ) I.val := by
  by_cases hcop : IsCoprime I.val Iδ.val
  · have hs := (firstMovingFactors_coprime_support_iff P R C p m n right
      δ Iδ hδ I.val hactive).mpr hcop
    simp only [if_pos hs, mul_one]
  · let D : OriginalMovingFactors A P R := OriginalMovingFactors.singleton δ 1
    have he : D.factorIdeal 0 = Iδ := D.factorIdeal_eq_of_generates 0 Iδ hδ
    have hz : actualIdealResidue (A := A) (σ := σ) I.val δ.val = 0 :=
      D.factor_residue_zero_of_not_coprime hroot hemb 0 I (by simpa only [he] using hcop)
    rw [firstMovingFactors_residue P R C p m n right δ I.val, hz]
    simp only [zero_mul]

/-- The original first multiplier is absorbed into the computed fixed
moving character with all physical mask zeros retained. The background
may be ramified; no multiplicativity of two ramified characters is used. -/
theorem firstMovingFactors_masked_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (right : Bool)
    (δ : NonzeroRingElements A.R) (Iδ : A.Exterior) (hδ : A.Generates Iδ δ.val)
    (background : HeckeCharacter K) (oldMask : HeckeGeneral.Analysis.NonzeroIdeal K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I)
    (hactive : IsCoprime I.val (firstActiveIdeal p m n).val) :
    heckeIdealCoefficient K
        (background * (firstMovingFactors P R C p m n right δ).character) I *
        (if IsCoprime I.val
            (oldMask.val * (firstMovingFactors P R C p m n right δ).support.val)
          then (1 : ℂ) else 0) =
      (heckeIdealCoefficient K background I *
        (if IsCoprime I.val oldMask.val then (1 : ℂ) else 0)) *
          (firstMovingFactors P R C p m n right δ).residueValue (σ := σ) I.val := by
  by_cases hm : IsCoprime I.val oldMask.val
  · simp only [IsCoprime.mul_right_iff, hm, true_and, if_true, mul_one]
    rw [(firstMovingFactors P R C p m n right δ).
      background_coefficient_masked hroot hemb background I hI,
      mul_assoc, firstMovingFactors_residue_mask P R hroot hemb C p m n right
        δ Iδ hδ I hactive]
  · simp only [IsCoprime.mul_right_iff, hm, false_and, if_false, mul_zero, zero_mul]

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

theorem first_left_factor_moving
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (u : Kˣ) (hu : (u : K) = (a : K)) (hallowed : A.IsAllowed C.correction.B u)
    (hcop : IsCoprime I.val (firstActiveIdeal p m n).val)
    (δ : NonzeroRingElements A.R) :
    firstLeftDivisorFactor (generatedOriginalColumn (σ := σ) hΓ I a ha)
        (actualActiveColumn hΓ C p hp m n) δ.val =
      (firstMovingFactors P R C p m n false δ).residueValue (σ := σ) I.val := by
  simpa only [firstMovingFactors_residue, Bool.false_eq_true, if_false] using
    first_left_factor hΓ C p hp m n I a ha u hu hallowed hcop δ.val

theorem first_right_factor_moving
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (u : Kˣ) (hu : (u : K) = (a : K)) (hallowed : A.IsAllowed C.correction.B u)
    (hcop : IsCoprime I.val (firstActiveIdeal p m n).val)
    (δ : NonzeroRingElements A.R) :
    firstRightDivisorFactor (generatedOriginalColumn (σ := σ) hΓ I a ha)
        (actualActiveColumn hΓ C p hp m n) δ.val =
      (firstMovingFactors P R C p m n true δ).residueValue (σ := σ) I.val := by
  simpa only [firstMovingFactors_residue, if_true] using
    first_right_factor hΓ C p hp m n I a ha u hu hallowed hcop δ.val

/-- The canonical original block supplies the allowed residual generator
and its actual coprimality with the active support. Neither is a new
input to the moving factorization. -/
theorem canonical_first_left_factor_moving
    (C : A.GeneralArithmeticContext σ η hS)
    {α β : Type*} (left : Finset α) (right : Finset β)
    (fullI : α → A.Exterior) (fullJ : β → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right
      (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (δ : NonzeroRingElements A.R) (i : α) :
    let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
    firstLeftDivisorFactor
        (generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i)
          (b.leftGenerator i) (b.left_generates i))
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity) δ.val =
      (firstMovingFactors P R C b.primes b.leftMultiplicity b.rightMultiplicity false δ).
        residueValue (σ := σ) (b.leftResidual i).val := by
  let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
  obtain ⟨u, hu, ha⟩ :=
    (canonicalFirstCommonBlock_allowed C left right fullI fullJ DE hDE).1 i
  exact first_left_factor_moving P R hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity (b.leftResidual i)
    (b.leftGenerator i) (b.left_generates i) u hu ha
    ((residual_active_coprimalities b).1 i) δ

theorem canonical_first_right_factor_moving
    (C : A.GeneralArithmeticContext σ η hS)
    {α β : Type*} (left : Finset α) (right : Finset β)
    (fullI : α → A.Exterior) (fullJ : β → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right
      (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (δ : NonzeroRingElements A.R) (j : β) :
    let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
    firstRightDivisorFactor
        (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j)
          (b.rightGenerator j) (b.right_generates j))
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity) δ.val =
      (firstMovingFactors P R C b.primes b.leftMultiplicity b.rightMultiplicity true δ).
        residueValue (σ := σ) (b.rightResidual j).val := by
  let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
  obtain ⟨u, hu, ha⟩ :=
    (canonicalFirstCommonBlock_allowed C left right fullI fullJ DE hDE).2 j
  exact first_right_factor_moving P R hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity (b.rightResidual j)
    (b.rightGenerator j) (b.right_generates j) u hu ha
    ((residual_active_coprimalities b).2 j) δ

/-- The second divisor phase uses the actual inverse chosen unit.
Keeping it as an original factor records the exact fixed arithmetic. -/
def secondMaskMovingFactors (ε : NonzeroRingElements A.R) : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton ε (-1)

theorem secondMaskMovingFactors_residue (ε : NonzeroRingElements A.R)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).divisorPhase ε.val =
      (secondMaskMovingFactors P R ε).residueValue (σ := σ) I.val := by
  rw [generated_divisor_phase hΓ]
  simp only [secondMaskMovingFactors, OriginalMovingFactors.residueValue,
    OriginalMovingFactors.singleton, Fin.prod_univ_one, zpow_neg_one, idealPhase,
    MonoidHom.coe_mk, OneHom.coe_mk]

variable [IsPrincipalIdealRing A.R]

theorem empty_mask_generator_generates :
    A.Generates (unitExterior A)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅).val := by
  refine ⟨(sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅).property, ?_⟩
  rw [← (unitExterior_generates A).2, Ideal.span_singleton_one,
    Ideal.span_singleton_eq_top]
  exact isUnit_iff_dvd_one.mpr (empty_mask_generator_dvd_one A.Sf)

/-- The actual empty-mask phase has no displayed ideal cost, although
its finite unit character has not been replaced by the trivial character. -/
theorem second_empty_mask_fullIdeal :
    (secondMaskMovingFactors P R
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)).fullIdeal =
      unitExterior A := by
  exact OriginalMovingFactors.singleton_fullIdeal (unitExterior A) _
    empty_mask_generator_generates (-1)

theorem second_empty_mask_support :
    (secondMaskMovingFactors P R
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)).support =
      unitExterior A := by
  apply Subtype.ext
  change CommonSupportMass.commonRadical _ _ = (unitExterior A).val
  rw [second_empty_mask_fullIdeal]
  simp [CommonSupportMass.commonRadical, unitExterior,
    HeckePort.IdealMobiusDivisorSum.primeSupport]

end CanonicalSecondRectangularFactors

namespace CompleteMovingRowRecipe

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)

private theorem original_plain_coefficient (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainCoefficient
        (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id).plain
        (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id).plainTwist
        (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id).mask I =
      (Q.arithmeticAtoms ξ).leftArithmetic I := by
  simp only [CanonicalOriginalPhaseCalibration.sourceCharacters, sourcePlainCoefficient,
    CanonicalOriginalPhaseCalibration.coefficient_one, mul_one,
    CanonicalOriginalPhaseCalibration.originalCoprimeMask,
    arithmeticAtoms, completeIdealFixedTwistArithmeticAtoms,
    MonoidHom.coe_mk, OneHom.coe_mk]

private theorem original_prime_coefficient
    (i : Fin (data ξ).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) :
    sourcePrimeCoefficient
        ((CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id).slot i)
        ((CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id).slotTwist i)
        (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id).mask p =
      (Q.arithmeticAtoms ξ).primeArithmetic i p := by
  simp only [CanonicalOriginalPhaseCalibration.sourceCharacters, sourcePrimeCoefficient,
    primeCoefficient_one, mul_one, id_eq,
    CanonicalOriginalPhaseCalibration.originalCoprimeMask,
    arithmeticAtoms, completeIdealFixedTwistArithmeticAtoms,
    MonoidHom.coe_mk, OneHom.coe_mk]

variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin (data ξ).geometry.slotCount → Finset (HeightOneSpectrum (𝓞 K)))

/-- The exact original per-occurrence table, built from the same
computed parent atoms. No new arithmetic identification is a field. -/
def originalTermDictionary (comparison : Bool) :
    SecondCoefficientTermDictionary
      (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
        (Q.correction * Q.moving.character) Q.arithmeticMask id)
      (side.phase PUnit χ) S₁ S₂ S where
  leftAtom I := ((Q.arithmeticAtoms ξ).constantAtoms W a Z t).leftValue
    (if comparison then Y₁ else Z ^ a.n₁) (sourceMomentIdeal I)
  rightAtom I := ((Q.arithmeticAtoms ξ).constantAtoms W a Z t).rightValue
    (if comparison then Y₂ else Z ^ a.n₂) (sourceMomentIdeal I)
  slotAtom := ((Q.arithmeticAtoms ξ).constantAtoms W a Z t).primeValue
  leftRay _ := PUnit.unit
  rightRay _ := PUnit.unit
  slotRay _ _ := PUnit.unit
  scale₁ := if comparison then Y₁ else Z ^ a.n₁
  scale₂ := if comparison then Y₂ else Z ^ a.n₂
  base := Z
  length i := ((data ξ).geometry.slots i).length
  leftWeight I := W.left PUnit.unit t
    (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁))
  rightWeight I := W.right PUnit.unit t
    (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂))
  slotWeight i p := ((data ξ).geometry.slots i).profile t
    ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots i).length)
  plain₁ I _ := by
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one,
      Q.original_plain_coefficient ξ] <;> rfl
  plain₂ I _ := by
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one,
      Q.original_plain_coefficient ξ] <;> rfl
  prime i p _ := by
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one,
      Q.original_prime_coefficient ξ] <;> rfl

/-- It is literally the original rectangle before the first transform,
evaluated at the actual Cartesian ideal and prime occurrences. -/
theorem originalTermDictionary_coefficient (comparison : Bool)
    (i : AllocationColumn K (data ξ).geometry.slotCount) :
    (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S comparison).coefficient i =
      (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).rectangle comparison
        ((sourceMomentIdeal i.1.1, sourceMomentIdeal i.1.2), i.2) := rfl

theorem originalTermDictionary_bare (comparison : Bool)
    (i : AllocationColumn K (data ξ).geometry.slotCount)
    (hi : i ∈ childCartesianColumns S₁ S₂ S) :
    (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S comparison).coefficient i =
      rawBareSourceCoefficient
        (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
          (Q.correction * Q.moving.character) Q.arithmeticMask id)
        (if comparison then Y₁ else Z ^ a.n₁) (if comparison then Y₂ else Z ^ a.n₂)
        Z (fun j => ((data ξ).geometry.slots j).length)
        (fun I => W.left PUnit.unit t (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁)))
        (fun I => W.right PUnit.unit t (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂)))
        (fun j p => ((data ξ).geometry.slots j).profile t
          ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots j).length)) i := by
  have h := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S comparison).
    coefficient_phase i hi
  simpa only [CanonicalSecondRectangularFactors.punit_phase, mul_one] using h

/-- Both comparison scales use the same original characters, prime
occurrences and finite-ray labels. Only the two plain tests change. -/
def originalComparison : SecondCoefficientComparison
    (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S false) where
  leftAtom := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true).leftAtom
  rightAtom := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true).rightAtom
  scale₁ := Y₁
  scale₂ := Y₂
  leftWeight := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true).leftWeight
  rightWeight := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true).rightWeight
  plain₁ := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true).plain₁
  plain₂ := (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true).plain₂

@[simp] theorem originalComparison_dictionary :
    (Q.originalComparison ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S).dictionary =
      Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S true := rfl

/-- The original whole centered coefficient is an output of the two
single-atom dictionaries. There is one shared additional normalizer. -/
theorem originalComparison_centeredCoefficient (u v : ℂ)
    (w : Fin (data ξ).geometry.slotCount → ℂ)
    (i : AllocationColumn K (data ξ).geometry.slotCount) :
    (Q.originalComparison ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S).centeredCoefficient u v w i =
      SecondCoefficientTermDictionary.centralNormalizer u v w *
        (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient true
          ((sourceMomentIdeal i.1.1, sourceMomentIdeal i.1.2), i.2) := by
  rw [SecondCoefficientComparison.centeredCoefficient,
    SecondCoefficientTermDictionary.normalizedCoefficient_eq,
    Q.originalComparison_dictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S,
    SecondCoefficientTermDictionary.normalizedCoefficient_eq,
    Q.originalTermDictionary_coefficient ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S,
    Q.originalTermDictionary_coefficient ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S]
  change _ - _ = _ * (_ - _)
  ring

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ S support)

/-- The common scalar consists of the original two extracted ideals
and the actual frozen prime occurrences. It is shared by the main and
comparison scales. -/
def originalCommonScalar : ℂ :=
  b.bareCommonScalar
    (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
      (Q.correction * Q.moving.character) Q.arithmeticMask id)
    Z (fun j => ((data ξ).geometry.slots j).length)
    (fun j p => ((data ξ).geometry.slots j).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots j).length))

/-- The residual coefficient uses exactly the selected original slot
indices and the original tests evaluated at the reconstructed ideals. -/
def originalResidualCoefficient (comparison : Bool) :
    AllocationColumn K b.keep.card → ℂ :=
  b.bareResidualCoefficient
    (CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
      (Q.correction * Q.moving.character) Q.arithmeticMask id)
    (if comparison then Y₁ else Z ^ a.n₁) (if comparison then Y₂ else Z ^ a.n₂)
    Z (fun j => ((data ξ).geometry.slots j).length)
    (fun I => W.left PUnit.unit t
      (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁)))
    (fun I => W.right PUnit.unit t
      (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂)))
    (fun j p => ((data ξ).geometry.slots j).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots j).length))

/-- Common extraction is an identity of the actual computed parent
coefficient, with no new coefficient factorization premise. -/
theorem originalTermDictionary_extract (comparison : Bool)
    (y : AllocationColumn K b.keep.card) (hy : y ∈ b.residualColumns) :
    (Q.originalTermDictionary ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S comparison).
        coefficient (b.reconstruct y) =
      Q.originalCommonScalar ξ Z t S₁ S₂ S b *
        Q.originalResidualCoefficient ξ W a Z t Y₁ Y₂ S₁ S₂ S b comparison y := by
  rw [Q.originalTermDictionary_bare ξ W a Z t Y₁ Y₂ side χ S₁ S₂ S comparison
    (b.reconstruct y) (b.original_subset (b.reconstruct_mem y hy))]
  exact b.raw_bare_extract _ _ _ _ _ _ _ _ y hy

/-- The complete original subtraction has one common extracted scalar.
Both residual rectangles retain the same actual prime slots. -/
theorem original_centered_extract
    (y : AllocationColumn K b.keep.card) (hy : y ∈ b.residualColumns) :
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient true
        ((sourceMomentIdeal (b.reconstruct y).1.1,
          sourceMomentIdeal (b.reconstruct y).1.2), (b.reconstruct y).2) =
      Q.originalCommonScalar ξ Z t S₁ S₂ S b *
        (Q.originalResidualCoefficient ξ W a Z t Y₁ Y₂ S₁ S₂ S b false y -
          Q.originalResidualCoefficient ξ W a Z t Y₁ Y₂ S₁ S₂ S b true y) := by
  change _ - _ = _
  rw [← Q.originalTermDictionary_coefficient ξ W a Z t Y₁ Y₂ .left 1 S₁ S₂ S false,
    ← Q.originalTermDictionary_coefficient ξ W a Z t Y₁ Y₂ .left 1 S₁ S₂ S true,
    Q.originalTermDictionary_extract ξ W a Z t Y₁ Y₂ .left 1 S₁ S₂ S b false y hy,
    Q.originalTermDictionary_extract ξ W a Z t Y₁ Y₂ .left 1 S₁ S₂ S b true y hy,
    mul_sub]

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondRectangularFactors.first_left_factor
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondRectangularFactors.first_right_factor
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.character_coefficient_of_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondRectangularFactors.firstMovingFactors_masked_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondRectangularFactors.canonical_first_left_factor_moving
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondRectangularFactors.canonical_first_right_factor_moving
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondRectangularFactors.second_empty_mask_support
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.originalTermDictionary
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.original_centered_extract
