import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCharacterSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPhaseCalibration

/-!
# The genuine fixed phases of the first left and right columns

The first transform's divisor factor is not a trivial finite phase.
Allowed-generator reciprocity converts its active-character values
one prime at a time into the original residue symbol of one fixed
nonzero element.  The right side uses the complementary positive
exponents, so nonunit zeros are preserved as well as unit values.

These fixed elements precede the second row and both Fourier variables.
Their literal singleton moving recipes can therefore be appended to
the original moving list before the second active factor is appended.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open LocalFiniteSumCompatibility
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments.Active

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

namespace CanonicalLiteralFirstPhase

variable (C : A.GeneralArithmeticContext σ η hS)

private theorem prime_reciprocity
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : K) (by exact_mod_cast ha.1)))
    (p : ExteriorPrime A) :
    σ (A.sexticResidue (primeIdeal p) a) =
      σ (A.sexticResidue I (generator C p)) := by
  by_cases hcop : IsCoprime I.val (primeIdeal p).val
  · exact (congrArg σ (C.reciprocity.1 I (primeIdeal p) a (generator C p)
      (Units.mk0 (a : K) (by exact_mod_cast ha.1))
      (Units.mk0 (generator C p : K) (by exact_mod_cast (generator_generates C p).1))
      ha (generator_generates C p) rfl rfl haAllowed (generator_allowed C p)
      hcop.sup_eq)).symm
  · have hz := ArithmeticContext.actual_sextic_noncoprime_vanishing
      A I (primeIdeal p) a (generator C p) ha (generator_generates C p)
      (fun he => hcop (Ideal.isCoprime_iff_sup_eq.mpr he))
    rw [hz.1, hz.2]

private theorem prime_power_star (p : ExteriorPrime A) (e : ℕ)
    (he : 0 < e) (he6 : e < 6)
    (x : A.R ⧸ A.extendIdeal (primeIdeal p)) :
    star ((chi (σ := σ) p ^ e) x) =
      chi (σ := σ) p x ^ (6 - e) := by
  letI : Finite (A.R ⧸ A.extendIdeal (primeIdeal p)) := A.exteriorResidue_finite _
  have h6 : chi (σ := σ) p ^ 6 = 1 := by
    simpa only [chi_exact_order] using pow_orderOf_eq_one (chi (σ := σ) p)
  have hinv : chi (σ := σ) p ^ (6 - e) = (chi (σ := σ) p ^ e)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, Nat.sub_add_cancel he6.le, h6]
  rw [MulChar.star_apply', ← hinv,
    MulChar.pow_apply' _ (Nat.sub_pos_of_lt he6).ne']

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def leftExponent (m n : ι → ℕ) (i : activeSupport Finset.univ m n) : ℕ :=
  1 + netExponent (m i.val) (n i.val)

def rightExponent (m n : ι → ℕ) (i : activeSupport Finset.univ m n) : ℕ :=
  1 + (6 - netExponent (m i.val) (n i.val))

theorem rightExponent_eq (m n : ι → ℕ) (i : activeSupport Finset.univ m n) :
    rightExponent m n i = 7 - netExponent (m i.val) (n i.val) := by
  have he := netExponent_lt_six (m i.val) (n i.val)
  unfold rightExponent
  omega

def leftElement (p : ι → ExteriorPrime A) (m n : ι → ℕ) (δ : A.R) : A.R :=
  δ * primePowerProductGenerator C (firstActivePrimes p m n) (leftExponent m n)

def rightElement (p : ι → ExteriorPrime A) (m n : ι → ℕ) (δ : A.R) : A.R :=
  δ * primePowerProductGenerator C (firstActivePrimes p m n) (rightExponent m n)

theorem active_value
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : K) (by exact_mod_cast ha.1))) :
    (actualActiveColumn hΓ C p hp m n).character (Ideal.Quotient.mk _ a) =
      ∏ i : activeSupport Finset.univ m n,
        (generatedOriginalColumn (σ := σ) hΓ I a ha).character
          (Ideal.Quotient.mk _ (generator C (p i.val))) ^
            netExponent (m i.val) (n i.val) := by
  rw [actualActiveColumn_character_mk, actualFirstActiveCharacter_mk]
  apply Finset.prod_congr rfl
  intro i _
  rw [MulChar.pow_apply' _ (netExponent_ne_zero Finset.univ m n i),
    actual_prime_character_value C,
    prime_reciprocity C I a ha haAllowed,
    generatedOriginalColumn_character_mk]

theorem active_star_value
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : K) (by exact_mod_cast ha.1))) :
    star ((actualActiveColumn hΓ C p hp m n).character (Ideal.Quotient.mk _ a)) =
      ∏ i : activeSupport Finset.univ m n,
        (generatedOriginalColumn (σ := σ) hΓ I a ha).character
          (Ideal.Quotient.mk _ (generator C (p i.val))) ^
            (6 - netExponent (m i.val) (n i.val)) := by
  rw [actualActiveColumn_character_mk, actualFirstActiveCharacter_mk, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [prime_power_star (p i.val) _
    (Nat.pos_of_ne_zero (netExponent_ne_zero Finset.univ m n i))
    (netExponent_lt_six (m i.val) (n i.val)),
    actual_prime_character_value C,
    prime_reciprocity C I a ha haAllowed,
    generatedOriginalColumn_character_mk]

/-- The actual first left phase, including all its original zeros. -/
theorem leftDivisorFactor
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : K) (by exact_mod_cast ha.1))) (δ : A.R) :
    firstLeftDivisorFactor (generatedOriginalColumn (σ := σ) hΓ I a ha)
      (actualActiveColumn hΓ C p hp m n) δ =
      actualIdealResidue (A := A) (σ := σ) I.val (leftElement C p m n δ) := by
  rw [actualIdealResidue_exterior,
    ← generatedOriginalColumn_character_mk hΓ I a ha]
  unfold firstLeftDivisorFactor
  rw [active_value hΓ C p hp m n I a ha haAllowed]
  change
    ((generatedOriginalColumn (σ := σ) hΓ I a ha).character (Ideal.Quotient.mk _ δ) *
      (generatedOriginalColumn (σ := σ) hΓ I a ha).character
        (Ideal.Quotient.mk _ (firstActiveGenerator C p m n))) * _ = _
  simp only [leftElement, firstActiveGenerator, primePowerProductGenerator,
    firstActivePrimes, leftExponent, map_mul, map_prod, map_pow,
    pow_one, pow_add, Finset.prod_mul_distrib]
  ring

/-- The actual first right phase uses positive complementary
exponents. No inverse of a possibly zero value is introduced. -/
theorem rightDivisorFactor
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : K) (by exact_mod_cast ha.1))) (δ : A.R) :
    firstRightDivisorFactor (generatedOriginalColumn (σ := σ) hΓ I a ha)
      (actualActiveColumn hΓ C p hp m n) δ =
      actualIdealResidue (A := A) (σ := σ) I.val (rightElement C p m n δ) := by
  rw [actualIdealResidue_exterior,
    ← generatedOriginalColumn_character_mk hΓ I a ha]
  unfold firstRightDivisorFactor
  rw [active_star_value hΓ C p hp m n I a ha haAllowed]
  change
    ((generatedOriginalColumn (σ := σ) hΓ I a ha).character (Ideal.Quotient.mk _ δ) *
      (generatedOriginalColumn (σ := σ) hΓ I a ha).character
        (Ideal.Quotient.mk _ (firstActiveGenerator C p m n))) * _ = _
  simp only [rightElement, firstActiveGenerator, primePowerProductGenerator,
    firstActivePrimes, rightExponent, map_mul, map_prod, map_pow,
    pow_one, pow_add, Finset.prod_mul_distrib]
  ring

def leftIdeal (p : ι → ExteriorPrime A) (m n : ι → ℕ) (D : A.Exterior) : A.Exterior :=
  ExteriorIdealEuler.mul D (primePowerProduct (firstActivePrimes p m n) (leftExponent m n))

def rightIdeal (p : ι → ExteriorPrime A) (m n : ι → ℕ) (D : A.Exterior) : A.Exterior :=
  ExteriorIdealEuler.mul D (primePowerProduct (firstActivePrimes p m n) (rightExponent m n))

theorem leftElement_generates (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    A.Generates (leftIdeal p m n D) (leftElement C p m n δ) :=
  generated_product D (primePowerProduct (firstActivePrimes p m n) (leftExponent m n))
    (leftIdeal p m n D) rfl δ _ hδ (primePowerProduct_generates C _ _)

theorem rightElement_generates (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    A.Generates (rightIdeal p m n D) (rightElement C p m n δ) :=
  generated_product D (primePowerProduct (firstActivePrimes p m n) (rightExponent m n))
    (rightIdeal p m n D) rfl δ _ hδ (primePowerProduct_generates C _ _)

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- The first fixed factor is computed from its original element;
its sector and finite character are the existing canonical dictionary. -/
def leftMoving (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton
    ⟨leftElement C p m n δ, (leftElement_generates C p m n D δ hδ).1⟩ 1

def rightMoving (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton
    ⟨rightElement C p m n δ, (rightElement_generates C p m n D δ hδ).1⟩ 1

@[simp] theorem leftMoving_support (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    (leftMoving C P R p m n D δ hδ).support.val =
      CommonSupportMass.commonRadical (leftIdeal p m n D).val (leftIdeal p m n D).val :=
  OriginalMovingFactors.singleton_support _ _ (leftElement_generates C p m n D δ hδ) 1

@[simp] theorem rightMoving_support (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    (rightMoving C P R p m n D δ hδ).support.val =
      CommonSupportMass.commonRadical (rightIdeal p m n D).val (rightIdeal p m n D).val :=
  OriginalMovingFactors.singleton_support _ _ (rightElement_generates C p m n D δ hδ) 1

/-- The fixed element supplies its own finite character and its full
zero-extended mask.  In particular the source does not assume that
this newly computed moving character belongs to the original theta. -/
theorem singleton_evaluation (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J a =
      heckeIdealCoefficient K
          (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).character J *
        (if sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J ∧
          IsCoprime J.val I.val then 1 else 0) := by
  let D := OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1
  have hchar : D.character = D.factorCharacter 0 := by
    change (∏ i : Fin 1, D.factorCharacter i ^ (1 : ℤ)) = D.factorCharacter 0
    simp only [zpow_one, Fin.prod_univ_one]
  have hI : D.factorIdeal 0 = I := D.factorIdeal_eq_of_generates 0 I ha
  have he := D.factor_evaluation 0 J
  change zeroExtendedSexticIdealEvaluation K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P.arithmetic.root6
      P.arithmetic.primitive6 P.arithmetic.embedding J a =
    heckeIdealCoefficient K (D.factorCharacter 0) J *
      (if sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J ∧
        IsCoprime J.val (D.factorIdeal 0).val then 1 else 0) at he
  rw [← hchar, hI] at he
  exact he

theorem singleton_unramified
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal I.val) :
    UnramifiedAt K
      (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).character p := by
  by_contra hram
  have hne := CanonicalOriginalPhaseCalibration.original_evaluation_ne_zero
    P I a ha (CanonicalOriginalPhaseCalibration.primeIdeal p)
    (CanonicalOriginalPhaseCalibration.outside_prime P p hp) hcop
  have he := singleton_evaluation P R I a ha
    (CanonicalOriginalPhaseCalibration.primeIdeal p)
  simp only [CanonicalOriginalPhaseCalibration.outside_prime P p hp,
    hcop, and_self, if_true, mul_one] at he
  rw [he, CanonicalOriginalPhaseCalibration.coefficient_prime,
    primeCoefficient_of_ramified K _ p hram] at hne
  exact hne rfl

/-- The background is allowed to ramify.  Only the actual fixed moving
character is proved unramified on the nonzero part of its own mask. -/
theorem multiply_singleton_residue
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (χ : HeckeCharacter K) (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    heckeIdealCoefficient K χ J * actualIdealResidue (A := A) (σ := σ) J.val a =
      heckeIdealCoefficient K
          (χ * (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).character) J *
        (if sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J ∧
          IsCoprime J.val I.val then 1 else 0) := by
  rw [CanonicalOriginalPhaseCalibration.residue_eq_probe_evaluation P hroot hemb,
    singleton_evaluation P R I a ha J]
  by_cases hgood : sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J ∧
      IsCoprime J.val I.val
  · rw [if_pos hgood, mul_one, mul_one,
      CanonicalOriginalPhaseCalibration.coefficient_mul_right_unramified]
    intro p hp
    exact singleton_unramified P R I a ha p (hgood.1 p hp).1
      (hgood.2.of_isCoprime_of_dvd_left hp)
  · simp only [if_neg hgood, mul_zero]

theorem leftDivisorFactor_euler
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I D : A.Exterior) (a δ : A.R) (ha : A.Generates I a) (hδ : A.Generates D δ)
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : K) (by exact_mod_cast ha.1))) (χ : HeckeCharacter K) :
    heckeIdealCoefficient K χ (exteriorMomentIdeal I) *
        firstLeftDivisorFactor (generatedOriginalColumn (σ := σ) hΓ I a ha)
          (actualActiveColumn hΓ C p hp m n) δ =
      heckeIdealCoefficient K (χ * (leftMoving C P R p m n D δ hδ).character)
          (exteriorMomentIdeal I) *
        (if IsCoprime I.val (leftIdeal p m n D).val then 1 else 0) := by
  rw [leftDivisorFactor hΓ C p hp m n I a ha haAllowed δ]
  have he := multiply_singleton_residue P R hroot hemb
    (leftIdeal p m n D) (leftElement C p m n δ)
    (leftElement_generates C p m n D δ hδ) χ (exteriorMomentIdeal I)
  have hout : sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (exteriorMomentIdeal I) :=
    (CanonicalOriginalPhaseCalibration.outside_iff_coprime (exteriorMomentIdeal I)).mpr
      (Ideal.isCoprime_iff_sup_eq.mpr I.property.2)
  simpa only [hout, true_and] using he

theorem rightDivisorFactor_euler
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (I D : A.Exterior) (a δ : A.R) (ha : A.Generates I a) (hδ : A.Generates D δ)
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : K) (by exact_mod_cast ha.1))) (χ : HeckeCharacter K) :
    heckeIdealCoefficient K χ (exteriorMomentIdeal I) *
        firstRightDivisorFactor (generatedOriginalColumn (σ := σ) hΓ I a ha)
          (actualActiveColumn hΓ C p hp m n) δ =
      heckeIdealCoefficient K (χ * (rightMoving C P R p m n D δ hδ).character)
          (exteriorMomentIdeal I) *
        (if IsCoprime I.val (rightIdeal p m n D).val then 1 else 0) := by
  rw [rightDivisorFactor hΓ C p hp m n I a ha haAllowed δ]
  have he := multiply_singleton_residue P R hroot hemb
    (rightIdeal p m n D) (rightElement C p m n δ)
    (rightElement_generates C p m n D δ hδ) χ (exteriorMomentIdeal I)
  have hout : sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (exteriorMomentIdeal I) :=
    (CanonicalOriginalPhaseCalibration.outside_iff_coprime (exteriorMomentIdeal I)).mpr
      (Ideal.isCoprime_iff_sup_eq.mpr I.property.2)
  simpa only [hout, true_and] using he

end CanonicalLiteralFirstPhase
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFirstPhase.leftDivisorFactor
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFirstPhase.rightDivisorFactor
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFirstPhase.leftMoving
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFirstPhase.rightMoving
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFirstPhase.leftDivisorFactor_euler
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFirstPhase.rightDivisorFactor_euler
