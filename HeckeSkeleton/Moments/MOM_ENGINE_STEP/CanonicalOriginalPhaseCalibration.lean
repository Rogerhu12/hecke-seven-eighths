import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualMovingFrequencyFactors
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildSectors
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalChildData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfiles
import HeckeAxiom.SexticSymbolDictionary

/-!
# Original residue phases in the constructed complete child data

The two residue libraries are identified on the same original arithmetic
data.  Complete-row and active-factor characters are unramified away from
their actual displayed masks, as follows from their nonzero original
sextic coefficients.  Euler-coefficient multiplication is used only there;
the background may retain arbitrary ramification and its original zeros.

The fixed correction is placed in the fixed source characters.  The
remaining finite-ray twist is the original trivial character, whose actual
membership in theta is required.  Every original deletion is preserved:
the old column mask, the sixth-root mask, the displayed active support,
and the complete residual ideal all occur in the child common mask.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalOriginalPhaseCalibration

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

def primeIdeal (p : HeightOneSpectrum (𝓞 K)) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩

@[simp] theorem coefficient_prime (χ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K)) :
    heckeIdealCoefficient K χ (primeIdeal p) = primeCoefficient K χ p :=
  idealCoefficient_prime (primeCoefficient K χ) p

theorem coefficient_one (I : HeckeGeneral.Analysis.NonzeroIdeal K) : heckeIdealCoefficient K 1 I = 1 := by
  have hp (Q : Ideal (𝓞 K)) : primeIdealValue (primeCoefficient K 1) Q = 1 := by
    unfold primeIdealValue
    split_ifs <;> simp only [primeCoefficient_one]
  simp only [heckeIdealCoefficient, nonzeroIdealCoefficient, idealCoefficient,
    ite_eq_right (nonZeroDivisors.coe_ne_zero I)]
  rw [show primeIdealValue (primeCoefficient K (1 : HeckeCharacter K)) =
    (fun _ => 1) from funext hp]
  simp only [Multiset.map_const, Multiset.prod_replicate, one_pow]

/-- The right character need only be unramified at the actual prime
divisors of this complete ideal. -/
theorem coefficient_mul_right_unramified (ψ χ : HeckeCharacter K) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hχ : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K χ p) :
    heckeIdealCoefficient K (ψ * χ) I =
      heckeIdealCoefficient K ψ I * heckeIdealCoefficient K χ I := by
  have hmap :
      (normalizedFactors I.val).map (primeIdealValue (primeCoefficient K (ψ * χ))) =
        (normalizedFactors I.val).map
          (fun Q => primeIdealValue (primeCoefficient K ψ) Q *
            primeIdealValue (primeCoefficient K χ) Q) := by
    apply Multiset.map_congr rfl
    intro Q hQ
    have hp := prime_of_normalized_factor Q hQ
    have hd : Q ∣ I.val := dvd_of_mem_normalizedFactors hQ
    have he := primeCoefficient_mul_right_unramified K ψ χ
      (HeightOneSpectrum.ofPrime hp) (hχ (HeightOneSpectrum.ofPrime hp) hd)
    simpa only [primeIdealValue, dif_pos hp] using he
  simp only [heckeIdealCoefficient, nonzeroIdealCoefficient, idealCoefficient,
    ite_eq_right (nonZeroDivisors.coe_ne_zero I)]
  rw [hmap, Multiset.prod_map_mul]

theorem outside_iff_coprime (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I ↔
      IsCoprime I.val A.cS := by
  constructor
  · intro hI
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact (HeckeAxiom.sup_cS_eq_top_iff A I.val (nonZeroDivisors.coe_ne_zero I)).mpr
      (fun p hp => (hI p hp).1)
  · intro hI p hp
    have hS := (HeckeAxiom.sup_cS_eq_top_iff A I.val
      (nonZeroDivisors.coe_ne_zero I)).mp (Ideal.isCoprime_iff_sup_eq.mp hI) p hp
    exact ⟨hS, HeckeAxiom.six_not_mem A p hS⟩

/-- This is the original normalized residue family, including the
fixed exceptional zeros, not an independently calibrated phase. -/
theorem residue_eq_original_evaluation (I : HeckeGeneral.Analysis.NonzeroIdeal K) (a : A.R) :
    actualIdealResidue (A := A) (σ := σ) I.val a =
      zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (A.zeta12 ^ 2) (HeckeAxiom.zeta12_sq_primitive A) σ I a := by
  by_cases hI : IsCoprime I.val A.cS
  · rw [actualIdealResidue, dif_pos ⟨nonZeroDivisors.coe_ne_zero I, hI⟩,
      zeroExtendedSexticIdealEvaluation, dif_pos ((outside_iff_coprime I).mpr hI)]
    exact (HeckeAxiom.sexticIdealEvaluation_eq_sexticResidue A σ
      ⟨I.val, nonZeroDivisors.coe_ne_zero I, Ideal.isCoprime_iff_sup_eq.mp hI⟩ a _ _ _).symm
  · have hbad : ¬sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I :=
      fun h => hI ((outside_iff_coprime I).mp h)
    simp only [actualIdealResidue, dif_neg (fun h => hI h.2),
      zeroExtendedSexticIdealEvaluation, dif_neg hbad]

/-- The original twelfth root proves the negative-frequency phase
identity, including all nonunit zeros. -/
theorem residue_neg (I : Ideal (𝓞 K)) (a : A.R) :
    actualIdealResidue (A := A) (σ := σ) I (-a) =
      actualIdealResidue (A := A) (σ := σ) I a := by
  by_cases hI : I ≠ 0 ∧ IsCoprime I A.cS
  · have hone : actualIdealResidue (A := A) (σ := σ) I (-1) = 1 := by
      rw [actualIdealResidue, dif_pos hI, A.sexticResidue_neg_one, map_one]
    rw [neg_eq_neg_one_mul, actualIdealResidue_frequency_mul, hone, one_mul]
  · simp only [actualIdealResidue, dif_neg hI]

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- Only the two literal original arithmetic fields are needed for the
phase dictionary. They are reflexive for the same ArithmeticChoice. -/
theorem residue_eq_probe_evaluation
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ) (I : HeckeGeneral.Analysis.NonzeroIdeal K) (a : A.R) :
    actualIdealResidue (A := A) (σ := σ) I.val a =
      zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding I a := by
  simpa only [hroot, hemb] using
    (residue_eq_original_evaluation (A := A) (σ := σ) I a)

theorem original_evaluation_ne_zero (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hJ : sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J)
    (hcop : IsCoprime J.val I.val) :
    zeroExtendedSexticIdealEvaluation K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding J a ≠ 0 := by
  have hone : zeroExtendedSexticIdealEvaluation K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P.arithmetic.root6
      P.arithmetic.primitive6 P.arithmetic.embedding J 1 = 1 := by
    simp only [zeroExtendedSexticIdealEvaluation, dif_pos hJ,
      sIntegerSexticIdealEvaluation_one]
  have hsix := zeroExtendedSexticIdealEvaluation_generated_sixth_mul P J I a 1 ha
  rw [mul_one, if_pos hcop, hone] at hsix
  intro hz
  rw [pow_succ' a 5, zeroExtendedSexticIdealEvaluation_original_mul P, hz, zero_mul] at hsix
  exact zero_ne_one hsix

theorem outside_prime (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :
    sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (primeIdeal p) := by
  intro q hq
  have he : p = q := HeightOneSpectrum.ext
    (p.isPrime.isMaximal p.ne_bot |>.eq_of_le q.isPrime.ne_top (Ideal.le_of_dvd hq))
  subst q
  exact ⟨hp, P.arithmetic.away_six p hp⟩

private theorem unramified_of_original_evaluation
    (χ : HeckeCharacter K) (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal I.val)
    (he : zeroExtendedSexticIdealEvaluation K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P.arithmetic.root6
      P.arithmetic.primitive6 P.arithmetic.embedding (primeIdeal p) a =
      heckeIdealCoefficient K χ (primeIdeal p)) :
    UnramifiedAt K χ p := by
  by_contra hram
  have hne := original_evaluation_ne_zero P I a ha (primeIdeal p) (outside_prime P p hp) hcop
  rw [he, coefficient_prime, primeCoefficient_of_ramified K χ p hram] at hne
  exact hne rfl

variable {Ih : A.Exterior} {h g : A.R} {factor : ℝ}

theorem residualCharacter_unramified (row : ActualChildRow Ih h g factor)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal row.ideal.val) :
    UnramifiedAt K
      (completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P R (row.sector P) row.momentIdeal) p := by
  apply unramified_of_original_evaluation P _ row.ideal row.element row.generates p hp hcop
  have he := row.orbit_evaluation P R (primeIdeal p)
  change zeroExtendedSexticIdealEvaluation K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P.arithmetic.root6
      P.arithmetic.primitive6 P.arithmetic.embedding (primeIdeal p) row.element = _ at he
  simpa only [decomposedIdealRowMask, outside_prime P p hp, hcop, and_self,
    if_true, mul_one] using he

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem activeCharacter_unramified (C : A.GeneralArithmeticContext σ η hS)
    (primes : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal
      (secondOriginalMovingFactors P R C primes m n pattern).support.val) :
    UnramifiedAt K (secondOriginalMovingFactors P R C primes m n pattern).character p := by
  let D := secondOriginalMovingFactors P R C primes m n pattern
  let I := secondActiveFrequencyIdeal primes m n pattern
  have hg := secondActiveFrequencyGenerator_generates C primes m n pattern
  have hfull : D.fullIdeal = I :=
    OriginalMovingFactors.singleton_fullIdeal I _ hg 1
  have hcopI : IsCoprime p.asIdeal I.val := by
    rw [← hfull]
    exact (D.coprime_support_iff_fullIdeal p.asIdeal).mp hcop
  apply unramified_of_original_evaluation P D.character I _ hg p hp hcopI
  have he := secondOriginalMovingFactors_evaluation P R C primes m n pattern (primeIdeal p)
  simpa only [outside_prime P p hp, hcop, and_self, if_true, mul_one] using he

/-- The old fixed column deletion as a literal multiplicative mask. -/
def originalCoprimeMask (M : HeckeGeneral.Analysis.NonzeroIdeal K) : Ideal (𝓞 K) →* ℂ where
  toFun I := if IsCoprime I M.val then 1 else 0
  map_one' := by simp
  map_mul' I J := by
    rw [IsCoprime.mul_left_iff]
    by_cases hI : IsCoprime I M.val <;>
      by_cases hJ : IsCoprime J M.val <;> simp [hI, hJ]

def phaseMask (u : HeckeGeneral.Analysis.NonzeroIdeal K) (moving : Ideal (𝓞 K))
    (root : A.Exterior) (J : HeckeGeneral.Analysis.NonzeroIdeal K) : Prop :=
  sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J ∧
    IsCoprime J.val u.val ∧ IsCoprime J.val moving ∧ IsCoprime J.val root.val

/-- The original common factor and the actual quotient element produce
exactly the two computed characters with their complete common mask. -/
theorem extracted_residue_character
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hsector : row.sector P = ν) (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    actualIdealResidue (A := A) (σ := σ) J.val g *
        actualIdealResidue (A := A) (σ := σ) J.val row.element =
      heckeIdealCoefficient K (secondOriginalMovingFactors P R C primes m n pattern).character J *
        heckeIdealCoefficient K
          (completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
            P R ν row.momentIdeal) J *
        (if phaseMask row.momentIdeal
          (secondOriginalMovingFactors P R C primes m n pattern).support.val
          (secondSixthRootIdeal primes m n) J then 1 else 0) := by
  rw [← actualIdealResidue_frequency_mul, residue_eq_probe_evaluation P hroot hemb,
    hfactor, mul_assoc, zeroExtendedSexticIdealEvaluation_generated_sixth_mul P J
      (secondSixthRootIdeal primes m n) (secondSixthRootGenerator C primes m n) _
      (secondSixthRootGenerator_generates C primes m n),
    zeroExtendedSexticIdealEvaluation_original_mul P,
    secondOriginalMovingFactors_evaluation P R C primes m n pattern]
  have he := row.orbit_evaluation P R J
  change zeroExtendedSexticIdealEvaluation K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P.arithmetic.root6
      P.arithmetic.primitive6 P.arithmetic.embedding J row.element = _ at he
  rw [hsector] at he
  rw [he]
  by_cases hJ : sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) J <;>
    by_cases hu : IsCoprime J.val row.ideal.val <;>
    by_cases hm : IsCoprime J.val
      (secondOriginalMovingFactors P R C primes m n pattern).support.val <;>
    by_cases hs : IsCoprime J.val (secondSixthRootIdeal primes m n).val <;>
    simp [phaseMask, decomposedIdealRowMask, ActualChildRow.momentIdeal,
      exteriorMomentIdeal, hJ, hu, hm, hs, mul_assoc]

variable {ω ψ : HeckeCharacter K}

/-- The actual fixed correction is included in the source characters;
this preserves their ramification zeros without an unramified-background
hypothesis. The finite-ray character itself is the original one. -/
def sourceCharacters (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
    (oldMask : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ}
    (index : Fin k → Fin parent.geometry.slotCount) : FixedChildCharacters K k where
  plain := parent.plainBackground * correction
  slot i := parent.slotCoefficient (index i) * correction
  plainTwist := 1
  slotTwist _ := 1
  mask := originalCoprimeMask oldMask
  fixedRay := {1}
  plainTwist_mem := Finset.mem_singleton_self 1
  slotTwist_mem _ := Finset.mem_singleton_self 1

@[simp] theorem sourceCharacters_restrictSlots
    (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
    (oldMask : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ} (index : Fin k → Fin parent.geometry.slotCount)
    (keep : Finset (Fin k)) :
    (sourceCharacters parent correction oldMask index).restrictSlots keep =
      sourceCharacters parent correction oldMask
        (fun i => index (SlotRestriction.index keep i)) := rfl

def childData (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
    (hcorr : correction ∈ parent.theta)
    (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (oldMask : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
    (inverse left right : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount) : MomentData K ω ψ :=
  CanonicalOriginalChildData.data parent (secondOriginalMovingFactors P R C primes m n pattern)
    correction (Or.inr hcorr) (fun _ => ν)
    (oldMask * exteriorMomentIdeal (secondSixthRootIdeal primes m n)) budget
    inverse left right geometry index

variable (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
variable (hcorr : correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
variable (m n : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (oldMask : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
variable (inverse left right : IdealTest K) (geometry : SlotGeometry K)
variable (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)

theorem childData_mask (u J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    maskValue (childData P R parent correction hcorr C primes m n pattern ν oldMask budget
        inverse left right geometry index) u J.val =
      (if phaseMask u (secondOriginalMovingFactors P R C primes m n pattern).support.val
          (secondSixthRootIdeal primes m n) J ∧ IsCoprime J.val oldMask.val then 1 else 0) := by
  change (if ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u J.val &&
      decide (IsCoprime J.val (secondOriginalMovingFactors P R C primes m n pattern).support.val)) &&
      decide (IsCoprime J.val (oldMask.val * (secondSixthRootIdeal primes m n).val)))
      then (1 : ℂ) else 0) = _
  simp only [completeIdealCommonMask, phaseMask, sexticIdealOutsideS,
    Bool.and_eq_true, decide_eq_true_eq, IsCoprime.mul_right_iff]
  congr 1
  exact propext (by tauto)

/-- Only active and residual factors are split from the actual Euler
coefficient. Their unramifiedness follows internally from this same mask. -/
theorem childData_row_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = ν) (χ : HeckeCharacter K) (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    heckeIdealCoefficient K
        (χ * (childData P R parent correction hcorr C primes m n pattern ν oldMask budget
          inverse left right geometry index).rowCharacter row.momentIdeal) J *
      maskValue (childData P R parent correction hcorr C primes m n pattern ν oldMask budget
        inverse left right geometry index) row.momentIdeal J.val =
      heckeIdealCoefficient K (χ * correction) J * originalCoprimeMask oldMask J.val *
        actualIdealResidue (A := A) (σ := σ) J.val g *
        actualIdealResidue (A := A) (σ := σ) J.val row.element := by
  let D := secondOriginalMovingFactors P R C primes m n pattern
  let χu := completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    P R ν row.momentIdeal
  have hphase := extracted_residue_character P R hroot hemb C primes m n pattern
    row hfactor ν hsector J
  rw [childData_mask P R parent correction hcorr C primes m n pattern ν oldMask budget
    inverse left right geometry index]
  rw [mul_assoc (heckeIdealCoefficient K (χ * correction) J * originalCoprimeMask oldMask J.val),
    hphase]
  change heckeIdealCoefficient K (χ * (correction * D.character * χu)) J *
      (if phaseMask row.momentIdeal D.support.val (secondSixthRootIdeal primes m n) J ∧
        IsCoprime J.val oldMask.val then 1 else 0) =
    (heckeIdealCoefficient K (χ * correction) J *
      (if IsCoprime J.val oldMask.val then 1 else 0)) *
      (heckeIdealCoefficient K D.character J * heckeIdealCoefficient K χu J *
        (if phaseMask row.momentIdeal D.support.val (secondSixthRootIdeal primes m n) J
          then 1 else 0))
  by_cases hgood : phaseMask row.momentIdeal D.support.val
      (secondSixthRootIdeal primes m n) J ∧ IsCoprime J.val oldMask.val
  · have hmove : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J.val →
        UnramifiedAt K D.character p := by
      intro p hp
      exact activeCharacter_unramified P R C primes m n pattern p (hgood.1.1 p hp).1
        (hgood.1.2.2.1.of_isCoprime_of_dvd_left hp)
    have hrow : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J.val →
        UnramifiedAt K χu p := by
      intro p hp
      have hu := residualCharacter_unramified P R row p (hgood.1.1 p hp).1
        (hgood.1.2.1.of_isCoprime_of_dvd_left hp)
      simpa only [hsector] using hu
    rw [show χ * (correction * D.character * χu) =
      ((χ * correction) * D.character) * χu by ac_rfl,
      coefficient_mul_right_unramified _ _ J hrow,
      coefficient_mul_right_unramified _ _ J hmove]
    simp only [hgood, hgood.1, hgood.2, if_true, mul_one]
    ring
  · by_cases hm : phaseMask row.momentIdeal D.support.val
        (secondSixthRootIdeal primes m n) J
    · have ho : ¬IsCoprime J.val oldMask.val := fun ho => hgood ⟨hm, ho⟩
      simp only [if_neg hgood, if_neg ho, if_pos hm, mul_zero, zero_mul]
    · simp only [if_neg hgood, if_neg hm, mul_zero, zero_mul]

/-- The actual single-ideal and single-prime dictionary is a conclusion
of the constructed data and the original frequency/sector identities. -/
def calibration
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = ν) :
    (sourceCharacters parent correction oldMask index).Calibration (σ := σ)
      (childData P R parent correction hcorr C primes m n pattern ν oldMask budget
        inverse left right geometry index) rfl row.momentIdeal g row.element where
  fixedRay_mem_theta θ hθ := by
    have he : θ = 1 := Finset.mem_singleton.mp hθ
    subst θ
    exact hone
  plain J := by
    have he := childData_row_coefficient P R parent correction hcorr C primes m n pattern
      ν oldMask budget inverse left right geometry index hroot hemb
      row hfactor hsector parent.plainBackground J
    simpa only [sourceCharacters, sourcePlainCoefficient, coefficient_one, mul_one] using he
  slot i p := by
    let d := childData P R parent correction hcorr C primes m n pattern ν oldMask budget
      inverse left right geometry index
    have he := childData_row_coefficient P R parent correction hcorr C primes m n pattern
      ν oldMask budget inverse left right geometry index hroot hemb
      row hfactor hsector (parent.slotCoefficient (index i)) (primeIdeal p)
    simp only [coefficient_prime] at he
    change primeCoefficient K (d.rowCharacter row.momentIdeal * parent.slotCoefficient (index i)) p *
      maskValue d row.momentIdeal p.asIdeal = _
    rw [mul_comm (d.rowCharacter row.momentIdeal) (parent.slotCoefficient (index i))]
    simpa only [sourceCharacters, sourcePrimeCoefficient, primeCoefficient_one,
      Fin.cast_refl, id_eq, mul_one] using he

/-- The right source has negative extracted factor and the same true
quotient element. The original twelfth root supplies its phase identity. -/
def negativeCalibration
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = ν) :
    (sourceCharacters parent correction oldMask index).Calibration (σ := σ)
      (childData P R parent correction hcorr C primes m n pattern ν oldMask budget
        inverse left right geometry index) rfl row.momentIdeal (-g) row.element where
  fixedRay_mem_theta := (calibration P R parent correction hcorr C primes m n pattern
    ν oldMask budget inverse left right geometry index hone hroot hemb row hfactor hsector).fixedRay_mem_theta
  plain J := by
    rw [residue_neg]
    exact (calibration P R parent correction hcorr C primes m n pattern
      ν oldMask budget inverse left right geometry index hone hroot hemb row hfactor hsector).plain J
  slot i p := by
    rw [residue_neg]
    exact (calibration P R parent correction hcorr C primes m n pattern
      ν oldMask budget inverse left right geometry index hone hroot hemb row hfactor hsector).slot i p

section ActualIndices

variable {H : Type*}

/-- The two actual finite partitions are made in the index type.
Consequently both identities used by the dictionary hold for all h. -/
abbrev PatternSector (S : ActualSecondCorrelationRows A σ H ι)
    (C : A.GeneralArithmeticContext σ η hS) (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :=
  {h : S.NonunitClass C pattern // (S.extractedRow C h.val).sector P = ν}

/-- On the actual common-correlation quotient rows, no phase identity
is supplied: factorization and sector identity are proved internally. -/
def actualCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    (sourceCharacters parent correction oldMask index).Calibration (σ := σ)
      (childData P R parent correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity
        pattern ν oldMask budget inverse left right geometry index) rfl
      (S.extractedRow C q.val.val).momentIdeal (S.factor C q.val.val.val)
      (S.extractedRow C q.val.val).element :=
  calibration P R parent correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity
    pattern ν oldMask budget inverse left right geometry index hone hroot hemb
    (S.extractedRow C q.val.val) (S.factor_nonunitClass C pattern q.val) q.property

def actualNegativeCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    (sourceCharacters parent correction oldMask index).Calibration (σ := σ)
      (childData P R parent correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity
        pattern ν oldMask budget inverse left right geometry index) rfl
      (S.extractedRow C q.val.val).momentIdeal (-(S.factor C q.val.val.val))
      (S.extractedRow C q.val.val).element :=
  negativeCalibration P R parent correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity
    pattern ν oldMask budget inverse left right geometry index hone hroot hemb
    (S.extractedRow C q.val.val) (S.factor_nonunitClass C pattern q.val) q.property

/-- The actual allocation deletes only its original frozen slots.
Both its source characters and the child's slot data use the same
`equivFin` index; there is no new occurrence or theta character. -/
def actualAllocatedCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (B : ActualColumnAllocation K geometry.slotCount)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    ((sourceCharacters parent correction oldMask index).restrictSlots B.keep).Calibration (σ := σ)
      ((childData P R parent correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity
        pattern ν oldMask budget inverse left right geometry index).restrictSlots B.keep) rfl
      (S.extractedRow C q.val.val).momentIdeal (S.factor C q.val.val.val)
      (S.extractedRow C q.val.val).element :=
  (actualCalibration P R parent correction hcorr C pattern ν oldMask budget
    inverse left right geometry index S hone hroot hemb q).restricted B.keep

def actualNegativeAllocatedCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (B : ActualColumnAllocation K geometry.slotCount)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    ((sourceCharacters parent correction oldMask index).restrictSlots B.keep).Calibration (σ := σ)
      ((childData P R parent correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity
        pattern ν oldMask budget inverse left right geometry index).restrictSlots B.keep) rfl
      (S.extractedRow C q.val.val).momentIdeal (-(S.factor C q.val.val.val))
      (S.extractedRow C q.val.val).element :=
  (actualNegativeCalibration P R parent correction hcorr C pattern ν oldMask budget
    inverse left right geometry index S hone hroot hemb q).restricted B.keep

end ActualIndices

section SameChoice

variable {S₀ : Finset (HeightOneSpectrum (𝓞 K))} {root12 : K}

/-- For the same original ArithmeticChoice and probe, the two phase
field identities are consequences of that literal arithmetic record. -/
theorem chosenProbe_phase_fields (X : HeckeAxiom.ArithmeticChoice K S₀ root12 σ)
    (P : ProbeData K (X.places : Set (HeightOneSpectrum (𝓞 K))))
    (hP : P.arithmetic = X.thetaData) :
    P.arithmetic.root6 = X.A.zeta12 ^ 2 ∧ P.arithmetic.embedding = σ := by
  rw [hP]
  exact ⟨rfl, rfl⟩

end SameChoice

end HeckeSkeleton.Moments.EngineStep.CanonicalOriginalPhaseCalibration

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalPhaseCalibration.residue_eq_original_evaluation
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalPhaseCalibration.coefficient_mul_right_unramified
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalPhaseCalibration.extracted_residue_character
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalPhaseCalibration.calibration
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalPhaseCalibration.actualCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalPhaseCalibration.actualNegativeCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalPhaseCalibration.actualAllocatedCalibration
