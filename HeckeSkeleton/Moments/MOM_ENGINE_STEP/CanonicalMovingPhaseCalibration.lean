import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondFactorAssembly

/-!
# Actual quotient-row calibration with the original moving prefix

The source keeps the fixed character computed from all earlier original
factors. The child appends the actual second active frequency factors to
that same list. Its remaining ideal keeps both the earlier deletion and
the full second sixth-root support. The original parent background and
theta family are unchanged by this arithmetic construction.

The dictionary is proved on every row of the genuine nonunit-pattern and
unit-sector subtype. No character equality is assumed only on the finite
carrier, and no moving character is reclassified as a theta correction.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalMovingPhaseCalibration

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open CanonicalOriginalPhaseCalibration CanonicalSecondFactorAssembly

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {ω ψ : HeckeCharacter K}

/-- The child contains the literal old list followed by the true
second active factor. No cancellation changes displayed support. -/
def childData (parent : MomentData K ω ψ)
    (prefix : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (hcorr : correction = 1 ∨ correction ∈ parent.theta)
    (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool)
    (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (remaining : NonzeroIdeal K) (budget : ℝ)
    (inverse left right : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount) : MomentData K ω ψ :=
  CanonicalOriginalChildData.data parent
    (prefix.append (secondOriginalMovingFactors P R C primes m n pattern))
    correction hcorr (fun _ => sector)
    (remaining * exteriorMomentIdeal (secondSixthRootIdeal primes m n)) budget
    inverse left right geometry index

variable (parent : MomentData K ω ψ)
variable (prefix : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (hcorr : correction = 1 ∨ correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
variable (m n : ι → ℕ) (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : NonzeroIdeal K) (budget : ℝ)
variable (inverse left right : IdealTest K) (geometry : SlotGeometry K)
variable (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)
variable {Ih : A.Exterior} {h g : A.R} {factor : ℝ}

/-- The complete child mask is the actual second phase mask times the
original prefix and remaining deletion. The sixth-root mask is present
even when the primitive active character is trivial. -/
theorem childData_mask (u J : NonzeroIdeal K) :
    maskValue (childData P R parent prefix correction hcorr C primes m n pattern sector
        remaining budget inverse left right geometry index) u J.val =
      (if phaseMask u (secondOriginalMovingFactors P R C primes m n pattern).support.val
          (secondSixthRootIdeal primes m n) J ∧
          IsCoprime J.val (movingMask prefix remaining).val then (1 : ℂ) else 0) := by
  change (if ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u J.val &&
      decide (IsCoprime J.val
        (prefix.append (secondOriginalMovingFactors P R C primes m n pattern)).support.val)) &&
      decide (IsCoprime J.val (remaining.val * (secondSixthRootIdeal primes m n).val)))
      then (1 : ℂ) else 0) = _
  simp only [completeIdealCommonMask, phaseMask, movingMask, sexticIdealOutsideS,
    Bool.and_eq_true, decide_eq_true_eq, IsCoprime.mul_right_iff,
    prefix.coprime_append_support]
  congr 1
  exact propext (by tauto)

/-- Both new character factors are split only on their actual live
mask. The whole earlier prefix stays in the fixed background, which
is permitted to ramify. -/
theorem childData_row_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = sector) (χ : HeckeCharacter K) (J : NonzeroIdeal K) :
    heckeIdealCoefficient K
        (χ * (childData P R parent prefix correction hcorr C primes m n pattern sector
          remaining budget inverse left right geometry index).rowCharacter row.momentIdeal) J *
      maskValue (childData P R parent prefix correction hcorr C primes m n pattern sector
        remaining budget inverse left right geometry index) row.momentIdeal J.val =
      heckeIdealCoefficient K (χ * (correction * prefix.character)) J *
        originalCoprimeMask (movingMask prefix remaining) J.val *
        actualIdealResidue (A := A) (σ := σ) J.val g *
        actualIdealResidue (A := A) (σ := σ) J.val row.element := by
  let D := secondOriginalMovingFactors P R C primes m n pattern
  let χu := completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    P R sector row.momentIdeal
  have hphase := extracted_residue_character P R hroot hemb C primes m n pattern
    row hfactor sector hsector J
  rw [childData_mask P R parent prefix correction hcorr C primes m n pattern sector
    remaining budget inverse left right geometry index]
  rw [mul_assoc (heckeIdealCoefficient K (χ * (correction * prefix.character)) J *
    originalCoprimeMask (movingMask prefix remaining) J.val), hphase]
  change heckeIdealCoefficient K (χ * (correction * (prefix.append D).character * χu)) J *
      (if phaseMask row.momentIdeal D.support.val (secondSixthRootIdeal primes m n) J ∧
        IsCoprime J.val (movingMask prefix remaining).val then 1 else 0) =
    (heckeIdealCoefficient K (χ * (correction * prefix.character)) J *
      (if IsCoprime J.val (movingMask prefix remaining).val then 1 else 0)) *
      (heckeIdealCoefficient K D.character J * heckeIdealCoefficient K χu J *
        (if phaseMask row.momentIdeal D.support.val (secondSixthRootIdeal primes m n) J
          then 1 else 0))
  rw [prefix.append_character D]
  by_cases hgood : phaseMask row.momentIdeal D.support.val
      (secondSixthRootIdeal primes m n) J ∧ IsCoprime J.val (movingMask prefix remaining).val
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
    rw [show χ * (correction * (prefix.character * D.character) * χu) =
      ((χ * (correction * prefix.character)) * D.character) * χu by ac_rfl,
      coefficient_mul_right_unramified _ _ J hrow,
      coefficient_mul_right_unramified _ _ J hmove]
    simp only [hgood, hgood.1, hgood.2, if_true, mul_one]
    ring
  · by_cases hm : phaseMask row.momentIdeal D.support.val
        (secondSixthRootIdeal primes m n) J
    · have ho : ¬IsCoprime J.val (movingMask prefix remaining).val := fun ho => hgood ⟨hm, ho⟩
      simp only [if_neg hgood, if_neg ho, if_pos hm, mul_zero, zero_mul]
    · simp only [if_neg hgood, if_neg hm, mul_zero, zero_mul]

/-- The computed original source characters calibrate the actual
complete child data on every residual row in this fixed unit sector. -/
def calibration
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = sector) :
    (movingSourceCharacters parent correction prefix remaining index).Calibration (σ := σ)
      (childData P R parent prefix correction hcorr C primes m n pattern sector remaining budget
        inverse left right geometry index) rfl row.momentIdeal g row.element where
  fixedRay_mem_theta θ hθ := by
    have he : θ = 1 := Finset.mem_singleton.mp hθ
    subst θ
    exact hone
  plain J := by
    have he := childData_row_coefficient P R parent prefix correction hcorr C primes m n pattern
      sector remaining budget inverse left right geometry index hroot hemb
      row hfactor hsector parent.plainBackground J
    simpa only [movingSourceCharacters, sourceCharacters, sourcePlainCoefficient,
      coefficient_one, mul_one] using he
  slot i p := by
    let d := childData P R parent prefix correction hcorr C primes m n pattern sector
      remaining budget inverse left right geometry index
    have he := childData_row_coefficient P R parent prefix correction hcorr C primes m n pattern
      sector remaining budget inverse left right geometry index hroot hemb
      row hfactor hsector (parent.slotCoefficient (index i)) (primeIdeal p)
    simp only [coefficient_prime] at he
    change primeCoefficient K (d.rowCharacter row.momentIdeal * parent.slotCoefficient (index i)) p *
      maskValue d row.momentIdeal p.asIdeal = _
    rw [mul_comm (d.rowCharacter row.momentIdeal) (parent.slotCoefficient (index i))]
    simpa only [movingSourceCharacters, sourceCharacters, sourcePrimeCoefficient,
      primeCoefficient_one, Fin.cast_refl, id_eq, mul_one] using he

def negativeCalibration
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = sector) :
    (movingSourceCharacters parent correction prefix remaining index).Calibration (σ := σ)
      (childData P R parent prefix correction hcorr C primes m n pattern sector remaining budget
        inverse left right geometry index) rfl row.momentIdeal (-g) row.element where
  fixedRay_mem_theta := (calibration P R parent prefix correction hcorr C primes m n pattern
    sector remaining budget inverse left right geometry index hone hroot hemb row hfactor hsector).
      fixedRay_mem_theta
  plain J := by
    rw [residue_neg]
    exact (calibration P R parent prefix correction hcorr C primes m n pattern
      sector remaining budget inverse left right geometry index hone hroot hemb row hfactor hsector).
        plain J
  slot i p := by
    rw [residue_neg]
    exact (calibration P R parent prefix correction hcorr C primes m n pattern
      sector remaining budget inverse left right geometry index hone hroot hemb row hfactor hsector).
        slot i p

section ActualIndices

variable {H : Type*}

def actualCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern sector) :
    (movingSourceCharacters parent correction prefix remaining index).Calibration (σ := σ)
      (childData P R parent prefix correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity
        pattern sector remaining budget inverse left right geometry index) rfl
      (S.extractedRow C q.val.val).momentIdeal (S.factor C q.val.val.val)
      (S.extractedRow C q.val.val).element :=
  calibration P R parent prefix correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity
    pattern sector remaining budget inverse left right geometry index hone hroot hemb
    (S.extractedRow C q.val.val) (S.factor_nonunitClass C pattern q.val) q.property

def actualNegativeCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern sector) :
    (movingSourceCharacters parent correction prefix remaining index).Calibration (σ := σ)
      (childData P R parent prefix correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity
        pattern sector remaining budget inverse left right geometry index) rfl
      (S.extractedRow C q.val.val).momentIdeal (-(S.factor C q.val.val.val))
      (S.extractedRow C q.val.val).element :=
  negativeCalibration P R parent prefix correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity
    pattern sector remaining budget inverse left right geometry index hone hroot hemb
    (S.extractedRow C q.val.val) (S.factor_nonunitClass C pattern q.val) q.property

def actualAllocatedCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (B : ActualColumnAllocation K geometry.slotCount)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern sector) :
    ((movingSourceCharacters parent correction prefix remaining index).restrictSlots B.keep).
      Calibration (σ := σ)
      ((childData P R parent prefix correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity
        pattern sector remaining budget inverse left right geometry index).restrictSlots B.keep) rfl
      (S.extractedRow C q.val.val).momentIdeal (S.factor C q.val.val.val)
      (S.extractedRow C q.val.val).element :=
  (actualCalibration P R parent prefix correction hcorr C pattern sector remaining budget
    inverse left right geometry index S hone hroot hemb q).restricted B.keep

def actualNegativeAllocatedCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (B : ActualColumnAllocation K geometry.slotCount)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern sector) :
    ((movingSourceCharacters parent correction prefix remaining index).restrictSlots B.keep).
      Calibration (σ := σ)
      ((childData P R parent prefix correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity
        pattern sector remaining budget inverse left right geometry index).restrictSlots B.keep) rfl
      (S.extractedRow C q.val.val).momentIdeal (-(S.factor C q.val.val.val))
      (S.extractedRow C q.val.val).element :=
  (actualNegativeCalibration P R parent prefix correction hcorr C pattern sector remaining budget
    inverse left right geometry index S hone hroot hemb q).restricted B.keep

end ActualIndices

section Families

variable {X : Type*}

/-- The full moving-row recipe is produced by the same raw child
constructor, before any normalized capacity child is selected. -/
def movingRecipe
    (inverseTests leftTests rightTests : X → IdealTest K)
    (geometries : X → SlotGeometry K)
    (indices : ∀ ξ, Fin (geometries ξ).slotCount → Fin parent.geometry.slotCount) :
    CompleteMovingRowRecipe A P R (fun ξ =>
      childData P R parent prefix correction hcorr C primes m n pattern sector remaining budget
        (inverseTests ξ) (leftTests ξ) (rightTests ξ) (geometries ξ) (indices ξ)) :=
  CanonicalOriginalChildData.recipe parent
    (prefix.append (secondOriginalMovingFactors P R C primes m n pattern))
    correction hcorr (fun _ => sector)
    (remaining * exteriorMomentIdeal (secondSixthRootIdeal primes m n)) budget
    inverseTests leftTests rightTests geometries indices

theorem movingRecipe_fullJointBudget
    (inverseTests leftTests rightTests : X → IdealTest K)
    (geometries : X → SlotGeometry K)
    (indices : ∀ ξ, Fin (geometries ξ).slotCount → Fin parent.geometry.slotCount)
    (Z width : ℝ) :
    (movingRecipe P R parent prefix correction hcorr C primes m n pattern sector remaining
      (Z ^ width) inverseTests leftTests rightTests geometries indices).FullJointBudget Z width := by
  intro ξ u hu
  exact hu.2

end Families

section OriginalProfiles

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (leftAtom rightAtom : CanonicalLogProfiles.Atom V)
variable (slotAtom : Fin geometry.slotCount → CanonicalLogProfiles.Atom V)
variable (hleft : CanonicalLogProfiles.PositivePlainProfile left)
variable (hright : CanonicalLogProfiles.PositivePlainProfile right)
variable (hslot : ∀ i, CanonicalLogProfiles.PositivePrimeProfile (geometry.slots i))

/-- The actual logarithmic profile update is a literal data identity.
The original moving list, theta family, background, complete quotient
row and every mask are independent of the Fourier parameter. -/
theorem childData_logProfiles_eq (ξ : V) :
    childData P R parent prefix correction hcorr C primes m n pattern sector remaining budget
      inverse (leftAtom.idealTest left hleft ξ) (rightAtom.idealTest right hright ξ)
      { slotCount := geometry.slotCount
        slots i := (slotAtom i).primeWindow (geometry.slots i) (hslot i) ξ } index =
      CanonicalLogProfiles.data
        (childData P R parent prefix correction hcorr C primes m n pattern sector remaining budget
          inverse left right geometry index)
        leftAtom rightAtom slotAtom hleft hright hslot ξ := rfl

end OriginalProfiles

end HeckeSkeleton.Moments.EngineStep.CanonicalMovingPhaseCalibration

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalMovingPhaseCalibration.childData_mask
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalMovingPhaseCalibration.childData_row_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalMovingPhaseCalibration.calibration
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalMovingPhaseCalibration.actualAllocatedCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalMovingPhaseCalibration.movingRecipe_fullJointBudget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalMovingPhaseCalibration.childData_logProfiles_eq
