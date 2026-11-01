import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPhaseCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalMovingFactorAppend

/-!
# Literal residue calibration after appending the new moving factor

The source keeps every original moving character inside its actual Euler
coefficient.  The child appends the new active factor to the original
list and retains the full sixth root in its remaining deletion.  The
effective old support is used only through its proved complete-row mask
identity.  In particular no unramifiedness of the original moving or
background characters is assumed, and no character is added to theta.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalAppendedPhaseCalibration

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}

/-- The entire old moving product remains in each original coefficient.
The finite-ray factor is the original trivial character. -/
def sourceCharacters (parent : MomentData K ω ψ)
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ}
    (index : Fin k → Fin parent.geometry.slotCount) : FixedChildCharacters K k where
  plain := parent.plainBackground * correction * oldMoving.character
  slot i := parent.slotCoefficient (index i) * correction * oldMoving.character
  plainTwist := 1
  slotTwist _ := 1
  mask := originalCoprimeMask (exteriorMomentIdeal (oldMoving.effectiveFullSupport remaining))
  fixedRay := {1}
  plainTwist_mem := Finset.mem_singleton_self 1
  slotTwist_mem _ := Finset.mem_singleton_self 1

@[simp] theorem sourceCharacters_restrictSlots
    (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ}
    (index : Fin k → Fin parent.geometry.slotCount) (keep : Finset (Fin k)) :
    (sourceCharacters P R parent oldMoving correction remaining index).restrictSlots keep =
      sourceCharacters P R parent oldMoving correction remaining
        (fun i => index (SlotRestriction.index keep i)) := rfl

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual child uses the concatenated moving list and the full
new remaining sixth root.  All its raw fields are constructed here. -/
def childData (parent : MomentData K ω ψ)
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (hcorr : correction ∈ parent.theta)
    (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
    (inverse left right : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount) : MomentData K ω ψ :=
  CanonicalOriginalChildData.data parent
    (oldMoving.appendSecondFactor C primes m n pattern)
    correction (Or.inr hcorr) (fun _ => ν)
    (remainingMaskIdeal A remaining * exteriorMomentIdeal (secondSixthRootIdeal primes m n))
    budget inverse left right geometry index

variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
variable (m n : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
variable (inverse left right : IdealTest K) (geometry : SlotGeometry K)
variable (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)

private theorem common_mask_reorder (a b c d : Bool) :
    (((a && b) && c) && d) = ((a && c) && (b && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- The old support is collapsed only behind the same complete-row
gate.  This is an identity of the actual child masks, including zeros. -/
theorem childData_mask_eq (u J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    maskValue (childData P R parent oldMoving correction hcorr C primes m n pattern ν
      remaining budget inverse left right geometry index) u J.val =
    maskValue (CanonicalOriginalPhaseCalibration.childData P R parent correction hcorr
      C primes m n pattern ν (exteriorMomentIdeal (oldMoving.effectiveFullSupport remaining))
      budget inverse left right geometry index) u J.val := by
  apply congrArg (fun gate : Bool => if gate then (1 : ℂ) else 0)
  change ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u J.val &&
      decide (IsCoprime J.val
        (oldMoving.appendFactors (secondOriginalMovingFactors P R C primes m n pattern)).support.val)) &&
      decide (IsCoprime J.val
        (remainingMaskIdeal A remaining * exteriorMomentIdeal (secondSixthRootIdeal primes m n)).val)) =
    ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u J.val &&
      decide (IsCoprime J.val (secondOriginalMovingFactors P R C primes m n pattern).support.val)) &&
      decide (IsCoprime J.val
        ((oldMoving.effectiveFullSupport remaining).val * (secondSixthRootIdeal primes m n).val)))
  rw [oldMoving.appendFactors_normalizedFullMask
    (secondOriginalMovingFactors P R C primes m n pattern) remaining u
    (secondSixthRootIdeal primes m n) J.val,
    oldMoving.effectiveFullSupport_mask remaining u J.val,
    IsCoprime.mul_right_iff]
  simp only [Bool.decide_and]
  exact common_mask_reorder _ _ _ _

/-- The original moving character is multiplied into the unchanged
source background; only the genuinely new active and row characters
are separated by the original residue dictionary. -/
theorem childData_rowCharacter (u : HeckeGeneral.Analysis.NonzeroIdeal K) (χ : HeckeCharacter K) :
    χ * (childData P R parent oldMoving correction hcorr C primes m n pattern ν
      remaining budget inverse left right geometry index).rowCharacter u =
    (χ * oldMoving.character) *
      (CanonicalOriginalPhaseCalibration.childData P R parent correction hcorr C primes m n
        pattern ν (exteriorMomentIdeal (oldMoving.effectiveFullSupport remaining)) budget
        inverse left right geometry index).rowCharacter u := by
  change χ * ((correction * (oldMoving.appendSecondFactor C primes m n pattern).character) *
      completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R ν u) =
    (χ * oldMoving.character) *
      ((correction * (secondOriginalMovingFactors P R C primes m n pattern).character) *
        completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R ν u)
  rw [oldMoving.appendSecondFactor_character C primes m n pattern]
  ac_rfl

variable {Ih : A.Exterior} {h g : A.R} {factor : ℝ}

theorem childData_row_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = ν) (χ : HeckeCharacter K) (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    heckeIdealCoefficient K
        (χ * (childData P R parent oldMoving correction hcorr C primes m n pattern ν
          remaining budget inverse left right geometry index).rowCharacter row.momentIdeal) J *
      maskValue (childData P R parent oldMoving correction hcorr C primes m n pattern ν
        remaining budget inverse left right geometry index) row.momentIdeal J.val =
      heckeIdealCoefficient K (χ * correction * oldMoving.character) J *
        originalCoprimeMask (exteriorMomentIdeal (oldMoving.effectiveFullSupport remaining)) J.val *
        actualIdealResidue (A := A) (σ := σ) J.val g *
        actualIdealResidue (A := A) (σ := σ) J.val row.element := by
  rw [childData_rowCharacter P R parent oldMoving correction hcorr C primes m n pattern ν
      remaining budget inverse left right geometry index row.momentIdeal χ,
    childData_mask_eq P R parent oldMoving correction hcorr C primes m n pattern ν
      remaining budget inverse left right geometry index row.momentIdeal J]
  have he := CanonicalOriginalPhaseCalibration.childData_row_coefficient
    P R parent correction hcorr C primes m n pattern ν
    (exteriorMomentIdeal (oldMoving.effectiveFullSupport remaining)) budget
    inverse left right geometry index hroot hemb row hfactor hsector (χ * oldMoving.character) J
  have hc : (χ * oldMoving.character) * correction =
      χ * correction * oldMoving.character := by ac_rfl
  simpa only [hc] using he

/-- Single-ideal and single-prime identities for the same appended
child, with its literal original background and finite slot characters. -/
def calibration
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = ν) :
    (sourceCharacters P R parent oldMoving correction remaining index).Calibration (σ := σ)
      (childData P R parent oldMoving correction hcorr C primes m n pattern ν remaining budget
        inverse left right geometry index) rfl row.momentIdeal g row.element where
  fixedRay_mem_theta θ hθ := by
    have he : θ = 1 := Finset.mem_singleton.mp hθ
    subst θ
    exact hone
  plain J := by
    have he := childData_row_coefficient P R parent oldMoving correction hcorr C primes m n
      pattern ν remaining budget inverse left right geometry index hroot hemb
      row hfactor hsector parent.plainBackground J
    simpa only [sourceCharacters, sourcePlainCoefficient, coefficient_one, mul_one] using he
  slot i p := by
    let d := childData P R parent oldMoving correction hcorr C primes m n pattern ν
      remaining budget inverse left right geometry index
    have he := childData_row_coefficient P R parent oldMoving correction hcorr C primes m n
      pattern ν remaining budget inverse left right geometry index hroot hemb
      row hfactor hsector (parent.slotCoefficient (index i)) (primeIdeal p)
    simp only [coefficient_prime] at he
    change primeCoefficient K (d.rowCharacter row.momentIdeal * parent.slotCoefficient (index i)) p *
      maskValue d row.momentIdeal p.asIdeal = _
    rw [mul_comm (d.rowCharacter row.momentIdeal) (parent.slotCoefficient (index i))]
    simpa only [sourceCharacters, sourcePrimeCoefficient, primeCoefficient_one,
      Fin.cast_refl, id_eq, mul_one] using he

def negativeCalibration
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = ν) :
    (sourceCharacters P R parent oldMoving correction remaining index).Calibration (σ := σ)
      (childData P R parent oldMoving correction hcorr C primes m n pattern ν remaining budget
        inverse left right geometry index) rfl row.momentIdeal (-g) row.element where
  fixedRay_mem_theta := (calibration P R parent oldMoving correction hcorr C primes m n pattern
    ν remaining budget inverse left right geometry index hone hroot hemb
    row hfactor hsector).fixedRay_mem_theta
  plain J := by
    rw [residue_neg]
    exact (calibration P R parent oldMoving correction hcorr C primes m n pattern
      ν remaining budget inverse left right geometry index hone hroot hemb row hfactor hsector).plain J
  slot i p := by
    rw [residue_neg]
    exact (calibration P R parent oldMoving correction hcorr C primes m n pattern
      ν remaining budget inverse left right geometry index hone hroot hemb row hfactor hsector).slot i p

section ActualIndices

variable {H : Type*}

/-- Actual live rows supply their own factorization and sector. -/
def actualCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    (sourceCharacters P R parent oldMoving correction remaining index).Calibration (σ := σ)
      (childData P R parent oldMoving correction hcorr C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern ν remaining budget inverse left right geometry index) rfl
      (S.extractedRow C q.val.val).momentIdeal (S.factor C q.val.val.val)
      (S.extractedRow C q.val.val).element :=
  calibration P R parent oldMoving correction hcorr C S.primes S.leftMultiplicity
    S.rightMultiplicity pattern ν remaining budget inverse left right geometry index
    hone hroot hemb (S.extractedRow C q.val.val) (S.factor_nonunitClass C pattern q.val) q.property

def actualNegativeCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    (sourceCharacters P R parent oldMoving correction remaining index).Calibration (σ := σ)
      (childData P R parent oldMoving correction hcorr C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern ν remaining budget inverse left right geometry index) rfl
      (S.extractedRow C q.val.val).momentIdeal (-(S.factor C q.val.val.val))
      (S.extractedRow C q.val.val).element :=
  negativeCalibration P R parent oldMoving correction hcorr C S.primes S.leftMultiplicity
    S.rightMultiplicity pattern ν remaining budget inverse left right geometry index
    hone hroot hemb (S.extractedRow C q.val.val) (S.factor_nonunitClass C pattern q.val) q.property

/-- The same actual allocation acts on both the source dictionary and
the chosen child. No second removal choice is made in the calibration. -/
def actualAllocatedCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (B : ActualColumnAllocation K geometry.slotCount)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    ((sourceCharacters P R parent oldMoving correction remaining index).restrictSlots B.keep).Calibration
      (σ := σ) ((childData P R parent oldMoving correction hcorr C S.primes
        S.leftMultiplicity S.rightMultiplicity pattern ν remaining budget
        inverse left right geometry index).restrictSlots B.keep) rfl
      (S.extractedRow C q.val.val).momentIdeal (S.factor C q.val.val.val)
      (S.extractedRow C q.val.val).element :=
  (actualCalibration P R parent oldMoving correction hcorr C pattern ν remaining budget
    inverse left right geometry index S hone hroot hemb q).restricted B.keep

def actualNegativeAllocatedCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (B : ActualColumnAllocation K geometry.slotCount)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    ((sourceCharacters P R parent oldMoving correction remaining index).restrictSlots B.keep).Calibration
      (σ := σ) ((childData P R parent oldMoving correction hcorr C S.primes
        S.leftMultiplicity S.rightMultiplicity pattern ν remaining budget
        inverse left right geometry index).restrictSlots B.keep) rfl
      (S.extractedRow C q.val.val).momentIdeal (-(S.factor C q.val.val.val))
      (S.extractedRow C q.val.val).element :=
  (actualNegativeCalibration P R parent oldMoving correction hcorr C pattern ν remaining budget
    inverse left right geometry index S hone hroot hemb q).restricted B.keep

end ActualIndices

end HeckeSkeleton.Moments.EngineStep.CanonicalAppendedPhaseCalibration

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalAppendedPhaseCalibration.childData_mask_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalAppendedPhaseCalibration.childData_row_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalAppendedPhaseCalibration.actualAllocatedCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalAppendedPhaseCalibration.actualNegativeAllocatedCalibration
