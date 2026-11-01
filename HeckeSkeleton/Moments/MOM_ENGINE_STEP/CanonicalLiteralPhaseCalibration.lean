import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDeletion
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralMaskSupport

/-!
# Literal source characters and the actual appended child calibration

The first divisor, pool reciprocity and empty-mask unit elements are
inserted as three genuine moving singletons.  An additional deletion
ideal retains the passive first common primes.  Its full multiplicity is
kept in the remaining ideal of the same child.

The literal source mask and the child's exterior-radical source mask
agree on ideals coprime to the original fixed S.  Outside that gate the
actual residue is zero.  Transporting the two single-atom identities by
these facts gives the actual arithmetic calibration, without assuming
equality of entire source records or of whole polynomials.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPhaseCalibration

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}

/-- Only the original three generated elements occur here.  In
particular the first element is not assumed to contain passive primes. -/
structure FixedPhases (A : SArithmeticData K) where
  firstIdeal : A.Exterior
  poolIdeal : A.Exterior
  unitIdeal : A.Exterior
  firstElement : A.R
  poolElement : A.R
  unitElement : A.R
  first_generates : A.Generates firstIdeal firstElement
  pool_generates : A.Generates poolIdeal poolElement
  unit_generates : A.Generates unitIdeal unitElement

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

namespace FixedPhases

variable (F : FixedPhases A)

def firstMoving : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton ⟨F.firstElement, F.first_generates.1⟩ 1

def poolMoving : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton ⟨F.poolElement, F.pool_generates.1⟩ 1

def unitMoving : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton ⟨F.unitElement, F.unit_generates.1⟩ 1

/-- The list is appended in exactly the order of the literal atom
operations.  No exponent is combined or cancelled. -/
def moving (D : OriginalMovingFactors A P R) : OriginalMovingFactors A P R :=
  ((D.appendFactors (F.firstMoving P R)).appendFactors (F.poolMoving P R)).appendFactors
    (F.unitMoving P R)

theorem moving_character (D : OriginalMovingFactors A P R) :
    (F.moving P R D).character =
      ((D.character * (F.firstMoving P R).character) * (F.poolMoving P R).character) *
        (F.unitMoving P R).character := by
  simp only [moving, OriginalMovingFactors.appendFactors_character]

private theorem singleton_support_coprime
    (J : A.Exterior) (a : A.R) (ha : A.Generates J a) (I : Ideal (𝓞 K)) :
    IsCoprime I (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).support.val ↔
      IsCoprime I J.val := by
  rw [OriginalMovingFactors.coprime_support_iff_fullIdeal,
    OriginalMovingFactors.singleton_fullIdeal J a ha 1]

theorem moving_support_coprime (D : OriginalMovingFactors A P R) (I : Ideal (𝓞 K)) :
    IsCoprime I (F.moving P R D).support.val ↔
      ((IsCoprime I D.support.val ∧ IsCoprime I F.firstIdeal.val) ∧
        IsCoprime I F.poolIdeal.val) ∧ IsCoprime I F.unitIdeal.val := by
  simp only [moving, OriginalMovingFactors.appendFactors_support_coprime_iff,
    firstMoving, poolMoving, unitMoving,
    singleton_support_coprime P R F.firstIdeal F.firstElement F.first_generates I,
    singleton_support_coprime P R F.poolIdeal F.poolElement F.pool_generates I,
    singleton_support_coprime P R F.unitIdeal F.unitElement F.unit_generates I]

/-- The extra mask is a separate deletion, independent of whether a
prime appears in one of the fixed residue phases. -/
def applyCharacters {k : ℕ} (T : FixedChildCharacters K k)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K) : FixedChildCharacters K k :=
  ((((T.movingSingleton P R F.firstIdeal F.firstElement F.first_generates).movingSingleton
    P R F.poolIdeal F.poolElement F.pool_generates).movingSingleton
    P R F.unitIdeal F.unitElement F.unit_generates).deleteMask extra)

@[simp] theorem applyCharacters_restrictSlots {k : ℕ} (T : FixedChildCharacters K k)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K) (keep : Finset (Fin k)) :
    (F.applyCharacters P R T extra).restrictSlots keep =
      F.applyCharacters P R (T.restrictSlots keep) extra := rfl

end FixedPhases

private theorem effective_support_coprime
    (D : OriginalMovingFactors A P R) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (I : Ideal (𝓞 K)) (hI : IsCoprime I A.cS) :
    IsCoprime I (D.effectiveFullSupport remaining).val ↔
      IsCoprime I D.support.val ∧ IsCoprime I remaining.val := by
  change IsCoprime I (D.fullMaskSupport (remainingMaskIdeal A remaining)).val ↔ _
  rw [D.fullMaskSupport_coprime_iff, remainingMaskIdeal_val,
    ← remainingMaskRadical_coprime_iff A remaining I hI]

private theorem mask_indicator_mul (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : ℂ) else 0) * (if q then 1 else 0) =
      if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false,
    true_and, false_and, mul_one, mul_zero, zero_mul]

section Source

variable {ω ψ : HeckeCharacter K}

/-- The source is formed from the actual original character and raw
mask, before the three moving operations and extra common deletion. -/
def sourceCharacters (F : FixedPhases A) (parent : MomentData K ω ψ)
    (D : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ}
    (index : Fin k → Fin parent.geometry.slotCount) : FixedChildCharacters K k :=
  F.applyCharacters P R
    (CanonicalOriginalPhaseCalibration.sourceCharacters parent
      (correction * D.character) (exteriorMomentIdeal D.support * remaining) index) extra

variable (F : FixedPhases A) (parent : MomentData K ω ψ)
variable (D : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ}
variable (index : Fin k → Fin parent.geometry.slotCount)

@[simp] theorem sourceCharacters_restrictSlots (keep : Finset (Fin k)) :
    (sourceCharacters P R F parent D correction remaining extra index).restrictSlots keep =
      sourceCharacters P R F parent D correction remaining extra
        (fun i => index (SlotRestriction.index keep i)) := rfl

theorem sourceCharacters_plain :
    (sourceCharacters P R F parent D correction remaining extra index).plain =
      (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
        correction (remaining * extra) index).plain := by
  change (((parent.plainBackground * (correction * D.character)) *
    (F.firstMoving P R).character) * (F.poolMoving P R).character) *
      (F.unitMoving P R).character =
    (parent.plainBackground * correction) * (F.moving P R D).character
  rw [F.moving_character P R D]
  ac_rfl

theorem sourceCharacters_slot (i : Fin k) :
    (sourceCharacters P R F parent D correction remaining extra index).slot i =
      (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
        correction (remaining * extra) index).slot i := by
  change (((parent.slotCoefficient (index i) * (correction * D.character)) *
    (F.firstMoving P R).character) * (F.poolMoving P R).character) *
      (F.unitMoving P R).character =
    (parent.slotCoefficient (index i) * correction) * (F.moving P R D).character
  rw [F.moving_character P R D]
  ac_rfl

/-- This equality uses exactly the original fixed-S gate.  It is not
asserted for arbitrary ideals outside that gate. -/
theorem sourceCharacters_mask (I : Ideal (𝓞 K)) (hI : IsCoprime I A.cS) :
    (sourceCharacters P R F parent D correction remaining extra index).mask I =
      (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
        correction (remaining * extra) index).mask I := by
  change ((((if IsCoprime I (D.support.val * remaining.val) then (1 : ℂ) else 0) *
      (if IsCoprime I F.firstIdeal.val then 1 else 0)) *
      (if IsCoprime I F.poolIdeal.val then 1 else 0)) *
      (if IsCoprime I F.unitIdeal.val then 1 else 0)) *
      (if IsCoprime I extra.val then 1 else 0) =
    (if IsCoprime I ((F.moving P R D).effectiveFullSupport (remaining * extra)).val
      then 1 else 0)
  simp only [mask_indicator_mul]
  congr 1
  apply propext
  rw [effective_support_coprime P R (F.moving P R D) (remaining * extra) I hI,
    F.moving_support_coprime P R D I]
  change ((((IsCoprime I (D.support.val * remaining.val) ∧
    IsCoprime I F.firstIdeal.val) ∧ IsCoprime I F.poolIdeal.val) ∧
    IsCoprime I F.unitIdeal.val) ∧ IsCoprime I extra.val) ↔
    (((IsCoprime I D.support.val ∧ IsCoprime I F.firstIdeal.val) ∧
      IsCoprime I F.poolIdeal.val) ∧ IsCoprime I F.unitIdeal.val) ∧
        IsCoprime I (remaining.val * extra.val)
  rw [IsCoprime.mul_right_iff, IsCoprime.mul_right_iff]
  tauto

theorem sourceCharacters_plain_coefficient
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : IsCoprime I.val A.cS) :
    sourcePlainCoefficient
        (sourceCharacters P R F parent D correction remaining extra index).plain
        (sourceCharacters P R F parent D correction remaining extra index).plainTwist
        (sourceCharacters P R F parent D correction remaining extra index).mask I =
      sourcePlainCoefficient
        (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
          correction (remaining * extra) index).plain
        (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
          correction (remaining * extra) index).plainTwist
        (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
          correction (remaining * extra) index).mask I := by
  unfold sourcePlainCoefficient
  rw [sourceCharacters_plain P R F parent D correction remaining extra index,
    sourceCharacters_mask P R F parent D correction remaining extra index I.val hI]

theorem sourceCharacters_prime_coefficient (i : Fin k) (p : HeightOneSpectrum (𝓞 K))
    (hp : IsCoprime p.asIdeal A.cS) :
    sourcePrimeCoefficient
        ((sourceCharacters P R F parent D correction remaining extra index).slot i)
        ((sourceCharacters P R F parent D correction remaining extra index).slotTwist i)
        (sourceCharacters P R F parent D correction remaining extra index).mask p =
      sourcePrimeCoefficient
        ((CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
          correction (remaining * extra) index).slot i)
        ((CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
          correction (remaining * extra) index).slotTwist i)
        (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
          correction (remaining * extra) index).mask p := by
  unfold sourcePrimeCoefficient
  rw [sourceCharacters_slot P R F parent D correction remaining extra index i,
    sourceCharacters_mask P R F parent D correction remaining extra index p.asIdeal hp]

variable {σ : K →+* ℂ}

private def calibrationOfCanonical (d : MomentData K ω ψ) (count : d.geometry.slotCount = k)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h' : A.R)
    (original : (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
      correction (remaining * extra) index).Calibration (σ := σ) d count u g h') :
    (sourceCharacters P R F parent D correction remaining extra index).Calibration
      (σ := σ) d count u g h' where
  fixedRay_mem_theta := original.fixedRay_mem_theta
  plain I := by
    rw [original.plain I]
    by_cases hI : IsCoprime I.val A.cS
    · rw [sourceCharacters_plain_coefficient P R F parent D correction remaining extra index I hI]
    · have hzero : actualIdealResidue (A := A) (σ := σ) I.val g = 0 := by
        exact dif_neg (fun h => hI h.2)
      simp only [hzero, mul_zero, zero_mul]
  slot i p := by
    rw [original.slot i p]
    by_cases hp : IsCoprime p.asIdeal A.cS
    · rw [sourceCharacters_prime_coefficient P R F parent D correction remaining extra index
        (Fin.cast count i) p hp]
    · have hzero : actualIdealResidue (A := A) (σ := σ) p.asIdeal g = 0 := by
        exact dif_neg (fun h => hp h.2)
      simp only [hzero, mul_zero, zero_mul]

end Source

section ActualIndices

variable {ω ψ : HeckeCharacter K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : FixedPhases A) (parent : MomentData K ω ψ)
variable (D : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (hcorr : correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
variable (inverse left right : IdealTest K) (geometry : SlotGeometry K)
variable (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)

/-- The original pattern-sector row supplies its genuine generator
factorization. Only the already proved single-atom identities are
transported from the exterior-radical source to the literal source. -/
def actualCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    (sourceCharacters P R F parent D correction remaining extra index).Calibration (σ := σ)
      (CanonicalAppendedPhaseCalibration.childData P R parent (F.moving P R D) correction hcorr
        C S.primes S.leftMultiplicity S.rightMultiplicity pattern ν (remaining * extra) budget
        inverse left right geometry index) rfl
      (S.extractedRow C q.val.val).momentIdeal (S.factor C q.val.val.val)
      (S.extractedRow C q.val.val).element :=
  calibrationOfCanonical P R F parent D correction remaining extra index _ rfl _ _ _
    (CanonicalAppendedPhaseCalibration.actualCalibration P R parent (F.moving P R D)
      correction hcorr C pattern ν (remaining * extra) budget inverse left right geometry index
      S hone hroot hemb q)

def actualNegativeCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    (sourceCharacters P R F parent D correction remaining extra index).Calibration (σ := σ)
      (CanonicalAppendedPhaseCalibration.childData P R parent (F.moving P R D) correction hcorr
        C S.primes S.leftMultiplicity S.rightMultiplicity pattern ν (remaining * extra) budget
        inverse left right geometry index) rfl
      (S.extractedRow C q.val.val).momentIdeal (-(S.factor C q.val.val.val))
      (S.extractedRow C q.val.val).element :=
  calibrationOfCanonical P R F parent D correction remaining extra index _ rfl _ _ _
    (CanonicalAppendedPhaseCalibration.actualNegativeCalibration P R parent (F.moving P R D)
      correction hcorr C pattern ν (remaining * extra) budget inverse left right geometry index
      S hone hroot hemb q)

/-- The chosen allocation is unchanged. Both the literal dictionary
and the original child use its same retained-slot map. -/
def actualAllocatedCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (B : ActualColumnAllocation K geometry.slotCount)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    ((sourceCharacters P R F parent D correction remaining extra index).restrictSlots B.keep).Calibration
      (σ := σ)
      ((CanonicalAppendedPhaseCalibration.childData P R parent (F.moving P R D) correction hcorr
        C S.primes S.leftMultiplicity S.rightMultiplicity pattern ν (remaining * extra) budget
        inverse left right geometry index).restrictSlots B.keep) rfl
      (S.extractedRow C q.val.val).momentIdeal (S.factor C q.val.val.val)
      (S.extractedRow C q.val.val).element :=
  (actualCalibration P R F parent D correction hcorr C pattern ν remaining extra budget
    inverse left right geometry index S hone hroot hemb q).restricted B.keep

def actualNegativeAllocatedCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (B : ActualColumnAllocation K geometry.slotCount)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    ((sourceCharacters P R F parent D correction remaining extra index).restrictSlots B.keep).Calibration
      (σ := σ)
      ((CanonicalAppendedPhaseCalibration.childData P R parent (F.moving P R D) correction hcorr
        C S.primes S.leftMultiplicity S.rightMultiplicity pattern ν (remaining * extra) budget
        inverse left right geometry index).restrictSlots B.keep) rfl
      (S.extractedRow C q.val.val).momentIdeal (-(S.factor C q.val.val.val))
      (S.extractedRow C q.val.val).element :=
  (actualNegativeCalibration P R F parent D correction hcorr C pattern ν remaining extra budget
    inverse left right geometry index S hone hroot hemb q).restricted B.keep

end ActualIndices

section OriginalSource

variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (F : FixedPhases A)

/-- The actual original recipe's raw product mask is definitionally
the starting mask used above. All three singleton operations remain
the literal operations on that source. -/
theorem apply_literalSourceCharacters (ξ : X)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K) :
    F.applyCharacters P R (Q.literalSourceCharacters ξ) extra =
      sourceCharacters P R F (data ξ) Q.moving Q.correction Q.remaining extra id := rfl

theorem apply_literalSourceCharacters_restricted (ξ : X)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (keep : Finset (Fin (data ξ).geometry.slotCount)) :
    F.applyCharacters P R ((Q.literalSourceCharacters ξ).restrictSlots keep) extra =
      sourceCharacters P R F (data ξ) Q.moving Q.correction Q.remaining extra
        (SlotRestriction.index keep) := rfl

/-- The existing recipe permits the original correction to be one;
the original theta identity supplies that case internally. -/
theorem original_correction_mem (ξ : X)
    (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta) :
    Q.correction ∈ (data ξ).theta := by
  rcases Q.correction_mem ξ with h | h
  · simpa only [h] using hone
  · exact h

end OriginalSource

section ActualAtoms

variable {σ : K →+* ℂ} {k : ℕ}
variable (F : FixedPhases A) (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

/-- All norm powers, the extracted scalar and the Gauss normalizers
leave the characters alone. The three actual moving operations and
the independent full common deletion are exactly those calibrated
above; the original first extraction supplies their slot map. -/
theorem secondInput_characters (power : A.Exterior) (δ₁ δ₂ : ℝ)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((d.secondInput (σ := σ) b P R power F.firstIdeal F.poolIdeal F.unitIdeal
      F.firstElement F.poolElement F.unitElement F.first_generates F.pool_generates
      F.unit_generates δ₁ δ₂).deleteMask extra).characters =
      F.applyCharacters P R (d.characters.restrictSlots b.keep) extra := rfl

end ActualAtoms

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPhaseCalibration

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPhaseCalibration.FixedPhases.moving_support_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPhaseCalibration.sourceCharacters_mask
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPhaseCalibration.actualAllocatedCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPhaseCalibration.actualNegativeAllocatedCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPhaseCalibration.apply_literalSourceCharacters_restricted
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPhaseCalibration.secondInput_characters
