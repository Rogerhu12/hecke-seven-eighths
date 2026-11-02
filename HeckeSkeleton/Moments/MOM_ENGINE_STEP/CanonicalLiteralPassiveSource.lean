import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCenteredPassive
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocationAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidCharacters

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# The actual finite source after passive-mask allocation

One exterior smooth carrier is fixed for both original rectangles.
Its single-occurrence functions are the same quotient profiles of the
original second allocation.  Only the paid characters replace the old
characters.  Passive labels are computed on this enlarged carrier,
and each surviving label supplies its actual quotient table.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

namespace CanonicalLiteralPassiveSource

open CanonicalLiteralPassiveDeletion CanonicalLiteralProfileCarrier
open CanonicalLiteralCenteredPassive CanonicalLiteralAllocatedData
open CanonicalLiteralPhaseCalibration

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)

/-- A fixed table with the original quotient profiles and complete
Gauss normalization, on the untruncated exterior smooth carrier. -/
def table (A : SArithmeticData K) (T : FixedChildCharacters K B.keep.card) :
    CanonicalLiteralRectangles.Atoms (K := K) B.keep.card :=
  { d.allocate B with
    characters := T
    plain₁ := idealCarrier (W.exteriorSmoothPlain₁ B A)
    plain₂ := idealCarrier (W.exteriorSmoothPlain₂ B A)
    slots := W.exteriorSmoothSlots B A
    plain₁_nonzero := idealCarrier_nonzero _
    plain₂_nonzero := idealCarrier_nonzero _ }

def profiles (A : SArithmeticData K) (T : FixedChildCharacters K B.keep.card) :
    (table W B A T).ProfileData where
  left := (W.allocate B).left
  right := (W.allocate B).right
  slot := (W.allocate B).slot
  slot_length := (W.allocate B).slot_length
  left_positive := (W.allocate B).left_positive
  right_positive := (W.allocate B).right_positive
  slot_positive := (W.allocate B).slot_positive
  left_frozen := (W.allocate B).left_frozen
  right_frozen := (W.allocate B).right_frozen
  slot_frozen := (W.allocate B).slot_frozen
  left_eval := (W.allocate B).left_eval
  right_eval := (W.allocate B).right_eval
  slot_eval := (W.allocate B).slot_eval

@[simp] theorem table_normalizer (A : SArithmeticData K)
    (T : FixedChildCharacters K B.keep.card) : (table W B A T).normalizer = d.normalizer := by
  sorry

def plainLocation₁ (firstSign : ℝ) (negative : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) : WithLp 2 (ℝ × ℝ) :=
  CanonicalLiteralProfileData.orientedLocation negative
    (CanonicalLiteralLocations.plain firstSign (B.plainDivisor 0 * I))

def plainLocation₂ (firstSign : ℝ) (negative : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) : WithLp 2 (ℝ × ℝ) :=
  CanonicalLiteralProfileData.orientedLocation negative
    (CanonicalLiteralLocations.plain firstSign (B.plainDivisor (Fin.succ 0) * I))

def slotLocation (firstSign : ℝ) (negative : Bool) (i : Fin B.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) : WithLp 2 (ℝ × ℝ) :=
  CanonicalLiteralProfileData.orientedLocation negative
    (CanonicalLiteralLocations.prime firstSign (SlotRestriction.index B.keep i) p)

def centeredColumn (T : FixedChildCharacters K B.keep.card)
    (g h : A.R) (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) : ℂ :=
  d.normalizer *
    (jointFourierColumn B.childColumns
      (T.coefficient (σ := σ) g h
        (d.scale₁ false / idealNorm K (B.plainDivisor 0))
        (d.scale₂ false / idealNorm K (B.plainDivisor (Fin.succ 0))) d.base
        (fun i => d.length (SlotRestriction.index B.keep i))
        (fun I => d.rectangleLeftWeight false (B.plainDivisor 0 * I))
        (fun I => d.rightWeight false (B.plainDivisor (Fin.succ 0) * I))
        (fun i => d.slotWeight (SlotRestriction.index B.keep i)))
      (childCartesianLocation (plainLocation₁ B firstSign negative)
        (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ -
     jointFourierColumn B.childColumns
      (T.coefficient (σ := σ) g h
        (d.scale₁ true / idealNorm K (B.plainDivisor 0))
        (d.scale₂ true / idealNorm K (B.plainDivisor (Fin.succ 0))) d.base
        (fun i => d.length (SlotRestriction.index B.keep i))
        (fun I => d.rectangleLeftWeight true (B.plainDivisor 0 * I))
        (fun I => d.rightWeight true (B.plainDivisor (Fin.succ 0) * I))
        (fun i => d.slotWeight (SlotRestriction.index B.keep i)))
      (childCartesianLocation (plainLocation₁ B firstSign negative)
        (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ)

def labels (A : SArithmeticData K) (M : HeckeGeneral.Analysis.NonzeroIdeal K) :=
  liveLabels M.val (idealCarrier (W.exteriorSmoothPlain₁ B A))
    (idealCarrier (W.exteriorSmoothPlain₂ B A)) (W.exteriorSmoothSlots B A)
    id id HeightOneSpectrum.asIdeal

def branch (A : SArithmeticData K) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (a : { a // a ∈ labels W B A M }) : ActualColumnAllocation K B.keep.card :=
  allocation M.val (idealCarrier (W.exteriorSmoothPlain₁ B A))
    (idealCarrier (W.exteriorSmoothPlain₂ B A)) (W.exteriorSmoothSlots B A)
    (idealCarrier_nonzero _) (idealCarrier_nonzero _) a

def passiveColumn (T : FixedChildCharacters K B.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) (g h : A.R)
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) : ℂ :=
  ∑ a ∈ (labels W B A M).attach,
    sign a.val * jointFourierColumn (branch W B A M a).columns
      ((table W B A T).frequencyWhole (σ := σ) g h)
      (rawSourceLocation (plainLocation₁ B firstSign negative)
        (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ

theorem table_frequencyWhole (T : FixedChildCharacters K B.keep.card)
    (g h : A.R) (i : AllocationColumn K B.keep.card) :
    (table W B A T).frequencyWhole (σ := σ) g h i =
      d.normalizer *
        (rawSourceCoefficient (σ := σ) T g h
          (d.scale₁ false / idealNorm K (B.plainDivisor 0))
          (d.scale₂ false / idealNorm K (B.plainDivisor (Fin.succ 0))) d.base
          (fun j => d.length (SlotRestriction.index B.keep j))
          (fun I => d.rectangleLeftWeight false (B.plainDivisor 0 * I))
          (fun I => d.rightWeight false (B.plainDivisor (Fin.succ 0) * I))
          (fun j => d.slotWeight (SlotRestriction.index B.keep j)) i -
         rawSourceCoefficient (σ := σ) T g h
          (d.scale₁ true / idealNorm K (B.plainDivisor 0))
          (d.scale₂ true / idealNorm K (B.plainDivisor (Fin.succ 0))) d.base
          (fun j => d.length (SlotRestriction.index B.keep j))
          (fun I => d.rectangleLeftWeight true (B.plainDivisor 0 * I))
          (fun I => d.rightWeight true (B.plainDivisor (Fin.succ 0) * I))
          (fun j => d.slotWeight (SlotRestriction.index B.keep j)) i) := by
  sorry

/-- Each passive summand is now the genuine quotient table and its
actual frequency-dependent frozen scalar.  Nothing is estimated in
this identity. -/
theorem passiveColumn_eq_quotients (T : FixedChildCharacters K B.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) (g h : A.R)
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    passiveColumn (σ := σ) W B T M g h firstSign negative ξ =
      ∑ a ∈ (labels W B A M).attach,
        sign a.val *
          ((branch W B A M a).scalar (σ := σ) T g h
            (table W B A T).base (table W B A T).length (table W B A T).slotWeight *
            jointFourierColumn
              (childCartesianColumns ((table W B A T).allocate (branch W B A M a)).plain₁
                ((table W B A T).allocate (branch W B A M a)).plain₂
                ((table W B A T).allocate (branch W B A M a)).slots)
              (((table W B A T).allocate (branch W B A M a)).frequencyWhole (σ := σ) g h)
              (fun i => rawSourceLocation (plainLocation₁ B firstSign negative)
                (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)
                (CanonicalLiteralAllocationAtoms.reconstruct (branch W B A M a) i)) ξ) := by
  sorry

section PhaseChoice

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The original first path determines this choice before any passive
allocation.  The amplified case records only its actual pool element. -/
inductive PhaseChoice (F : FixedPhases A) (C : A.GeneralArithmeticContext σ η hS) where
  | unamplified
  | amplified (p : ExteriorPrime A) (e : AmplifierValuation)
      (pool_element : F.poolElement = generator C p ^ (2 * e.multiplicity))

namespace PhaseChoice

variable {F : FixedPhases A} {C : A.GeneralArithmeticContext σ η hS}

def phases (choice : PhaseChoice F C) : FixedPhases A :=
  match choice with
  | .unamplified => F
  | .amplified p e _ => CanonicalLiteralPaidCharacters.reducedPhases F C p e

def mask (choice : PhaseChoice F C) (extra : HeckeGeneral.Analysis.NonzeroIdeal K) :
    HeckeGeneral.Analysis.NonzeroIdeal K :=
  match choice with
  | .unamplified => extra
  | .amplified p e _ => CanonicalLiteralPaidCharacters.passiveMask extra p e

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}

def calibration (choice : PhaseChoice F C)
    (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K) (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (data : MomentData K ω ψ) (count : data.geometry.slotCount = k)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h : A.R)
    (original : (sourceCharacters P R F parent oldMoving correction remaining extra index).Calibration
      (σ := σ) data count u g h) :
    ((CanonicalLiteralPaidCharacters.paidSourceCharacters P R choice.phases parent oldMoving
      correction remaining index).deleteMask (choice.mask extra)).Calibration
      (σ := σ) data count u g h := by
  cases choice with
  | unamplified =>
    exact CanonicalLiteralPaidCharacters.calibration_delete P R F parent oldMoving
      correction remaining extra index data count u g h original
  | amplified p e hpool =>
    exact CanonicalLiteralPaidCharacters.calibration_reduced P R F parent oldMoving
      correction remaining extra index hroot hemb C p e hpool data count u g h original

end PhaseChoice
end PhaseChoice

section ActualSource

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}
variable (F : FixedPhases A) (parent : MomentData K ω ψ)
variable (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (S : ActualSecondCorrelationRows A σ H ι)
variable (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (firstSign : ℝ) (negative : Bool)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (row : CanonicalOriginalPhaseCalibration.PatternSector P S C pattern ν)

local notation "child" => (fun r ξ => CanonicalLiteralAllocatedData.data P R W B F parent
  oldMoving correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity pattern ν
  remaining extra m q inverse index r firstSign negative ξ)
local notation "rowIdeal" => (S.extractedRow C row.val.val).momentIdeal
local notation "rowElement" => (S.extractedRow C row.val.val).element
local notation "signedFactor" => (if negative then -(S.factor C row.val.val.val)
  else S.factor C row.val.val.val)

/-- Both signs use the original extracted row and the original chosen
unit-sector representative.  The right side changes only its actual
frequency sign and the already recorded Fourier locations. -/
def actualSignedDictionary (rectangle : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    ((sourceCharacters P R F parent oldMoving correction remaining extra index).restrictSlots
      B.keep).Calibration (σ := σ) (child rectangle ξ) rfl rowIdeal signedFactor rowElement := by
  cases negative with
  | false =>
    exact CanonicalLiteralAllocatedData.actualDictionary P R W B F parent oldMoving
      correction hcorr C pattern ν remaining extra m q inverse index rectangle firstSign false
      S hone hroot hemb row ξ
  | true =>
    exact CanonicalLiteralAllocatedData.actualNegativeDictionary P R W B F parent oldMoving
      correction hcorr C pattern ν remaining extra m q inverse index rectangle firstSign true
      S hone hroot hemb row ξ

include hcorr m q inverse hone hroot hemb in
/-- The actual row, mask, source characters and finite support
construct the passive expansion.  There is no final support bound,
allowed-row assumption or supplied whole-column identity. -/
theorem actual_centered_allocations
    (choice : PhaseChoice F C)
    (hcharacters : d.characters = sourceCharacters P R F parent oldMoving correction
      remaining extra index)
    (firstSupport : Finset (Ideal (𝓞 K))) (hfirst : ∀ v ∈ firstSupport, Prime v)
    (hextra : extra = literalDeletionIdeal firstSupport hfirst)
    (hl : ∀ i, 0 < S.leftMultiplicity i) (hr : ∀ i, 0 < S.rightMultiplicity i)
    (support : d.SupportData ((primeSupport A.cS ∪ firstSupport) ∪
      primeSupport (primePowerProduct S.primes S.leftMultiplicity).val))
    (hplain₁ : B.plain₁ = d.plain₁) (hplain₂ : B.plain₂ = d.plain₂)
    (hslots : B.slots = d.slots) (ξ : WithLp 2 (ℝ × ℝ)) :
    centeredColumn (σ := σ) (d := d) B (d.characters.restrictSlots B.keep)
      signedFactor rowElement firstSign negative ξ =
    passiveColumn (σ := σ) W B
      ((CanonicalLiteralPaidCharacters.paidSourceCharacters P R choice.phases parent oldMoving
        correction remaining index).restrictSlots B.keep)
      (choice.mask extra) signedFactor rowElement firstSign negative ξ := by
  sorry

end ActualSource

end CanonicalLiteralPassiveSource
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSource.profiles
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSource.table_frequencyWhole
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSource.passiveColumn_eq_quotients
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSource.actualSignedDictionary
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSource.actual_centered_allocations
