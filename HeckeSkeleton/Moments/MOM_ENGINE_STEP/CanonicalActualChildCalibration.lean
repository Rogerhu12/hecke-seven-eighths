import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualJointSources
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalBoundedChildSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFixedThetaClosure

/-!
# The bounded complete child of the same actual joint source

Both original rectangles and the amplified pool use their literal
allocation and retained occurrences. The profiles are constructed from
that source's two physical norm divisions and original evaluation.
The arithmetic dictionary is proved on the actual pattern/sector subtype,
including the negative right frequency. No completed child calibration,
profile identity or transformed dictionary is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalSecondFactorAssembly CanonicalActualSecondRectangles
open CanonicalCoreProfileIdentification

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

private theorem original_scale_positive (Z Y n : ℝ) (hZ : 1 < Z)
    (comparison : Bool) (hY : comparison = true → 0 < Y) :
    0 < (if comparison then Y else Z ^ n) := by
  split_ifs with h
  · exact hY h
  · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _

private theorem retained_index_injective {k : ℕ} (keep : Finset (Fin k)) :
    Function.Injective (SlotRestriction.index keep) := by
  intro i j hij
  exact keep.equivFin.symm.injective (Subtype.ext hij)

namespace Main

variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable [IsPrincipalIdealRing A.R]
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (x : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data x))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 1 < Z)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin (data x).geometry.slotCount → Finset (HeightOneSpectrum (𝓞 K)))
variable (firstCommon : A.Exterior)
variable (b₁ : SupportCartesianBranch S₁ S₂ S (primeSupport firstCommon.val))
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {τ : Type*} [Fintype τ] [DecidableEq τ]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (primes : τ → ExteriorPrime A) (m n : τ → ℕ) (firstRight : Bool)
variable (δ : NonzeroRingElements A.R) (firstTilt : ℝ)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (J₁ : AllocationColumn K b₁.keep.card → A.Exterior)
variable (hJ₁ : ∀ i ∈ b₁.residualColumns, (J₁ i).val = allocationColumnIdeal i)
variable (hactive : ∀ i ∈ b₁.residualColumns,
  IsCoprime (J₁ i).val (firstActiveIdeal primes m n).val)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable (secondCommon : A.Exterior)
local notation "L₁" => SupportCartesian.plainResidual S₁
  (primeSupport firstCommon.val) b₁.plainExtract₁
local notation "L₂" => SupportCartesian.plainResidual S₂
  (primeSupport firstCommon.val) b₁.plainExtract₂
local notation "idx₁" => SlotRestriction.index b₁.keep
local notation "Slots" => fun j => SupportCartesian.primeLive
  (S (idx₁ j)) (primeSupport firstCommon.val)
variable (b₂ : SupportCartesianBranch L₁ L₂ Slots (primeSupport secondCommon.val))
variable (J₂ : AllocationColumn K b₂.keep.card → A.Exterior)
variable (hJ₂ : ∀ i ∈ b₂.residualColumns, (J₂ i).val = allocationColumnIdeal i)
variable (secondTilt : ℝ) (rowOffset : H → ℝ)
variable (comparison : Bool)
variable (hcomparison : comparison = true →
  0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂)
local notation "idx₂" => SlotRestriction.index b₂.keep
local notation "factors" => fun ξ => originalSecondResidualCoreFactors Q x W a Z t Y₁ Y₂ hZ
  S₁ S₂ S firstCommon b₁ C primes m n firstRight δ firstTilt ξ hroot hemb
  J₁ hJ₁ hactive rows side χ secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
local notation "L₁₂" => SupportCartesian.plainResidual L₁
  (primeSupport secondCommon.val) b₂.plainExtract₁
local notation "L₂₂" => SupportCartesian.plainResidual L₂
  (primeSupport secondCommon.val) b₂.plainExtract₂
local notation "Slots₂" => fun j => SupportCartesian.primeLive
  (Slots (idx₂ j)) (primeSupport secondCommon.val)
variable (allocationIdeal : Ideal (𝓞 K))
variable (selection : primeSupport allocationIdeal → Finset (Fin (b₂.keep.card + 2)))
variable (hne : (WholeAllocation.pairedAllocatedColumns allocationIdeal selection
  L₁₂ L₂₂ Slots₂ id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "joint" => CanonicalActualJointSources.jointSource Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
local notation "prefix" => ((Q.moving.append
    (CanonicalSecondRectangularFactors.firstMovingFactors P R C primes m n firstRight δ)).append
      (CanonicalSecondRectangularFactors.secondMaskMovingFactors P R
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)))
local notation "remaining" => Q.remaining * exteriorMomentIdeal firstCommon
local notation "idx" => fun i => idx₁ (idx₂ (SlotRestriction.index joint.allocation.keep i))
local notation "slope" => if firstRight then 1 else -1
local notation "H₁" => (if comparison then Y₁ else Z ^ a.n₁) /
  idealNorm K b₁.plainDivisor₁ / idealNorm K b₂.plainDivisor₁
local notation "H₂" => (if comparison then Y₂ else Z ^ a.n₂) /
  idealNorm K b₁.plainDivisor₂ / idealNorm K b₂.plainDivisor₂
local notation "primeScale" => fun i => Z ^ ((data x).geometry.slots (idx i)).length
local notation "hH₁" => div_pos
  (div_pos (original_scale_positive Z Y₁ a.n₁ hZ comparison
    (fun h => (hcomparison h).1)) (idealNorm_pos K b₁.plainDivisor₁))
  (idealNorm_pos K b₂.plainDivisor₁)
local notation "hH₂" => div_pos
  (div_pos (original_scale_positive Z Y₂ a.n₂ hZ comparison
    (fun h => (hcomparison h).2.1)) (idealNorm_pos K b₁.plainDivisor₂))
  (idealNorm_pos K b₂.plainDivisor₂)
local notation "hPrime" => fun i => Real.rpow_pos_of_pos (zero_lt_one.trans hZ)
  (((data x).geometry.slots (idx i)).length)

variable (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

/-- The row type carries both actual arithmetic classes. All original
source fields and the actual final allocation are retained. -/
def patternSource : ActualAllocatedSource A (WithLp 2 (ℝ × ℝ))
    (CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector) b₂.keep.card :=
  CanonicalActualJointSources.byPatternSector P rows C joint pattern sector

local notation "actual" => patternSource Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector

variable (budget : ℝ) (anchor : NonzeroIdeal K)
variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {P₀ : ℝ}
variable (raw : RawProfileWindow rowDomain heightDomain window
  orders (data x) P₀)
variable (hanchor : anchor ∈ rowDomain) (hheight : t ∈ heightDomain)
variable (hpositive : window ⊆ Set.Ioi 0) (annulus : ℝ) (hAnnulus : 1 ≤ annulus)

/-- The child is produced from this actual source. Its compensation
uses the true comparison scales; its retained slots are original occurrences. -/
def childData (ξ : WithLp 2 (ℝ × ℝ)) : MomentData K ω ψ :=
  CanonicalBoundedChildData.boundedData (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus (firstDirection slope)
    (secondDirection (CanonicalActualJointSources.secondLogSlope side)) ξ

local notation "child" => childData Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector budget anchor raw hanchor hheight hpositive annulus hAnnulus

@[simp] theorem count (ξ : WithLp 2 (ℝ × ℝ)) :
    (child ξ).geometry.slotCount = actual.allocation.keep.card := rfl

@[simp] theorem theta (ξ : WithLp 2 (ℝ × ℝ)) :
    (child ξ).theta = (data x).theta := rfl

@[simp] theorem slot_coefficient (ξ : WithLp 2 (ℝ × ℝ))
    (i : Fin actual.allocation.keep.card) :
    (child ξ).slotCoefficient i = (data x).slotCoefficient (idx i) := rfl

/-- The same three original restrictions produce the child's length. -/
theorem lengths (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin actual.allocation.keep.card) :
    ((child ξ).geometry.slots i).length = actual.childLength i := by
  change ((data x).geometry.slots (idx i)).length =
    joint.length (SlotRestriction.index joint.allocation.keep i)
  exact (CanonicalActualJointSources.joint_length Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
    (SlotRestriction.index joint.allocation.keep i)).symm

theorem index_injective : Function.Injective idx :=
  (retained_index_injective b₁.keep).comp
    ((retained_index_injective b₂.keep).comp
      (retained_index_injective joint.allocation.keep))

/-- Slot restriction is exactly composition with the original indices;
it introduces no new character or theta correction. -/
theorem characters (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector) :
    (actual.characters q).restrictSlots actual.allocation.keep =
      movingSourceCharacters (data x) Q.correction prefix remaining idx := by
  change (joint.characters q.val.val).restrictSlots joint.allocation.keep = _
  rw [CanonicalActualJointSources.joint_characters Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val]
  rfl

/-- The whole arithmetic dictionary, including all mask zeros, is
constructed for every row of the actual subtype and both Fourier modes. -/
def dictionary (hone : (1 : HeckeCharacter K) ∈ (data x).theta)
    (ξ : WithLp 2 (ℝ × ℝ))
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector) :
    ((actual.characters q).restrictSlots actual.allocation.keep).Calibration (σ := σ)
      (child ξ) rfl (actual.row q).momentIdeal
        (actual.extractedFactor q) (actual.row q).element := by
  rw [characters Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector q]
  change (movingSourceCharacters (data x) Q.correction prefix remaining idx).Calibration
    (σ := σ) (child ξ) rfl (joint.row q.val.val).momentIdeal
      (joint.extractedFactor q.val.val) (joint.row q.val.val).element
  rw [CanonicalActualJointSources.joint_row_momentIdeal Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val,
    CanonicalActualJointSources.joint_extractedFactor Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val,
    CanonicalActualJointSources.joint_row_element Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val]
  have hpositiveDictionary := CanonicalBoundedChildData.calibration (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus (firstDirection slope)
    (secondDirection (CanonicalActualJointSources.secondLogSlope side))
      hone hroot hemb (rows.extractedRow C q.val.val)
      (rows.factor_nonunitClass C pattern q.val) q.property ξ
  have hnegativeDictionary := CanonicalBoundedChildData.negativeCalibration (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus (firstDirection slope)
    (secondDirection (CanonicalActualJointSources.secondLogSlope side))
      hone hroot hemb (rows.extractedRow C q.val.val)
      (rows.factor_nonunitClass C pattern q.val) q.property ξ
  cases side with
  | left => exact hpositiveDictionary
  | right => exact hnegativeDictionary

/-- Original finite slot membership is transported by the actual index. -/
theorem slot_in_theta
    (hslot : ∀ i, (data x).slotCoefficient i ∈ (data x).theta)
    (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin actual.allocation.keep.card) :
    (child ξ).slotCoefficient i ∈ (child ξ).theta :=
  hslot (idx i)

/-- Only the original fixed background and theta are used to classify
principal children. The moving prefix is never inserted into theta. -/
theorem principal_in_theta (hone : (1 : HeckeCharacter K) ∈ (data x).theta)
    (hbackground : FiniteOrder ψ → ψ ∈ (data x).theta ∧ ψ⁻¹ ∈ (data x).theta)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : NonzeroIdeal K)
    (hprincipal : (child ξ).plainBackground * (child ξ).rowCharacter u = 1) :
    (child ξ).rowCharacter u ∈ (child ξ).theta :=
  OriginalFixedThetaClosure.principal_in_theta (child ξ) hone hbackground u hprincipal

variable (hallowed : (data x).allowedRow anchor) (hwindow : window ⊆ Set.Iic annulus)
variable (hδ₁ : 0 ≤ firstTilt) (hδ₂ : 0 ≤ secondTilt)
variable (hδ : firstTilt + secondTilt ≤ 1 / 2)

/-- The actual left atom and actual joint location are the same bounded
child profile after the last literal allocation divisor. -/
include hallowed hwindow hδ₁ hδ₂ hδ in
theorem left_profile (ξ ζ : ℝ)
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (I : NonzeroIdeal K) :
    actual.leftWeight q (actual.allocation.plainDivisor 0 * I) *
      jointPhase (WithLp.toLp 2 (ξ, ζ))
        (actual.leftLocation q (actual.allocation.plainDivisor 0 * I)) =
      (child (WithLp.toLp 2 (ξ, ζ))).plainTest₁.profile
        (actual.row q).momentIdeal t
        (idealNorm K I / (actual.scale₁ / idealNorm K (actual.allocation.plainDivisor 0))) := by
  change joint.leftWeight q.val.val (joint.allocation.plainDivisor 0 * I) *
    jointPhase _ (joint.leftLocation q.val.val (joint.allocation.plainDivisor 0 * I)) = _
  rw [CanonicalActualJointSources.joint_leftWeight Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val,
    CanonicalActualJointSources.joint_leftLocation Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val]
  have hsourceScale : actual.scale₁ = H₁ :=
    CanonicalActualJointSources.joint_leftScale Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
  rw [hsourceScale]
  change _ = (child (WithLp.toLp 2 (ξ, ζ))).plainTest₁.profile
    (actual.row q).momentIdeal t
    (idealNorm K I / (H₁ / idealNorm K (joint.allocation.plainDivisor 0)))
  exact CanonicalBoundedChildData.left_profile (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus
    W hallowed hwindow hδ₁ hδ₂ hδ slope
    (CanonicalActualJointSources.secondLogSlope side)
    (if comparison then Y₁ else Z ^ a.n₁)
    (original_scale_positive Z Y₁ a.n₁ hZ comparison (fun h => (hcomparison h).1))
    b₁.plainDivisor₁ (joint.allocation.plainDivisor 0) I rfl
    (actual.row q).momentIdeal t ξ ζ

/-- The right source retains its positive second log slope after the
single whole conjugation. Its first phase is the same original phase. -/
include hallowed hwindow hδ₁ hδ₂ hδ in
theorem right_profile (ξ ζ : ℝ)
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (I : NonzeroIdeal K) :
    actual.rightWeight q (actual.allocation.plainDivisor (Fin.succ 0) * I) *
      jointPhase (WithLp.toLp 2 (ξ, ζ))
        (actual.rightLocation q (actual.allocation.plainDivisor (Fin.succ 0) * I)) =
      (child (WithLp.toLp 2 (ξ, ζ))).plainTest₂.profile
        (actual.row q).momentIdeal t
        (idealNorm K I /
          (actual.scale₂ / idealNorm K (actual.allocation.plainDivisor (Fin.succ 0)))) := by
  change joint.rightWeight q.val.val (joint.allocation.plainDivisor (Fin.succ 0) * I) *
    jointPhase _ (joint.rightLocation q.val.val (joint.allocation.plainDivisor (Fin.succ 0) * I)) = _
  rw [CanonicalActualJointSources.joint_rightWeight Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val,
    CanonicalActualJointSources.joint_rightLocation Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val]
  have hsourceScale : actual.scale₂ = H₂ :=
    CanonicalActualJointSources.joint_rightScale Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
  rw [hsourceScale]
  change _ = (child (WithLp.toLp 2 (ξ, ζ))).plainTest₂.profile
    (actual.row q).momentIdeal t
    (idealNorm K I / (H₂ / idealNorm K (joint.allocation.plainDivisor (Fin.succ 0))))
  exact CanonicalBoundedChildData.right_profile (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus
    W hallowed hwindow hδ₁ hδ₂ hδ slope
    (CanonicalActualJointSources.secondLogSlope side)
    (if comparison then Y₂ else Z ^ a.n₂)
    (original_scale_positive Z Y₂ a.n₂ hZ comparison (fun h => (hcomparison h).2.1))
    b₁.plainDivisor₂ (joint.allocation.plainDivisor (Fin.succ 0)) I rfl
    (actual.row q).momentIdeal t ξ ζ

/-- The last live occurrence uses its original prime profile and
length. No aggregate prime-bound hypothesis enters the identity. -/
include hwindow hδ₁ hδ₂ hδ in
theorem prime_profile (ξ ζ : ℝ)
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (i : Fin actual.allocation.keep.card) (p₀ : HeightOneSpectrum (𝓞 K)) :
    actual.slotWeight q (SlotRestriction.index actual.allocation.keep i) p₀ *
      jointPhase (WithLp.toLp 2 (ξ, ζ))
        (actual.slotLocation q (SlotRestriction.index actual.allocation.keep i) p₀) =
      ((child (WithLp.toLp 2 (ξ, ζ))).geometry.slots i).profile t
        ((Ideal.absNorm p₀.asIdeal : ℝ) /
          actual.base ^ ((child (WithLp.toLp 2 (ξ, ζ))).geometry.slots i).length) := by
  change joint.slotWeight q.val.val (SlotRestriction.index joint.allocation.keep i) p₀ *
    jointPhase _ (joint.slotLocation q.val.val (SlotRestriction.index joint.allocation.keep i) p₀) = _
  rw [CanonicalActualJointSources.joint_slotWeight Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val,
    CanonicalActualJointSources.joint_slotLocation Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val]
  have hsourceBase : actual.base = Z := CanonicalActualJointSources.joint_base Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
  rw [hsourceBase]
  change _ = ((child (WithLp.toLp 2 (ξ, ζ))).geometry.slots i).profile t
    ((Ideal.absNorm p₀.asIdeal : ℝ) / primeScale i)
  exact CanonicalBoundedChildData.prime_profile (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus
    hwindow hδ₁ hδ₂ hδ slope
    (CanonicalActualJointSources.secondLogSlope side) i p₀ t ξ ζ


/-- The actual profiles remain a norm-profile recipe on every allowed
child row. Their original anchor and evaluation height stay fixed. -/
def normProfiles : NormProfileRecipe child where
  left ξ _ y := (child ξ).plainTest₁.profile anchor t y
  right ξ _ y := (child ξ).plainTest₂.profile anchor t y
  left_eq _ _ _ _ _ := rfl
  right_eq _ _ _ _ _ := rfl

/-- This is the literal Fourier-profile package of the constructed child,
for the same allocation and physical comparison scales. -/
def originalLogProfiles : CanonicalLogProfiles.OriginalLogProfiles K ω ψ (WithLp 2 (ℝ × ℝ)) :=
  CanonicalBoundedChildData.originalLogProfiles (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus (firstDirection slope)
    (secondDirection (CanonicalActualJointSources.secondLogSlope side))

local notation "logProfiles" => originalLogProfiles Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector budget anchor raw hanchor hheight hpositive annulus hAnnulus

@[simp] theorem childData_eq_originalLogProfiles (ξ : WithLp 2 (ℝ × ℝ)) :
    child ξ = logProfiles.moving ξ := rfl

/-- The pre-Fourier profile window is constructed from the same original
window. Each real clipped compensation costs at most sqrt(annulus). -/
def originalWindow (hP : 0 ≤ P₀) :
    RawProfileWindow Set.univ Set.univ window orders logProfiles.original
      (Real.sqrt annulus * P₀) := by
  let base := CanonicalBoundedChildData.baseData (data x) prefix Q.correction
    (Q.correction_mem x) C rows.primes rows.leftMultiplicity rows.rightMultiplicity
    pattern sector remaining budget anchor t idx
  let scalars := OriginalClippedGaussProfiles.profileScalars base H₁ H₂ primeScale
    b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt hH₁ hH₂ hPrime hAnnulus
  let original := CanonicalBoundedChildData.baseRawWindow (data x) prefix Q.correction
    (Q.correction_mem x) C rows.primes rows.leftMultiplicity rows.rightMultiplicity
    pattern sector remaining budget anchor t idx raw hanchor hheight
  exact scalars.rawWindow base hP original (Real.sqrt annulus)
    (OriginalClippedGaussProfiles.sqrt_annulus_one_le hAnnulus)
    (min_le_right _ _) (min_le_right _ _) (fun _ => min_le_right _ _)

/-- The complete arithmetic recipe is generated with these same data;
all original prefix factors and the second active factors remain literal. -/
def movingRecipe : CompleteMovingRowRecipe A P R child :=
  CanonicalBoundedChildData.movingRecipe (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus (firstDirection slope)
    (secondDirection (CanonicalActualJointSources.secondLogSlope side))

local notation "recipe" => movingRecipe Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector budget anchor raw hanchor hheight hpositive annulus hAnnulus

theorem fullJointBudget (width : ℝ) (hbudget : budget = Z ^ width) :
    recipe.FullJointBudget Z width := by
  intro ξ u hu
  exact hu.2.trans_eq hbudget

/-- This numerical transport consumes the bound on the actual original
frequency ideal and complete mask. It derives allowed-row membership
from the proved factor norm identity, without an admissible-row premise. -/
theorem allowed_of_source_norm
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (hsource : A.exteriorNorm (actual.originalIdeal q) *
        idealNorm K (recipe.moving.fullMaskSupport recipe.remaining) ≤
      actual.normFactor q * budget) (ξ : WithLp 2 (ℝ × ℝ)) :
    (child ξ).allowedRow (actual.row q).momentIdeal := by
  refine ⟨(HeckeAxiom.exteriorEquiv A (actual.row q).ideal).property, ?_⟩
  apply le_of_mul_le_mul_left _ (actual.row q).factor_pos
  change actual.normFactor q * (A.exteriorNorm (actual.row q).ideal *
    idealNorm K (recipe.moving.fullMaskSupport recipe.remaining)) ≤ actual.normFactor q * budget
  rw [← mul_assoc, ← (actual.row q).norm_factor]
  exact hsource

/-- Coordinate-free form used by the complete source calibration. -/
include hallowed hwindow hδ₁ hδ₂ hδ in
theorem left_profile_joint (mode : WithLp 2 (ℝ × ℝ))
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (I : NonzeroIdeal K) :
    actual.leftWeight q (actual.allocation.plainDivisor 0 * I) *
      jointPhase mode (actual.leftLocation q (actual.allocation.plainDivisor 0 * I)) =
      (child mode).plainTest₁.profile (actual.row q).momentIdeal t
        (idealNorm K I / (actual.scale₁ / idealNorm K (actual.allocation.plainDivisor 0))) := by
  exact
    left_profile Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector budget anchor raw hanchor hheight hpositive annulus hAnnulus
      hallowed hwindow hδ₁ hδ₂ hδ (WithLp.ofLp mode).1 (WithLp.ofLp mode).2 q I

include hallowed hwindow hδ₁ hδ₂ hδ in
theorem right_profile_joint (mode : WithLp 2 (ℝ × ℝ))
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (I : NonzeroIdeal K) :
    actual.rightWeight q (actual.allocation.plainDivisor (Fin.succ 0) * I) *
      jointPhase mode
        (actual.rightLocation q (actual.allocation.plainDivisor (Fin.succ 0) * I)) =
      (child mode).plainTest₂.profile (actual.row q).momentIdeal t
        (idealNorm K I /
          (actual.scale₂ / idealNorm K (actual.allocation.plainDivisor (Fin.succ 0)))) := by
  exact
    right_profile Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector budget anchor raw hanchor hheight hpositive annulus hAnnulus
      hallowed hwindow hδ₁ hδ₂ hδ (WithLp.ofLp mode).1 (WithLp.ofLp mode).2 q I

include hwindow hδ₁ hδ₂ hδ in
theorem prime_profile_joint (mode : WithLp 2 (ℝ × ℝ))
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (i : Fin actual.allocation.keep.card) (p₀ : HeightOneSpectrum (𝓞 K)) :
    actual.slotWeight q (SlotRestriction.index actual.allocation.keep i) p₀ *
      jointPhase mode (actual.slotLocation q (SlotRestriction.index actual.allocation.keep i) p₀) =
      ((child mode).geometry.slots i).profile t
        ((Ideal.absNorm p₀.asIdeal : ℝ) / actual.base ^ ((child mode).geometry.slots i).length) := by
  exact
    prime_profile Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector budget anchor raw hanchor hheight hpositive annulus hAnnulus
      hwindow hδ₁ hδ₂ hδ (WithLp.ofLp mode).1 (WithLp.ofLp mode).2 q i p₀


section OriginalSupports

variable (hm : ∀ i, 0 < rows.leftMultiplicity i)
variable (hn : ∀ i, 0 < rows.rightMultiplicity i)
variable (secondRight : Bool)
variable (hcommon : secondCommon = primePowerProduct rows.primes
  (if secondRight then rows.rightMultiplicity else rows.leftMultiplicity))

/-- The actual allocation carrier is computed from the two original
common extractions. Only the original parent support inclusion is used. -/
include hm hn secondRight hcommon in
theorem effective_left_support
    (hS₁ : exteriorPlainSupport (A := A) (data x).plainTest₁ anchor
      (if comparison then Y₁ else Z ^ a.n₁) t ⊆ S₁)
    (hExterior : ∀ J ∈ S₁, IsCoprime J A.cS)
    (mode : WithLp 2 (ℝ × ℝ)) (u : NonzeroIdeal K) :
    effectivePlainSupport (child mode) (child mode).plainTest₁ u
      (actual.scale₁ / idealNorm K (actual.allocation.plainDivisor 0)) t ⊆
        actual.allocation.childPlain₁ := by
  let finalAllocation := actual.allocation
  let finalIndex := idx
  have hB : finalAllocation.plain₁ = L₁₂ := by cases side <;> rfl
  have hscale : actual.scale₁ = H₁ := CanonicalActualJointSources.joint_leftScale Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
  rw [hscale]
  subst secondCommon
  exact CanonicalBoundedChildSupport.effective_left_support (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    Q.remaining firstCommon budget anchor t finalIndex raw hanchor hheight hpositive
    H₁ H₂ (fun i => Z ^ ((data x).geometry.slots (finalIndex i)).length)
    b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt hH₁ hH₂
    (fun i => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hAnnulus
    (firstDirection slope) (secondDirection (CanonicalActualJointSources.secondLogSlope side))
    rows.primes_injective hm hn secondRight b₁ b₂ finalAllocation
    (if comparison then Y₁ else Z ^ a.n₁) hS₁ hExterior hB mode u t

include hm hn secondRight hcommon in
theorem effective_right_support
    (hS₂ : exteriorPlainSupport (A := A) (data x).plainTest₂ anchor
      (if comparison then Y₂ else Z ^ a.n₂) t ⊆ S₂)
    (hExterior : ∀ J ∈ S₂, IsCoprime J A.cS)
    (mode : WithLp 2 (ℝ × ℝ)) (u : NonzeroIdeal K) :
    effectivePlainSupport (child mode) (child mode).plainTest₂ u
      (actual.scale₂ / idealNorm K (actual.allocation.plainDivisor (Fin.succ 0))) t ⊆
        actual.allocation.childPlain₂ := by
  let finalAllocation := actual.allocation
  let finalIndex := idx
  have hB : finalAllocation.plain₂ = L₂₂ := by cases side <;> rfl
  have hscale : actual.scale₂ = H₂ := CanonicalActualJointSources.joint_rightScale Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
  rw [hscale]
  subst secondCommon
  exact CanonicalBoundedChildSupport.effective_right_support (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    Q.remaining firstCommon budget anchor t finalIndex raw hanchor hheight hpositive
    H₁ H₂ (fun i => Z ^ ((data x).geometry.slots (finalIndex i)).length)
    b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt hH₁ hH₂
    (fun i => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hAnnulus
    (firstDirection slope) (secondDirection (CanonicalActualJointSources.secondLogSlope side))
    rows.primes_injective hm hn secondRight b₁ b₂ finalAllocation
    (if comparison then Y₂ else Z ^ a.n₂) hS₂ hExterior hB mode u t

/-- The last child slots are the actual intersection of all three live
occurrence selections. The full arithmetic mask excludes both commons. -/
include hm hn secondRight hcommon in
theorem effective_prime_support
    (hSlots : ∀ i, exteriorPrimeSupport (A := A) ((data x).geometry.slots i) Z t ⊆ S i)
    (mode : WithLp 2 (ℝ × ℝ)) (u : NonzeroIdeal K)
    (i : Fin actual.allocation.keep.card) :
    effectivePrimeSupport (child mode) i u actual.base t ⊆ actual.allocation.childSlots i := by
  let finalAllocation := actual.allocation
  let finalIndex := idx
  have hB : finalAllocation.slots = Slots₂ := by cases side <;> rfl
  have hindex : finalIndex i = idx₁ (idx₂ (SlotRestriction.index finalAllocation.keep i)) := rfl
  have hbase : actual.base = Z := CanonicalActualJointSources.joint_base Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
  rw [hbase]
  subst secondCommon
  exact CanonicalBoundedChildSupport.effective_prime_support (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    Q.remaining firstCommon budget anchor t finalIndex raw hanchor hheight hpositive
    H₁ H₂ (fun i => Z ^ ((data x).geometry.slots (finalIndex i)).length)
    b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt hH₁ hH₂
    (fun i => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hAnnulus
    (firstDirection slope) (secondDirection (CanonicalActualJointSources.secondLogSlope side))
    rows.primes_injective hm hn secondRight b₁ b₂ finalAllocation
    Z hSlots hB i i hindex mode u t

end OriginalSupports

end Main

namespace Pool

open CanonicalActualPoolRectangles

variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable [IsPrincipalIdealRing A.R]
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (x : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data x))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 1 < Z)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin (data x).geometry.slotCount → Finset (HeightOneSpectrum (𝓞 K)))
variable (firstCommon : A.Exterior) (p : ExteriorPrime A) (v : ℕ) (hv : 0 < v)
variable (b₁ : SupportCartesianBranch S₁ S₂ S (primeSupport (combinedCommon firstCommon p v).val))
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {τ : Type*} [Fintype τ] [DecidableEq τ]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (primes : τ → ExteriorPrime A) (m n : τ → ℕ) (firstRight : Bool)
variable (δ : NonzeroRingElements A.R) (firstTilt : ℝ)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (J₁ : AllocationColumn K b₁.keep.card → A.Exterior)
variable (hJ₁ : ∀ i ∈ b₁.residualColumns, (J₁ i).val = allocationColumnIdeal i)
variable (hactive : ∀ i ∈ b₁.residualColumns,
  IsCoprime (J₁ i).val (firstActiveIdeal primes m n).val)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable (secondCommon : A.Exterior)
local notation "L₁" => SupportCartesian.plainResidual S₁
  (primeSupport (combinedCommon firstCommon p v).val) b₁.plainExtract₁
local notation "L₂" => SupportCartesian.plainResidual S₂
  (primeSupport (combinedCommon firstCommon p v).val) b₁.plainExtract₂
local notation "idx₁" => SlotRestriction.index b₁.keep
local notation "Slots" => fun j => SupportCartesian.primeLive
  (S (idx₁ j)) (primeSupport (combinedCommon firstCommon p v).val)
variable (b₂ : SupportCartesianBranch L₁ L₂ Slots (primeSupport secondCommon.val))
variable (J₂ : AllocationColumn K b₂.keep.card → A.Exterior)
variable (hJ₂ : ∀ i ∈ b₂.residualColumns, (J₂ i).val = allocationColumnIdeal i)
variable (secondTilt : ℝ) (rowOffset : H → ℝ)
variable (comparison : Bool)
variable (hcomparison : comparison = true →
  0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂)
local notation "idx₂" => SlotRestriction.index b₂.keep
local notation "factors" => fun ξ => originalPoolSecondCoreFactors Q x W a Z t Y₁ Y₂
  S₁ S₂ S firstCommon p v hv b₁ C primes m n firstRight δ firstTilt ξ hroot hemb
  J₁ hJ₁ hactive side χ rows secondCommon b₂ J₂ hJ₂ secondTilt rowOffset hZ comparison hcomparison
local notation "L₁₂" => SupportCartesian.plainResidual L₁
  (primeSupport secondCommon.val) b₂.plainExtract₁
local notation "L₂₂" => SupportCartesian.plainResidual L₂
  (primeSupport secondCommon.val) b₂.plainExtract₂
local notation "Slots₂" => fun j => SupportCartesian.primeLive
  (Slots (idx₂ j)) (primeSupport secondCommon.val)
variable (allocationIdeal : Ideal (𝓞 K))
variable (selection : primeSupport allocationIdeal → Finset (Fin (b₂.keep.card + 2)))
variable (hne : (WholeAllocation.pairedAllocatedColumns allocationIdeal selection
  L₁₂ L₂₂ Slots₂ id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "joint" => CanonicalActualJointSources.Pool.jointSource Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
local notation "prefix" => (((Q.moving.append
    (CanonicalSecondRectangularFactors.firstMovingFactors P R C primes m n firstRight δ)).append
      (poolMovingFactors (P := P) (R := R) C p v)).append
      (CanonicalSecondRectangularFactors.secondMaskMovingFactors P R
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)))
local notation "remaining" => Q.remaining * exteriorMomentIdeal (combinedCommon firstCommon p v)
local notation "idx" => fun i => idx₁ (idx₂ (SlotRestriction.index joint.allocation.keep i))
local notation "slope" => if firstRight then 1 else -1
local notation "H₁" => (if comparison then Y₁ else Z ^ a.n₁) /
  idealNorm K b₁.plainDivisor₁ / idealNorm K b₂.plainDivisor₁
local notation "H₂" => (if comparison then Y₂ else Z ^ a.n₂) /
  idealNorm K b₁.plainDivisor₂ / idealNorm K b₂.plainDivisor₂
local notation "primeScale" => fun i => Z ^ ((data x).geometry.slots (idx i)).length
local notation "hH₁" => div_pos
  (div_pos (original_scale_positive Z Y₁ a.n₁ hZ comparison
    (fun h => (hcomparison h).1)) (idealNorm_pos K b₁.plainDivisor₁))
  (idealNorm_pos K b₂.plainDivisor₁)
local notation "hH₂" => div_pos
  (div_pos (original_scale_positive Z Y₂ a.n₂ hZ comparison
    (fun h => (hcomparison h).2.1)) (idealNorm_pos K b₁.plainDivisor₂))
  (idealNorm_pos K b₂.plainDivisor₂)
local notation "hPrime" => fun i => Real.rpow_pos_of_pos (zero_lt_one.trans hZ)
  (((data x).geometry.slots (idx i)).length)

variable (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

/-- The row type carries both actual arithmetic classes. All original
source fields and the actual final allocation are retained. -/
def patternSource : ActualAllocatedSource A (WithLp 2 (ℝ × ℝ))
    (CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector) b₂.keep.card :=
  CanonicalActualJointSources.byPatternSector P rows C joint pattern sector

local notation "actual" => patternSource Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector

variable (budget : ℝ) (anchor : NonzeroIdeal K)
variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {P₀ : ℝ}
variable (raw : RawProfileWindow rowDomain heightDomain window
  orders (data x) P₀)
variable (hanchor : anchor ∈ rowDomain) (hheight : t ∈ heightDomain)
variable (hpositive : window ⊆ Set.Ioi 0) (annulus : ℝ) (hAnnulus : 1 ≤ annulus)

/-- The child is produced from this actual source. Its compensation
uses the true comparison scales; its retained slots are original occurrences. -/
def childData (ξ : WithLp 2 (ℝ × ℝ)) : MomentData K ω ψ :=
  CanonicalBoundedChildData.boundedData (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus (firstDirection slope)
    (secondDirection (CanonicalActualJointSources.secondLogSlope side)) ξ

local notation "child" => childData Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector budget anchor raw hanchor hheight hpositive annulus hAnnulus

@[simp] theorem count (ξ : WithLp 2 (ℝ × ℝ)) :
    (child ξ).geometry.slotCount = actual.allocation.keep.card := rfl

@[simp] theorem theta (ξ : WithLp 2 (ℝ × ℝ)) :
    (child ξ).theta = (data x).theta := rfl

@[simp] theorem slot_coefficient (ξ : WithLp 2 (ℝ × ℝ))
    (i : Fin actual.allocation.keep.card) :
    (child ξ).slotCoefficient i = (data x).slotCoefficient (idx i) := rfl

/-- The same three original restrictions produce the child's length. -/
theorem lengths (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin actual.allocation.keep.card) :
    ((child ξ).geometry.slots i).length = actual.childLength i := by
  change ((data x).geometry.slots (idx i)).length =
    joint.length (SlotRestriction.index joint.allocation.keep i)
  exact (CanonicalActualJointSources.Pool.joint_length Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
    (SlotRestriction.index joint.allocation.keep i)).symm

theorem index_injective : Function.Injective idx :=
  (retained_index_injective b₁.keep).comp
    ((retained_index_injective b₂.keep).comp
      (retained_index_injective joint.allocation.keep))

/-- Slot restriction is exactly composition with the original indices;
it introduces no new character or theta correction. -/
theorem characters (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector) :
    (actual.characters q).restrictSlots actual.allocation.keep =
      movingSourceCharacters (data x) Q.correction prefix remaining idx := by
  change (joint.characters q.val.val).restrictSlots joint.allocation.keep = _
  rw [CanonicalActualJointSources.Pool.joint_characters Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val]
  rfl

/-- The whole arithmetic dictionary, including all mask zeros, is
constructed for every row of the actual subtype and both Fourier modes. -/
def dictionary (hone : (1 : HeckeCharacter K) ∈ (data x).theta)
    (ξ : WithLp 2 (ℝ × ℝ))
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector) :
    ((actual.characters q).restrictSlots actual.allocation.keep).Calibration (σ := σ)
      (child ξ) rfl (actual.row q).momentIdeal
        (actual.extractedFactor q) (actual.row q).element := by
  rw [characters Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector q]
  change (movingSourceCharacters (data x) Q.correction prefix remaining idx).Calibration
    (σ := σ) (child ξ) rfl (joint.row q.val.val).momentIdeal
      (joint.extractedFactor q.val.val) (joint.row q.val.val).element
  rw [CanonicalActualJointSources.Pool.joint_row_momentIdeal Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val,
    CanonicalActualJointSources.Pool.joint_extractedFactor Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val,
    CanonicalActualJointSources.Pool.joint_row_element Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val]
  have hpositiveDictionary := CanonicalBoundedChildData.calibration (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus (firstDirection slope)
    (secondDirection (CanonicalActualJointSources.secondLogSlope side))
      hone hroot hemb (rows.extractedRow C q.val.val)
      (rows.factor_nonunitClass C pattern q.val) q.property ξ
  have hnegativeDictionary := CanonicalBoundedChildData.negativeCalibration (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus (firstDirection slope)
    (secondDirection (CanonicalActualJointSources.secondLogSlope side))
      hone hroot hemb (rows.extractedRow C q.val.val)
      (rows.factor_nonunitClass C pattern q.val) q.property ξ
  cases side with
  | left => exact hpositiveDictionary
  | right => exact hnegativeDictionary

/-- Original finite slot membership is transported by the actual index. -/
theorem slot_in_theta
    (hslot : ∀ i, (data x).slotCoefficient i ∈ (data x).theta)
    (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin actual.allocation.keep.card) :
    (child ξ).slotCoefficient i ∈ (child ξ).theta :=
  hslot (idx i)

/-- Only the original fixed background and theta are used to classify
principal children. The moving prefix is never inserted into theta. -/
theorem principal_in_theta (hone : (1 : HeckeCharacter K) ∈ (data x).theta)
    (hbackground : FiniteOrder ψ → ψ ∈ (data x).theta ∧ ψ⁻¹ ∈ (data x).theta)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : NonzeroIdeal K)
    (hprincipal : (child ξ).plainBackground * (child ξ).rowCharacter u = 1) :
    (child ξ).rowCharacter u ∈ (child ξ).theta :=
  OriginalFixedThetaClosure.principal_in_theta (child ξ) hone hbackground u hprincipal

variable (hallowed : (data x).allowedRow anchor) (hwindow : window ⊆ Set.Iic annulus)
variable (hδ₁ : 0 ≤ firstTilt) (hδ₂ : 0 ≤ secondTilt)
variable (hδ : firstTilt + secondTilt ≤ 1 / 2)

/-- The actual left atom and actual joint location are the same bounded
child profile after the last literal allocation divisor. -/
include hallowed hwindow hδ₁ hδ₂ hδ in
theorem left_profile (ξ ζ : ℝ)
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (I : NonzeroIdeal K) :
    actual.leftWeight q (actual.allocation.plainDivisor 0 * I) *
      jointPhase (WithLp.toLp 2 (ξ, ζ))
        (actual.leftLocation q (actual.allocation.plainDivisor 0 * I)) =
      (child (WithLp.toLp 2 (ξ, ζ))).plainTest₁.profile
        (actual.row q).momentIdeal t
        (idealNorm K I / (actual.scale₁ / idealNorm K (actual.allocation.plainDivisor 0))) := by
  change joint.leftWeight q.val.val (joint.allocation.plainDivisor 0 * I) *
    jointPhase _ (joint.leftLocation q.val.val (joint.allocation.plainDivisor 0 * I)) = _
  rw [CanonicalActualJointSources.Pool.joint_leftWeight Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val,
    CanonicalActualJointSources.Pool.joint_leftLocation Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val]
  have hsourceScale : actual.scale₁ = H₁ :=
    CanonicalActualJointSources.Pool.joint_leftScale Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
  rw [hsourceScale]
  change _ = (child (WithLp.toLp 2 (ξ, ζ))).plainTest₁.profile
    (actual.row q).momentIdeal t
    (idealNorm K I / (H₁ / idealNorm K (joint.allocation.plainDivisor 0)))
  exact CanonicalBoundedChildData.left_profile (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus
    W hallowed hwindow hδ₁ hδ₂ hδ slope
    (CanonicalActualJointSources.secondLogSlope side)
    (if comparison then Y₁ else Z ^ a.n₁)
    (original_scale_positive Z Y₁ a.n₁ hZ comparison (fun h => (hcomparison h).1))
    b₁.plainDivisor₁ (joint.allocation.plainDivisor 0) I rfl
    (actual.row q).momentIdeal t ξ ζ

/-- The right source retains its positive second log slope after the
single whole conjugation. Its first phase is the same original phase. -/
include hallowed hwindow hδ₁ hδ₂ hδ in
theorem right_profile (ξ ζ : ℝ)
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (I : NonzeroIdeal K) :
    actual.rightWeight q (actual.allocation.plainDivisor (Fin.succ 0) * I) *
      jointPhase (WithLp.toLp 2 (ξ, ζ))
        (actual.rightLocation q (actual.allocation.plainDivisor (Fin.succ 0) * I)) =
      (child (WithLp.toLp 2 (ξ, ζ))).plainTest₂.profile
        (actual.row q).momentIdeal t
        (idealNorm K I /
          (actual.scale₂ / idealNorm K (actual.allocation.plainDivisor (Fin.succ 0)))) := by
  change joint.rightWeight q.val.val (joint.allocation.plainDivisor (Fin.succ 0) * I) *
    jointPhase _ (joint.rightLocation q.val.val (joint.allocation.plainDivisor (Fin.succ 0) * I)) = _
  rw [CanonicalActualJointSources.Pool.joint_rightWeight Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val,
    CanonicalActualJointSources.Pool.joint_rightLocation Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val]
  have hsourceScale : actual.scale₂ = H₂ :=
    CanonicalActualJointSources.Pool.joint_rightScale Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
  rw [hsourceScale]
  change _ = (child (WithLp.toLp 2 (ξ, ζ))).plainTest₂.profile
    (actual.row q).momentIdeal t
    (idealNorm K I / (H₂ / idealNorm K (joint.allocation.plainDivisor (Fin.succ 0))))
  exact CanonicalBoundedChildData.right_profile (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus
    W hallowed hwindow hδ₁ hδ₂ hδ slope
    (CanonicalActualJointSources.secondLogSlope side)
    (if comparison then Y₂ else Z ^ a.n₂)
    (original_scale_positive Z Y₂ a.n₂ hZ comparison (fun h => (hcomparison h).2.1))
    b₁.plainDivisor₂ (joint.allocation.plainDivisor (Fin.succ 0)) I rfl
    (actual.row q).momentIdeal t ξ ζ

/-- The last live occurrence uses its original prime profile and
length. No aggregate prime-bound hypothesis enters the identity. -/
include hwindow hδ₁ hδ₂ hδ in
theorem prime_profile (ξ ζ : ℝ)
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (i : Fin actual.allocation.keep.card) (p₀ : HeightOneSpectrum (𝓞 K)) :
    actual.slotWeight q (SlotRestriction.index actual.allocation.keep i) p₀ *
      jointPhase (WithLp.toLp 2 (ξ, ζ))
        (actual.slotLocation q (SlotRestriction.index actual.allocation.keep i) p₀) =
      ((child (WithLp.toLp 2 (ξ, ζ))).geometry.slots i).profile t
        ((Ideal.absNorm p₀.asIdeal : ℝ) /
          actual.base ^ ((child (WithLp.toLp 2 (ξ, ζ))).geometry.slots i).length) := by
  change joint.slotWeight q.val.val (SlotRestriction.index joint.allocation.keep i) p₀ *
    jointPhase _ (joint.slotLocation q.val.val (SlotRestriction.index joint.allocation.keep i) p₀) = _
  rw [CanonicalActualJointSources.Pool.joint_slotWeight Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val,
    CanonicalActualJointSources.Pool.joint_slotLocation Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne q.val.val]
  have hsourceBase : actual.base = Z := CanonicalActualJointSources.Pool.joint_base Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
  rw [hsourceBase]
  change _ = ((child (WithLp.toLp 2 (ξ, ζ))).geometry.slots i).profile t
    ((Ideal.absNorm p₀.asIdeal : ℝ) / primeScale i)
  exact CanonicalBoundedChildData.prime_profile (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus
    hwindow hδ₁ hδ₂ hδ slope
    (CanonicalActualJointSources.secondLogSlope side) i p₀ t ξ ζ


/-- The actual profiles remain a norm-profile recipe on every allowed
child row. Their original anchor and evaluation height stay fixed. -/
def normProfiles : NormProfileRecipe child where
  left ξ _ y := (child ξ).plainTest₁.profile anchor t y
  right ξ _ y := (child ξ).plainTest₂.profile anchor t y
  left_eq _ _ _ _ _ := rfl
  right_eq _ _ _ _ _ := rfl

/-- This is the literal Fourier-profile package of the constructed child,
for the same allocation and physical comparison scales. -/
def originalLogProfiles : CanonicalLogProfiles.OriginalLogProfiles K ω ψ (WithLp 2 (ℝ × ℝ)) :=
  CanonicalBoundedChildData.originalLogProfiles (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus (firstDirection slope)
    (secondDirection (CanonicalActualJointSources.secondLogSlope side))

local notation "logProfiles" => originalLogProfiles Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector budget anchor raw hanchor hheight hpositive annulus hAnnulus

@[simp] theorem childData_eq_originalLogProfiles (ξ : WithLp 2 (ℝ × ℝ)) :
    child ξ = logProfiles.moving ξ := rfl

/-- The pre-Fourier profile window is constructed from the same original
window. Each real clipped compensation costs at most sqrt(annulus). -/
def originalWindow (hP : 0 ≤ P₀) :
    RawProfileWindow Set.univ Set.univ window orders logProfiles.original
      (Real.sqrt annulus * P₀) := by
  let base := CanonicalBoundedChildData.baseData (data x) prefix Q.correction
    (Q.correction_mem x) C rows.primes rows.leftMultiplicity rows.rightMultiplicity
    pattern sector remaining budget anchor t idx
  let scalars := OriginalClippedGaussProfiles.profileScalars base H₁ H₂ primeScale
    b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt hH₁ hH₂ hPrime hAnnulus
  let original := CanonicalBoundedChildData.baseRawWindow (data x) prefix Q.correction
    (Q.correction_mem x) C rows.primes rows.leftMultiplicity rows.rightMultiplicity
    pattern sector remaining budget anchor t idx raw hanchor hheight
  exact scalars.rawWindow base hP original (Real.sqrt annulus)
    (OriginalClippedGaussProfiles.sqrt_annulus_one_le hAnnulus)
    (min_le_right _ _) (min_le_right _ _) (fun _ => min_le_right _ _)

/-- The complete arithmetic recipe is generated with these same data;
all original prefix factors and the second active factors remain literal. -/
def movingRecipe : CompleteMovingRowRecipe A P R child :=
  CanonicalBoundedChildData.movingRecipe (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining budget anchor t idx raw hanchor hheight hpositive
    H₁ H₂ primeScale b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt
    hH₁ hH₂ hPrime hAnnulus (firstDirection slope)
    (secondDirection (CanonicalActualJointSources.secondLogSlope side))

local notation "recipe" => movingRecipe Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector budget anchor raw hanchor hheight hpositive annulus hAnnulus

theorem fullJointBudget (width : ℝ) (hbudget : budget = Z ^ width) :
    recipe.FullJointBudget Z width := by
  intro ξ u hu
  exact hu.2.trans_eq hbudget

/-- This numerical transport consumes the bound on the actual original
frequency ideal and complete mask. It derives allowed-row membership
from the proved factor norm identity, without an admissible-row premise. -/
theorem allowed_of_source_norm
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (hsource : A.exteriorNorm (actual.originalIdeal q) *
        idealNorm K (recipe.moving.fullMaskSupport recipe.remaining) ≤
      actual.normFactor q * budget) (ξ : WithLp 2 (ℝ × ℝ)) :
    (child ξ).allowedRow (actual.row q).momentIdeal := by
  refine ⟨(HeckeAxiom.exteriorEquiv A (actual.row q).ideal).property, ?_⟩
  apply le_of_mul_le_mul_left _ (actual.row q).factor_pos
  change actual.normFactor q * (A.exteriorNorm (actual.row q).ideal *
    idealNorm K (recipe.moving.fullMaskSupport recipe.remaining)) ≤ actual.normFactor q * budget
  rw [← mul_assoc, ← (actual.row q).norm_factor]
  exact hsource

/-- Coordinate-free form used by the complete source calibration. -/
include hallowed hwindow hδ₁ hδ₂ hδ in
theorem left_profile_joint (mode : WithLp 2 (ℝ × ℝ))
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (I : NonzeroIdeal K) :
    actual.leftWeight q (actual.allocation.plainDivisor 0 * I) *
      jointPhase mode (actual.leftLocation q (actual.allocation.plainDivisor 0 * I)) =
      (child mode).plainTest₁.profile (actual.row q).momentIdeal t
        (idealNorm K I / (actual.scale₁ / idealNorm K (actual.allocation.plainDivisor 0))) := by
  exact
    left_profile Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector budget anchor raw hanchor hheight hpositive annulus hAnnulus
      hallowed hwindow hδ₁ hδ₂ hδ (WithLp.ofLp mode).1 (WithLp.ofLp mode).2 q I

include hallowed hwindow hδ₁ hδ₂ hδ in
theorem right_profile_joint (mode : WithLp 2 (ℝ × ℝ))
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (I : NonzeroIdeal K) :
    actual.rightWeight q (actual.allocation.plainDivisor (Fin.succ 0) * I) *
      jointPhase mode
        (actual.rightLocation q (actual.allocation.plainDivisor (Fin.succ 0) * I)) =
      (child mode).plainTest₂.profile (actual.row q).momentIdeal t
        (idealNorm K I /
          (actual.scale₂ / idealNorm K (actual.allocation.plainDivisor (Fin.succ 0)))) := by
  exact
    right_profile Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector budget anchor raw hanchor hheight hpositive annulus hAnnulus
      hallowed hwindow hδ₁ hδ₂ hδ (WithLp.ofLp mode).1 (WithLp.ofLp mode).2 q I

include hwindow hδ₁ hδ₂ hδ in
theorem prime_profile_joint (mode : WithLp 2 (ℝ × ℝ))
    (q : CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector)
    (i : Fin actual.allocation.keep.card) (p₀ : HeightOneSpectrum (𝓞 K)) :
    actual.slotWeight q (SlotRestriction.index actual.allocation.keep i) p₀ *
      jointPhase mode (actual.slotLocation q (SlotRestriction.index actual.allocation.keep i) p₀) =
      ((child mode).geometry.slots i).profile t
        ((Ideal.absNorm p₀.asIdeal : ℝ) / actual.base ^ ((child mode).geometry.slots i).length) := by
  exact
    prime_profile Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne pattern sector budget anchor raw hanchor hheight hpositive annulus hAnnulus
      hwindow hδ₁ hδ₂ hδ (WithLp.ofLp mode).1 (WithLp.ofLp mode).2 q i p₀


section OriginalSupports

variable (hm : ∀ i, 0 < rows.leftMultiplicity i)
variable (hn : ∀ i, 0 < rows.rightMultiplicity i)
variable (secondRight : Bool)
variable (hcommon : secondCommon = primePowerProduct rows.primes
  (if secondRight then rows.rightMultiplicity else rows.leftMultiplicity))

/-- The actual allocation carrier is computed from the two original
common extractions. Only the original parent support inclusion is used. -/
include hm hn secondRight hcommon in
theorem effective_left_support
    (hS₁ : exteriorPlainSupport (A := A) (data x).plainTest₁ anchor
      (if comparison then Y₁ else Z ^ a.n₁) t ⊆ S₁)
    (hExterior : ∀ J ∈ S₁, IsCoprime J A.cS)
    (mode : WithLp 2 (ℝ × ℝ)) (u : NonzeroIdeal K) :
    effectivePlainSupport (child mode) (child mode).plainTest₁ u
      (actual.scale₁ / idealNorm K (actual.allocation.plainDivisor 0)) t ⊆
        actual.allocation.childPlain₁ := by
  let finalAllocation := actual.allocation
  let finalIndex := idx
  have hB : finalAllocation.plain₁ = L₁₂ := by cases side <;> rfl
  have hscale : actual.scale₁ = H₁ := CanonicalActualJointSources.Pool.joint_leftScale Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
  rw [hscale]
  subst secondCommon
  exact CanonicalBoundedChildSupport.effective_left_support (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    Q.remaining (combinedCommon firstCommon p v) budget anchor t finalIndex raw hanchor hheight hpositive
    H₁ H₂ (fun i => Z ^ ((data x).geometry.slots (finalIndex i)).length)
    b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt hH₁ hH₂
    (fun i => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hAnnulus
    (firstDirection slope) (secondDirection (CanonicalActualJointSources.secondLogSlope side))
    rows.primes_injective hm hn secondRight b₁ b₂ finalAllocation
    (if comparison then Y₁ else Z ^ a.n₁) hS₁ hExterior hB mode u t

include hm hn secondRight hcommon in
theorem effective_right_support
    (hS₂ : exteriorPlainSupport (A := A) (data x).plainTest₂ anchor
      (if comparison then Y₂ else Z ^ a.n₂) t ⊆ S₂)
    (hExterior : ∀ J ∈ S₂, IsCoprime J A.cS)
    (mode : WithLp 2 (ℝ × ℝ)) (u : NonzeroIdeal K) :
    effectivePlainSupport (child mode) (child mode).plainTest₂ u
      (actual.scale₂ / idealNorm K (actual.allocation.plainDivisor (Fin.succ 0))) t ⊆
        actual.allocation.childPlain₂ := by
  let finalAllocation := actual.allocation
  let finalIndex := idx
  have hB : finalAllocation.plain₂ = L₂₂ := by cases side <;> rfl
  have hscale : actual.scale₂ = H₂ := CanonicalActualJointSources.Pool.joint_rightScale Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
  rw [hscale]
  subst secondCommon
  exact CanonicalBoundedChildSupport.effective_right_support (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    Q.remaining (combinedCommon firstCommon p v) budget anchor t finalIndex raw hanchor hheight hpositive
    H₁ H₂ (fun i => Z ^ ((data x).geometry.slots (finalIndex i)).length)
    b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt hH₁ hH₂
    (fun i => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hAnnulus
    (firstDirection slope) (secondDirection (CanonicalActualJointSources.secondLogSlope side))
    rows.primes_injective hm hn secondRight b₁ b₂ finalAllocation
    (if comparison then Y₂ else Z ^ a.n₂) hS₂ hExterior hB mode u t

/-- The last child slots are the actual intersection of all three live
occurrence selections. The full arithmetic mask excludes both commons. -/
include hm hn secondRight hcommon in
theorem effective_prime_support
    (hSlots : ∀ i, exteriorPrimeSupport (A := A) ((data x).geometry.slots i) Z t ⊆ S i)
    (mode : WithLp 2 (ℝ × ℝ)) (u : NonzeroIdeal K)
    (i : Fin actual.allocation.keep.card) :
    effectivePrimeSupport (child mode) i u actual.base t ⊆ actual.allocation.childSlots i := by
  let finalAllocation := actual.allocation
  let finalIndex := idx
  have hB : finalAllocation.slots = Slots₂ := by cases side <;> rfl
  have hindex : finalIndex i = idx₁ (idx₂ (SlotRestriction.index finalAllocation.keep i)) := rfl
  have hbase : actual.base = Z := CanonicalActualJointSources.Pool.joint_base Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne
  rw [hbase]
  subst secondCommon
  exact CanonicalBoundedChildSupport.effective_prime_support (data x) prefix Q.correction (Q.correction_mem x)
    C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    Q.remaining (combinedCommon firstCommon p v) budget anchor t finalIndex raw hanchor hheight hpositive
    H₁ H₂ (fun i => Z ^ ((data x).geometry.slots (finalIndex i)).length)
    b₂.plainDivisor₁ b₂.plainDivisor₂ annulus firstTilt secondTilt hH₁ hH₂
    (fun i => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hAnnulus
    (firstDirection slope) (secondDirection (CanonicalActualJointSources.secondLogSlope side))
    rows.primes_injective hm hn secondRight b₁ b₂ finalAllocation
    Z hSlots hB i i hindex mode u t

end OriginalSupports

end Pool

end HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Main.dictionary

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Main.left_profile

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Main.right_profile

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Main.prime_profile

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Pool.dictionary

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Pool.left_profile

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Pool.right_profile

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Pool.prime_profile

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Main.originalWindow

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Main.fullJointBudget

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Main.allowed_of_source_norm

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Main.effective_left_support

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Main.effective_right_support

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Main.effective_prime_support

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Pool.originalWindow

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Pool.fullJointBudget

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Pool.allowed_of_source_norm

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Pool.effective_left_support

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Pool.effective_right_support

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualChildCalibration.Pool.effective_prime_support
