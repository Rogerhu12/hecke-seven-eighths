import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondFactorAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalCommonColumnMask
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LiveSourceConditions
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondFactorHybridBridge
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

/-!
# The actual second rectangles from the original occurrence tables

The old internal divisor is removed from a coefficient only on a genuine
common branch where it divides that branch's original common ideal. The
live-source theorem supplies this divisibility; it is not a new condition
on all source labels. All remaining coefficient operations are performed
on the original two plain occurrences and the original indexed prime
occurrences, before taking a norm or splitting the centered difference.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalActualSecondRectangles

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open MeasureTheory CanonicalSecondFactorAssembly CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

section OriginalDivisorGate

variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

/-- On the actual second common carrier the original internal divisor
already divides each original full modulus. -/
theorem left_original_divisor_dvd
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (left : Finset α) (S : Ideal (𝓞 K)) (hS : S ∣ DE.1)
    (i : α) (hi : i ∈ b.leftColumns left) : S ∣ (fullI i).val := by
  rw [b.left_reconstruct left i hi, b.common_left]
  exact hS.trans (dvd_mul_right DE.1 (b.leftResidual i).val)

theorem right_original_divisor_dvd
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (right : Finset β) (S : Ideal (𝓞 K)) (hS : S ∣ DE.2)
    (i : β) (hi : i ∈ b.rightColumns right) : S ∣ (fullJ i).val := by
  rw [b.right_reconstruct right i hi, b.common_right]
  exact hS.trans (dvd_mul_right DE.2 (b.rightResidual i).val)

/-- No coefficient support is enlarged when the live common-ideal
divisibility is used to simplify the old gate. -/
theorem left_divisor_gate
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (left : Finset α) (S : Ideal (𝓞 K)) (hS : S ∣ DE.1)
    (c : α → ℂ) (i : α) (hi : i ∈ b.leftColumns left) :
    (if S ∣ (fullI i).val then c i else 0) = c i :=
  if_pos (left_original_divisor_dvd b left S hS i hi)

theorem right_divisor_gate
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (right : Finset β) (S : Ideal (𝓞 K)) (hS : S ∣ DE.2)
    (c : β → ℂ) (i : β) (hi : i ∈ b.rightColumns right) :
    (if S ∣ (fullJ i).val then c i else 0) = c i :=
  if_pos (right_original_divisor_dvd b right S hS i hi)

end OriginalDivisorGate

section FirstOriginalTable

variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (x : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data x))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin (data x).geometry.slotCount → Finset (HeightOneSpectrum (𝓞 K)))
variable (common : A.Exterior)
variable (b : SupportCartesianBranch S₁ S₂ S (primeSupport common.val))
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {τ : Type*} [Fintype τ] [DecidableEq τ]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (primes : τ → ExteriorPrime A) (m n : τ → ℕ) (firstRight : Bool)
variable (δ : NonzeroRingElements A.R) (tilt ξ : ℝ)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)

local notation "L₁" => SupportCartesian.plainResidual S₁ (primeSupport common.val) b.plainExtract₁
local notation "L₂" => SupportCartesian.plainResidual S₂ (primeSupport common.val) b.plainExtract₂
local notation "Slots" => fun j => SupportCartesian.primeLive
  (S (SlotRestriction.index b.keep j)) (primeSupport common.val)
local notation "E₁" => CanonicalSecondRectangularFactors.firstMovingFactors
  P R C primes m n firstRight δ
local notation "M₁" => normLogWeight (tilt - 1) ξ (if firstRight then 1 else -1)
local notation "idx" => SlotRestriction.index b.keep

/-- The first table uses the original quotient profiles and original
retained slot indices. The common-column deletion is inserted by its
proved value one on these actual residual supports. -/
def firstResidualDictionary
    (J : AllocationColumn K b.keep.card → A.Exterior)
    (hJ : ∀ i ∈ b.residualColumns, (J i).val = allocationColumnIdeal i)
    (hactive : ∀ i ∈ b.residualColumns,
      IsCoprime (J i).val (firstActiveIdeal primes m n).val)
    (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle) (comparison : Bool) :
    SecondCoefficientTermDictionary
      (movingSourceCharacters (data x) Q.correction (Q.moving.append E₁)
        (Q.remaining * exteriorMomentIdeal common) idx)
      (side.phase PUnit χ) L₁ L₂ Slots :=
  CanonicalCommonColumnMask.dictionary (Q.moving.append E₁) Q.remaining common
    (data x) Q.correction idx (side.phase PUnit χ) S₁ S₂
    (fun j => S (idx j)) b.plainExtract₁ b.plainExtract₂
    (firstWeightedDictionary (data x) Q.correction Q.moving Q.remaining idx hroot hemb
      side χ L₁ L₂ Slots
      ((if comparison then Y₁ else Z ^ a.n₁) / idealNorm K b.plainDivisor₁)
      ((if comparison then Y₂ else Z ^ a.n₂) / idealNorm K b.plainDivisor₂)
      Z (fun j => ((data x).geometry.slots (idx j)).length)
      (fun I => W.left PUnit.unit t
        (idealNorm K (b.plainDivisor₁ * I) / (if comparison then Y₁ else Z ^ a.n₁)))
      (fun I => W.right PUnit.unit t
        (idealNorm K (b.plainDivisor₂ * I) / (if comparison then Y₂ else Z ^ a.n₂)))
      (fun j p => ((data x).geometry.slots (idx j)).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data x).geometry.slots (idx j)).length))
      M₁ C primes m n firstRight δ J hJ (b.residual b.witness)
      (b.residual_mem b.witness b.witness_mem) hactive)

/-- The whole first reciprocal and Fourier weight, before any second
common extraction. The two signs are the actual first left and right
Fourier locations. -/
def firstResidualTerm (comparison : Bool) (i : AllocationColumn K b.keep.card) : ℂ :=
  (Q.originalTermDictionary x W a Z t Y₁ Y₂ .left 1 S₁ S₂ S comparison).
      coefficient (b.reconstruct i) *
    (E₁.residueHom (σ := σ) * M₁) (allocationColumnIdeal i)

/-- The original complete coefficient is an output of the actual
single-occurrence construction. Its common scalar is retained exactly. -/
theorem firstResidualTerm_eq
    (J : AllocationColumn K b.keep.card → A.Exterior)
    (hJ : ∀ i ∈ b.residualColumns, (J i).val = allocationColumnIdeal i)
    (hactive : ∀ i ∈ b.residualColumns,
      IsCoprime (J i).val (firstActiveIdeal primes m n).val)
    (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle) (comparison : Bool)
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    firstResidualTerm Q x W a Z t Y₁ Y₂ S₁ S₂ S common b C primes m n
        firstRight δ tilt ξ comparison i =
      Q.originalCommonScalar x Z t S₁ S₂ S b *
        (firstResidualDictionary Q x W a Z t Y₁ Y₂ S₁ S₂ S common b C primes m n
          firstRight δ tilt ξ hroot hemb J hJ hactive side χ comparison).coefficient i := by
  rw [firstResidualTerm,
    Q.originalTermDictionary_extract x W a Z t Y₁ Y₂ .left 1 S₁ S₂ S b comparison i hi,
    firstResidualDictionary, CanonicalCommonColumnMask.dictionary_coefficient,
    firstWeightedDictionary_coefficient]
  · exact mul_assoc _ _ _
  · exact hi

/-- The same original common scalar multiplies the complete centered
subtraction. Neither rectangle is bounded separately here. -/
theorem firstResidualTerm_centered
    (J : AllocationColumn K b.keep.card → A.Exterior)
    (hJ : ∀ i ∈ b.residualColumns, (J i).val = allocationColumnIdeal i)
    (hactive : ∀ i ∈ b.residualColumns,
      IsCoprime (J i).val (firstActiveIdeal primes m n).val)
    (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    firstResidualTerm Q x W a Z t Y₁ Y₂ S₁ S₂ S common b C primes m n
        firstRight δ tilt ξ false i -
      firstResidualTerm Q x W a Z t Y₁ Y₂ S₁ S₂ S common b C primes m n
        firstRight δ tilt ξ true i =
      Q.originalCommonScalar x Z t S₁ S₂ S b *
        ((firstResidualDictionary Q x W a Z t Y₁ Y₂ S₁ S₂ S common b C primes m n
          firstRight δ tilt ξ hroot hemb J hJ hactive side χ false).coefficient i -
         (firstResidualDictionary Q x W a Z t Y₁ Y₂ S₁ S₂ S common b C primes m n
          firstRight δ tilt ξ hroot hemb J hJ hactive side χ true).coefficient i) := by
  rw [firstResidualTerm_eq Q x W a Z t Y₁ Y₂ S₁ S₂ S common b C primes m n
      firstRight δ tilt ξ hroot hemb J hJ hactive side χ false i hi,
    firstResidualTerm_eq Q x W a Z t Y₁ Y₂ S₁ S₂ S common b C primes m n
      firstRight δ tilt ξ hroot hemb J hJ hactive side χ true i hi,
    mul_sub]

end FirstOriginalTable

section ActualSecondExtraction

variable {k : ℕ}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {support : Finset (Ideal (𝓞 K))}

/-- Reconstruction keeps every frozen occurrence, including repeated
prime occurrences. This identity is independent of any arithmetic
coefficient and any profile. -/
theorem reconstruct_ideal
    (b : SupportCartesianBranch S₁ S₂ S support)
    (i : AllocationColumn K b.keep.card) :
    allocationColumnIdeal (b.reconstruct i) =
      frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 *
        allocationColumnIdeal i := by
  simp only [allocationColumnIdeal, SupportCartesianBranch.reconstruct,
    SlotRestriction.product_extend, frozenSourceIdeal,
    SupportCartesianBranch.plainDivisor₁, SupportCartesianBranch.plainDivisor₂,
    Finset.sdiff_eq_filter, Finset.mem_univ, true_and]
  ring

private theorem bare_left_scalar
    (T : FixedChildCharacters K k) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (c : ℂ) (i : AllocationColumn K k) :
    rawBareSourceCoefficient T N₁ N₂ Z length (fun I => c * w₁ I) w₂ w i =
      c * rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i := by
  simp only [rawBareSourceCoefficient, FixedChildCharacters.bareCoefficient,
    childCartesianCoefficient]
  ring

private theorem punit_dictionary_bare
    {T : FixedChildCharacters K k} (side : SecondColumnSide)
    (χ : (PUnit × PUnit) →* Circle)
    (F : SecondCoefficientTermDictionary T (side.phase PUnit χ) S₁ S₂ S)
    (i : AllocationColumn K k) (hi : i ∈ childCartesianColumns S₁ S₂ S) :
    F.coefficient i = rawBareSourceCoefficient T F.scale₁ F.scale₂ F.base F.length
      F.leftWeight F.rightWeight F.slotWeight i := by
  have h := F.coefficient_phase i hi
  simpa only [Subsingleton.elim (F.ray i) PUnit.unit,
    CanonicalSecondRectangularFactors.punit_phase, mul_one] using h

variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable [IsPrincipalIdealRing A.R]

local notation "ε" => sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅
local notation "E₂" => CanonicalSecondRectangularFactors.secondMaskMovingFactors P R ε

/-- The inverse unit character of the actual empty second mask is
retained, with its original generator. -/
theorem second_weight_empty (tilt : ℝ) :
    CanonicalSecondRectangularFactors.secondWeight (σ := σ) tilt ε.val =
      E₂.residueHom (σ := σ) * CanonicalSecondRectangularFactors.normPower tilt := by
  ext I
  simp only [CanonicalSecondRectangularFactors.secondWeight,
    CanonicalSecondRectangularFactors.secondMaskMovingFactors,
    CanonicalSecondRectangularFactors.idealPhase, OriginalMovingFactors.residueHom,
    OriginalMovingFactors.residueValue, OriginalMovingFactors.singleton,
    MonoidHom.mul_apply, MonoidHom.coe_mk, OneHom.coe_mk,
    Fin.prod_univ_one, zpow_neg_one, mul_comm]

variable (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
variable (prefix : OriginalMovingFactors A P R) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable (F : SecondCoefficientTermDictionary
  (movingSourceCharacters parent correction prefix remaining index)
  (side.phase PUnit χ) S₁ S₂ S)
variable (b : SupportCartesianBranch S₁ S₂ S support)
variable (common : A.Exterior)
variable (hcommon : frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 =
  common.val)
variable (scalar : ℂ) (tilt : ℝ)
variable (J : AllocationColumn K b.keep.card → A.Exterior)
variable (hJ : ∀ i ∈ b.residualColumns, (J i).val = allocationColumnIdeal i)

local notation "L₁" => SupportCartesian.plainResidual S₁ support b.plainExtract₁
local notation "L₂" => SupportCartesian.plainResidual S₂ support b.plainExtract₂
local notation "Slots" => fun j => SupportCartesian.primeLive
  (S (SlotRestriction.index b.keep j)) support
local notation "idx" => SlotRestriction.index b.keep
local notation "weight₂" => CanonicalSecondRectangularFactors.secondWeight (σ := σ) tilt ε.val
local notation "commonScalar" => b.bareCommonScalar
  (movingSourceCharacters parent correction prefix remaining index) F.base F.length F.slotWeight

/-- The residual core has no common scalar in its profiles. It is the
table used after the exact pre-Cauchy common-scalar reweighting. -/
def secondResidualCoreDictionary :
    SecondCoefficientTermDictionary
      (movingSourceCharacters parent correction (prefix.append E₂) remaining
        (fun j => index (idx j)))
      (side.phase PUnit χ) L₁ L₂ Slots :=
  emptyMaskWeightedDictionary parent correction prefix remaining (fun j => index (idx j))
    hroot hemb side χ L₁ L₂ Slots
    (F.scale₁ / idealNorm K b.plainDivisor₁)
    (F.scale₂ / idealNorm K b.plainDivisor₂) F.base (fun j => F.length (idx j))
    (fun I => F.leftWeight (b.plainDivisor₁ * I))
    (fun I => F.rightWeight (b.plainDivisor₂ * I))
    (fun j => F.slotWeight (idx j))
    (CanonicalSecondRectangularFactors.normPower tilt)
    J hJ (b.residual b.witness) (b.residual_mem b.witness b.witness_mem)

theorem secondResidualCoreDictionary_coefficient
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    (secondResidualCoreDictionary parent correction prefix remaining index hroot hemb
      side χ F b tilt J hJ).coefficient i =
      b.bareResidualCoefficient (movingSourceCharacters parent correction prefix remaining index)
        F.scale₁ F.scale₂ F.base F.length F.leftWeight F.rightWeight F.slotWeight i *
          weight₂ (J i).val := by
  rw [secondResidualCoreDictionary, emptyMaskWeightedDictionary_coefficient]
  · rw [hJ i hi, second_weight_empty (P := P) (R := R)]
    rfl
  · exact hi

/-- The second table is computed from the actual first single-atom
table. Its only new character is the actual empty-mask unit character;
the true common scalar includes the frozen first profiles and phases. -/
def secondResidualDictionary :
    SecondCoefficientTermDictionary
      (movingSourceCharacters parent correction (prefix.append E₂) remaining
        (fun j => index (idx j)))
      (side.phase PUnit χ) L₁ L₂ Slots :=
  emptyMaskWeightedDictionary parent correction prefix remaining (fun j => index (idx j))
    hroot hemb side χ L₁ L₂ Slots
    (F.scale₁ / idealNorm K b.plainDivisor₁)
    (F.scale₂ / idealNorm K b.plainDivisor₂) F.base (fun j => F.length (idx j))
    (fun I => (scalar * commonScalar * weight₂ common.val) * F.leftWeight (b.plainDivisor₁ * I))
    (fun I => F.rightWeight (b.plainDivisor₂ * I))
    (fun j => F.slotWeight (idx j))
    (CanonicalSecondRectangularFactors.normPower tilt)
    J hJ (b.residual b.witness) (b.residual_mem b.witness b.witness_mem)

/-- This is the same original second full-modulus coefficient on the
real reconstructed columns. No rectangle factor identity is an input. -/
theorem secondResidualDictionary_coefficient
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    (secondResidualDictionary parent correction prefix remaining index hroot hemb
      side χ F b common scalar tilt J hJ).coefficient i =
      scalar * F.coefficient (b.reconstruct i) * weight₂ (common.val * (J i).val) := by
  rw [secondResidualDictionary, emptyMaskWeightedDictionary_coefficient]
  · rw [bare_left_scalar]
    have hb := punit_dictionary_bare side χ F (b.reconstruct i)
      (b.original_subset (b.reconstruct_mem i hi))
    rw [hb, b.raw_bare_extract]
    · rw [map_mul, hJ i hi]
      simp only [second_weight_empty (P := P) (R := R)]
      change (scalar * commonScalar *
        (E₂.residueHom (σ := σ) * CanonicalSecondRectangularFactors.normPower tilt) common.val) *
          b.bareResidualCoefficient (movingSourceCharacters parent correction prefix remaining index)
            F.scale₁ F.scale₂ F.base F.length F.leftWeight F.rightWeight F.slotWeight i *
          (E₂.residueHom (σ := σ) * CanonicalSecondRectangularFactors.normPower tilt)
            (allocationColumnIdeal i) = _
      ring
    · exact hi
  · exact hi

/-- The scalar is outside the residual core, so it can be moved into
the actual row weight exactly once, before either row Cauchy step. -/
theorem second_original_to_core
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    scalar * F.coefficient (b.reconstruct i) * weight₂ (common.val * (J i).val) =
      (scalar * commonScalar * weight₂ common.val) *
        (secondResidualCoreDictionary parent correction prefix remaining index hroot hemb
          side χ F b tilt J hJ).coefficient i := by
  rw [secondResidualCoreDictionary_coefficient parent correction prefix remaining index
    hroot hemb side χ F b tilt J hJ i hi,
    punit_dictionary_bare side χ F (b.reconstruct i)
      (b.original_subset (b.reconstruct_mem i hi)),
    b.raw_bare_extract _ _ _ _ _ _ _ _ i hi, map_mul]
  ring

end ActualSecondExtraction

section OriginalNormalizers

variable {k : ℕ}
variable {T : FixedChildCharacters K k}
variable {side : SecondColumnSide} {χ : (PUnit × PUnit) →* Circle}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable (F : SecondCoefficientTermDictionary T (side.phase PUnit χ) S₁ S₂ S)
variable (G₁ G₂ : ℝ) (G : Fin k → ℝ)

/-- The original additional Gauss scales are recorded in the actual
frame. Their reciprocal square roots are compensated in the individual
profile weights, not in a new whole-coefficient premise. -/
def originalNormalizers :
    SecondCoefficientTermDictionary T (side.phase PUnit χ) S₁ S₂ S where
  leftAtom I := (Real.sqrt G₁ : ℂ) * F.leftAtom I
  rightAtom I := (Real.sqrt G₂ : ℂ) * F.rightAtom I
  slotAtom j p := (Real.sqrt (G j) : ℂ) * F.slotAtom j p
  leftRay := F.leftRay
  rightRay := F.rightRay
  slotRay := F.slotRay
  scale₁ := F.scale₁
  scale₂ := F.scale₂
  base := F.base
  length := F.length
  leftWeight I := (Real.sqrt G₁ : ℂ) * F.leftWeight I
  rightWeight I := (Real.sqrt G₂ : ℂ) * F.rightWeight I
  slotWeight j p := (Real.sqrt (G j) : ℂ) * F.slotWeight j p
  plain₁ I hI := by
    have h := F.plain₁ I hI
    calc
      _ = (Real.sqrt G₁ : ℂ) *
          (F.leftAtom I * ((side.phase PUnit χ) (F.leftRay I) : ℂ)) := mul_assoc _ _ _
      _ = _ := by rw [h]; ring
  plain₂ I hI := by
    have h := F.plain₂ I hI
    calc
      _ = (Real.sqrt G₂ : ℂ) *
          (F.rightAtom I * ((side.phase PUnit χ) (F.rightRay I) : ℂ)) := mul_assoc _ _ _
      _ = _ := by rw [h]; ring
  prime j p hp := by
    have h := F.prime j p hp
    calc
      _ = (Real.sqrt (G j) : ℂ) *
          (F.slotAtom j p * ((side.phase PUnit χ) (F.slotRay j p) : ℂ)) := mul_assoc _ _ _
      _ = _ := by rw [h]; ring

/-- The compensation is exact for each individual original occurrence.
No positive scale or repeated prime is discarded. -/
theorem originalNormalizers_coefficient
    (hG₁ : 0 < G₁) (hG₂ : 0 < G₂) (hG : ∀ i, 0 < G i)
    (i : AllocationColumn K k) :
    (originalNormalizers F G₁ G₂ G).normalizedCoefficient
        (Real.sqrt G₁ : ℂ)⁻¹ (Real.sqrt G₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (G j) : ℂ)⁻¹) i = F.coefficient i := by
  have h₁ : (Real.sqrt G₁ : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hG₁).ne'
  have h₂ : (Real.sqrt G₂ : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hG₂).ne'
  have hs (j : Fin k) : (Real.sqrt (G j) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (hG j)).ne'
  simp only [SecondCoefficientTermDictionary.normalizedCoefficient,
    SecondCoefficientTermDictionary.coefficient, originalNormalizers,
    childCartesianCoefficient, inv_mul_cancel_left₀ h₁,
    inv_mul_cancel_left₀ h₂, inv_mul_cancel_left₀ (hs _)]

@[simp] theorem originalNormalizers_ray (i : AllocationColumn K k) :
    (originalNormalizers F G₁ G₂ G).ray i = F.ray i := rfl

/-- Redistributing the two original plain scales does not change the
actual complex normalizer when their product is unchanged. This lets
each comparison profile use its own original length while the frame
keeps the original nominal Gauss scale. -/
theorem normalizedCoefficient_plain_product
    (H₁ H₂ : ℝ) (hG₁ : 0 ≤ G₁) (hH₁ : 0 ≤ H₁)
    (hproduct : G₁ * G₂ = H₁ * H₂) (i : AllocationColumn K k) :
    F.normalizedCoefficient (Real.sqrt G₁ : ℂ)⁻¹ (Real.sqrt G₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (G j) : ℂ)⁻¹) i =
      F.normalizedCoefficient (Real.sqrt H₁ : ℂ)⁻¹ (Real.sqrt H₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (G j) : ℂ)⁻¹) i := by
  rw [F.normalizedCoefficient_eq, F.normalizedCoefficient_eq]
  exact congrArg (fun z : ℂ => z * F.coefficient i)
    (extraGaussNormalizer_plain_product_eq G₁ G₂ H₁ H₂ G hG₁ hH₁ hproduct)

end OriginalNormalizers

section OriginalComparisonScales

variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {a : RealParameters} {Z Y₁ Y₂ floor padding : ℝ}

/-- The original centered comparison has the same plain-scale product;
the identity follows from the stated original comparison exponents. -/
theorem centered_plain_product
    (domain : PairedEngineDomain true d a Z Y₁ Y₂ floor padding) :
    Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂ := by
  rw [domain.comparison_left rfl, domain.comparison_right rfl,
    ← Real.rpow_add (zero_lt_one.trans domain.scale),
    ← Real.rpow_add (zero_lt_one.trans domain.scale)]
  congr 1
  ring

theorem centered_plain_positive
    (domain : PairedEngineDomain true d a Z Y₁ Y₂ floor padding) :
    0 < Y₁ ∧ 0 < Y₂ := by
  rw [domain.comparison_left rfl, domain.comparison_right rfl]
  exact ⟨Real.rpow_pos_of_pos (zero_lt_one.trans domain.scale) _,
    Real.rpow_pos_of_pos (zero_lt_one.trans domain.scale) _⟩

end OriginalComparisonScales

section ActualRectangularFactors

variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable [IsPrincipalIdealRing A.R]
variable {H τ : Type*} [Fintype τ] [DecidableEq τ]
variable (rows : ActualSecondCorrelationRows A σ H τ)
variable {k : ℕ}
variable (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
variable (prefix : OriginalMovingFactors A P R) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable (F : SecondCoefficientTermDictionary
  (movingSourceCharacters parent correction prefix remaining index)
  (side.phase PUnit χ) S₁ S₂ S)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ S support)
variable (common : A.Exterior) (scalar : ℂ) (tilt : ℝ)
variable (J : AllocationColumn K b.keep.card → A.Exterior)
variable (hJ : ∀ i ∈ b.residualColumns, (J i).val = allocationColumnIdeal i)
variable (hbase : 1 < F.base) (hlength : ∀ j, 0 < F.length j)
variable (G₁ G₂ : ℝ) (G : Fin b.keep.card → ℝ)
variable (hG₁ : 0 < G₁) (hG₂ : 0 < G₂) (hG : ∀ j, 0 < G j)
variable (rowOffset : H → ℝ)

local notation "L₁" => SupportCartesian.plainResidual S₁ support b.plainExtract₁
local notation "L₂" => SupportCartesian.plainResidual S₂ support b.plainExtract₂
local notation "Slots" => fun j => SupportCartesian.primeLive
  (S (SlotRestriction.index b.keep j)) support
local notation "ε" => sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅
local notation "weight₂" => CanonicalSecondRectangularFactors.secondWeight (σ := σ) tilt ε.val
local notation "table" => secondResidualDictionary parent correction prefix remaining index
  hroot hemb side χ F b common scalar tilt J hJ

/-- The computed first table constructs the actual second rectangle,
with its full second modulus in both the coefficient and logarithmic
location. The row offset is the original log radius on the left and zero
on the right. All same-source coefficient identities are proved here. -/
def secondRectangularFactors :
    SecondRectangularFactors rows PUnit side L₁ L₂ Slots J (fun _ => PUnit.unit)
      (fun i => scalar * F.coefficient (b.reconstruct i) *
        weight₂ (common.val * (J i).val))
      (fun h i => rowOffset h - Real.log (A.exteriorNorm common * A.exteriorNorm (J i))) χ where
  characters := _
  dictionary := originalNormalizers table G₁ G₂ G
  base_gt_one := hbase
  length_pos j := hlength (SlotRestriction.index b.keep j)
  plain₁_nonzero I hI := by
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hI
    exact supportResidual_ne_zero I support
  plain₂_nonzero I hI := by
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hI
    exact supportResidual_ne_zero I support
  ideal_product := hJ
  gaussScale₁ := G₁
  gaussScale₂ := G₂
  gaussSlotScale := G
  gaussScale₁_pos := hG₁
  gaussScale₂_pos := hG₂
  gaussSlotScale_pos := hG
  coefficient_factor i hi := by
    rw [originalNormalizers_coefficient table G₁ G₂ G hG₁ hG₂ hG i]
    exact (secondResidualDictionary_coefficient parent correction prefix remaining index
      hroot hemb side χ F b common scalar tilt J hJ i hi).symm
  ray_factor _ _ := Subsingleton.elim _ _
  leftLocation h I := rowOffset h - Real.log (A.exteriorNorm common) - Real.log (idealNorm K I)
  rightLocation _ I := -Real.log (idealNorm K I)
  slotLocation _ _ p := -Real.log (Ideal.absNorm p.asIdeal : ℝ)
  point_factor h _ i hi := by
    have hp := Finset.mem_product.mp (Finset.mem_product.mp hi).1
    have h₁ : i.1.1 ≠ 0 := by
      obtain ⟨I, _, hI⟩ := Finset.mem_image.mp hp.1
      rw [← hI]
      exact supportResidual_ne_zero I support
    have h₂ : i.1.2 ≠ 0 := by
      obtain ⟨I, _, hI⟩ := Finset.mem_image.mp hp.2
      rw [← hI]
      exact supportResidual_ne_zero I support
    have hx := rawSourceLocation_neg_log_exterior i h₁ h₂ (J i) (hJ i hi)
    rw [Real.log_mul (A.exteriorNorm_pos common).ne' (A.exteriorNorm_pos (J i)).ne']
    simp only [rawSourceLocation, childCartesianLocation] at hx ⊢
    linarith

/-- The same computed rectangle after its proved common scalar has
been moved into the original row weight. This is the input for
`withCommonAtoms`; no common scalar is paid again by these profiles. -/
def secondResidualCoreRectangularFactors :
    SecondRectangularFactors rows PUnit side L₁ L₂ Slots J (fun _ => PUnit.unit)
      (fun i => b.bareResidualCoefficient
        (movingSourceCharacters parent correction prefix remaining index)
        F.scale₁ F.scale₂ F.base F.length F.leftWeight F.rightWeight F.slotWeight i *
          weight₂ (J i).val)
      (fun h i => rowOffset h - Real.log (A.exteriorNorm common * A.exteriorNorm (J i))) χ := by
  let core := secondResidualCoreDictionary parent correction prefix remaining index
    hroot hemb side χ F b tilt J hJ
  let f := secondRectangularFactors rows parent correction prefix remaining index hroot hemb
    side χ F b common 1 tilt J hJ hbase hlength G₁ G₂ G hG₁ hG₂ hG rowOffset
  refine { f with dictionary := originalNormalizers core G₁ G₂ G,
    coefficient_factor := ?_, ray_factor := ?_ }
  · intro i hi
    rw [originalNormalizers_coefficient core G₁ G₂ G hG₁ hG₂ hG i]
    exact (secondResidualCoreDictionary_coefficient parent correction prefix remaining index
      hroot hemb side χ F b tilt J hJ i hi).symm
  · intro i _
    exact Subsingleton.elim _ _

end ActualRectangularFactors

section SameOriginalRectangles

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
variable (δ : NonzeroRingElements A.R) (firstTilt ξ : ℝ)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (J₁ : AllocationColumn K b₁.keep.card → A.Exterior)
variable (hJ₁ : ∀ i ∈ b₁.residualColumns, (J₁ i).val = allocationColumnIdeal i)
variable (hactive : ∀ i ∈ b₁.residualColumns,
  IsCoprime (J₁ i).val (firstActiveIdeal primes m n).val)
variable {H ν : Type*} [Fintype ν] [DecidableEq ν]
variable (rows : ActualSecondCorrelationRows A σ H ν)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable (secondCommon : A.Exterior)

local notation "L₁" => SupportCartesian.plainResidual S₁
  (primeSupport firstCommon.val) b₁.plainExtract₁
local notation "L₂" => SupportCartesian.plainResidual S₂
  (primeSupport firstCommon.val) b₁.plainExtract₂
local notation "Slots₁" => fun j => SupportCartesian.primeLive
  (S (SlotRestriction.index b₁.keep j)) (primeSupport firstCommon.val)

variable (b₂ : SupportCartesianBranch L₁ L₂ Slots₁ (primeSupport secondCommon.val))
variable (J₂ : AllocationColumn K b₂.keep.card → A.Exterior)
variable (hJ₂ : ∀ i ∈ b₂.residualColumns, (J₂ i).val = allocationColumnIdeal i)
variable (secondTilt : ℝ) (rowOffset : H → ℝ)

local notation "firstTable" => firstResidualDictionary Q x W a Z t Y₁ Y₂
  S₁ S₂ S firstCommon b₁ C primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ
local notation "firstTerm" => firstResidualTerm Q x W a Z t Y₁ Y₂
  S₁ S₂ S firstCommon b₁ C primes m n firstRight δ firstTilt ξ
local notation "idx₁" => SlotRestriction.index b₁.keep
local notation "idx₂" => SlotRestriction.index b₂.keep
local notation "E₁" => CanonicalSecondRectangularFactors.firstMovingFactors P R C primes m n firstRight δ
local notation "ε" => sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅
local notation "weight₂" => CanonicalSecondRectangularFactors.secondWeight (σ := σ) secondTilt ε.val
local notation "G₁" => (Z ^ a.n₁ / idealNorm K b₁.plainDivisor₁) / idealNorm K b₂.plainDivisor₁
local notation "G₂" => (Z ^ a.n₂ / idealNorm K b₁.plainDivisor₂) / idealNorm K b₂.plainDivisor₂
local notation "Gslots" => fun j => Z ^ ((data x).geometry.slots (idx₁ (idx₂ j))).length
local notation "H₁" => fun comparison : Bool =>
  ((if comparison then Y₁ else Z ^ a.n₁) / idealNorm K b₁.plainDivisor₁) /
    idealNorm K b₂.plainDivisor₁
local notation "H₂" => fun comparison : Bool =>
  ((if comparison then Y₂ else Z ^ a.n₂) / idealNorm K b₁.plainDivisor₂) /
    idealNorm K b₂.plainDivisor₂

private theorem actual_plain_product (comparison : Bool)
    (hplainProduct : comparison = true → Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂) :
    G₁ * G₂ = H₁ comparison * H₂ comparison := by
  cases comparison with
  | false => rfl
  | true =>
    change G₁ * G₂ =
      (Y₁ / idealNorm K b₁.plainDivisor₁ / idealNorm K b₂.plainDivisor₁) *
        (Y₂ / idealNorm K b₁.plainDivisor₂ / idealNorm K b₂.plainDivisor₂)
    simp only [div_eq_mul_inv]
    calc
      _ = (Z ^ a.n₁ * Z ^ a.n₂) *
          ((idealNorm K b₁.plainDivisor₁)⁻¹ * (idealNorm K b₂.plainDivisor₁)⁻¹ *
            (idealNorm K b₁.plainDivisor₂)⁻¹ * (idealNorm K b₂.plainDivisor₂)⁻¹) := by ring
      _ = _ := by rw [← hplainProduct rfl]; ring

include hZ in
private theorem actual_left_positive (comparison : Bool)
    (hY₁ : comparison = true → 0 < Y₁) : 0 < H₁ comparison := by
  apply div_pos _ (idealNorm_pos K _)
  apply div_pos _ (idealNorm_pos K _)
  cases comparison
  · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  · exact hY₁ rfl

include hZ in
private theorem actual_right_positive (comparison : Bool)
    (hY₂ : comparison = true → 0 < Y₂) : 0 < H₂ comparison := by
  apply div_pos _ (idealNorm_pos K _)
  apply div_pos _ (idealNorm_pos K _)
  cases comparison
  · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  · exact hY₂ rfl

/-- One of the two literal original comparison rectangles. Both
transforms, both common extractions, the original correction, all old
moving factors and the full first common deletion are constructed from
the same original inputs. Each profile is compensated at its own
original comparison length. The product identity above preserves the
frame's original nominal Gauss scales. -/
def originalSecondRectangularFactors (comparison : Bool)
    (hcomparison : comparison = true →
      0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂) :
    SecondRectangularFactors rows PUnit side
      (SupportCartesian.plainResidual L₁ (primeSupport secondCommon.val) b₂.plainExtract₁)
      (SupportCartesian.plainResidual L₂ (primeSupport secondCommon.val) b₂.plainExtract₂)
      (fun j => SupportCartesian.primeLive (Slots₁ (idx₂ j)) (primeSupport secondCommon.val))
      J₂ (fun _ => PUnit.unit)
      (fun i => firstTerm comparison (b₂.reconstruct i) *
        weight₂ (secondCommon.val * (J₂ i).val))
      (fun h i => rowOffset h - Real.log (A.exteriorNorm secondCommon * A.exteriorNorm (J₂ i))) χ := by
  have hG₁ : 0 < G₁ :=
    div_pos (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
      (idealNorm_pos K _)) (idealNorm_pos K _)
  have hG₂ : 0 < G₂ :=
    div_pos (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
      (idealNorm_pos K _)) (idealNorm_pos K _)
  have hGslots : ∀ j, 0 < Gslots j :=
    fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  let f := secondRectangularFactors rows (data x) Q.correction (Q.moving.append E₁)
    (Q.remaining * exteriorMomentIdeal firstCommon) idx₁ hroot hemb side χ
    (firstTable comparison) b₂ secondCommon
    (Q.originalCommonScalar x Z t S₁ S₂ S b₁) secondTilt J₂ hJ₂ hZ
    (fun j => ((data x).geometry.slots (idx₁ j)).length_pos)
    (H₁ comparison) (H₂ comparison) Gslots
    (actual_left_positive x a Z Y₁ hZ S₁ S₂ S firstCommon b₁ secondCommon b₂ comparison
      (fun hc => (hcomparison hc).1))
    (actual_right_positive x a Z Y₂ hZ S₁ S₂ S firstCommon b₁ secondCommon b₂ comparison
      (fun hc => (hcomparison hc).2.1))
    hGslots rowOffset
  refine { f with gaussScale₁ := G₁, gaussScale₂ := G₂,
    gaussScale₁_pos := hG₁, gaussScale₂_pos := hG₂, coefficient_factor := ?_ }
  intro i hi
  rw [firstResidualTerm_eq Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C primes m n
    firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ comparison
    (b₂.reconstruct i) (b₂.original_subset (b₂.reconstruct_mem i hi))]
  rw [normalizedCoefficient_plain_product f.dictionary G₁ G₂ Gslots
    (H₁ comparison) (H₂ comparison) hG₁.le
    (actual_left_positive x a Z Y₁ hZ S₁ S₂ S firstCommon b₁ secondCommon b₂ comparison
      (fun hc => (hcomparison hc).1)).le
    (actual_plain_product x a Z Y₁ Y₂ S₁ S₂ S firstCommon b₁
      secondCommon b₂ comparison (fun hc => (hcomparison hc).2.2)) i]
  exact f.coefficient_factor i hi

/-- The original whole centered coefficient is kept as one coefficient
through both actual transforms. There is a single first Fourier phase
and a single second empty-mask phase. -/
def originalSecondWholeCoefficient (i : AllocationColumn K b₂.keep.card) : ℂ :=
  (((Q.arithmeticAtoms x).constantAtoms W a Z t).values Y₁ Y₂).coefficient true
      ((sourceMomentIdeal (b₁.reconstruct (b₂.reconstruct i)).1.1,
        sourceMomentIdeal (b₁.reconstruct (b₂.reconstruct i)).1.2),
        (b₁.reconstruct (b₂.reconstruct i)).2) *
    (E₁.residueHom (σ := σ) *
      normLogWeight (firstTilt - 1) ξ (if firstRight then 1 else -1))
        (allocationColumnIdeal (b₂.reconstruct i)) *
    weight₂ (secondCommon.val * (J₂ i).val)

/-- The ordinary two-rectangle decomposition is proved from the same
original centered atom, after the branch has already been fixed. -/
theorem originalSecondWholeCoefficient_difference (i : AllocationColumn K b₂.keep.card) :
    originalSecondWholeCoefficient Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C
      primes m n firstRight δ firstTilt ξ secondCommon b₂ J₂ secondTilt i =
      firstTerm false (b₂.reconstruct i) * weight₂ (secondCommon.val * (J₂ i).val) -
        firstTerm true (b₂.reconstruct i) * weight₂ (secondCommon.val * (J₂ i).val) := by
  unfold originalSecondWholeCoefficient firstResidualTerm
  rw [Q.originalTermDictionary_coefficient x W a Z t Y₁ Y₂ .left 1 S₁ S₂ S false,
    Q.originalTermDictionary_coefficient x W a Z t Y₁ Y₂ .left 1 S₁ S₂ S true]
  change (_ - _) * _ * _ = _ * _ * _ - _ * _ * _
  ring

/-- The actual original Gauss modulus is reconstructed from the same
second common branch, rather than replaced by a nominal product. -/
theorem originalSourceModulus
    (hcommon : frozenSourceIdeal b₂.plainDivisor₁ b₂.plainDivisor₂ b₂.keep b₂.witness.2 =
      secondCommon.val)
    (i : AllocationColumn K b₂.keep.card) (hi : i ∈ b₂.residualColumns) :
    (J₁ (b₂.reconstruct i)).val = secondCommon.val * (J₂ i).val := by
  rw [hJ₁ (b₂.reconstruct i) (b₂.original_subset (b₂.reconstruct_mem i hi)),
    reconstruct_ideal b₂ i, hcommon, hJ₂ i hi]

theorem originalSourceModulus_norm
    (hcommon : frozenSourceIdeal b₂.plainDivisor₁ b₂.plainDivisor₂ b₂.keep b₂.witness.2 =
      secondCommon.val)
    (i : AllocationColumn K b₂.keep.card) (hi : i ∈ b₂.residualColumns) :
    A.exteriorNorm (J₁ (b₂.reconstruct i)) =
      A.exteriorNorm secondCommon * A.exteriorNorm (J₂ i) := by
  change (Ideal.absNorm (J₁ (b₂.reconstruct i)).val : ℝ) =
    (Ideal.absNorm secondCommon.val : ℝ) * (Ideal.absNorm (J₂ i).val : ℝ)
  rw [originalSourceModulus x S₁ S₂ S firstCommon b₁ J₁ hJ₁ secondCommon b₂ J₂ hJ₂
    hcommon i hi, map_mul, Nat.cast_mul]

/-- The rectangle now has the literal source modulus in both original
fields used by the canonical second chart. The complete modulus identity
is a conclusion of the two genuine occurrence dictionaries. -/
def originalSecondSourceRectangularFactors
    (hcommon : frozenSourceIdeal b₂.plainDivisor₁ b₂.plainDivisor₂ b₂.keep b₂.witness.2 =
      secondCommon.val)
    (comparison : Bool)
    (hcomparison : comparison = true →
      0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂) :
    SecondRectangularFactors rows PUnit side
      (SupportCartesian.plainResidual L₁ (primeSupport secondCommon.val) b₂.plainExtract₁)
      (SupportCartesian.plainResidual L₂ (primeSupport secondCommon.val) b₂.plainExtract₂)
      (fun j => SupportCartesian.primeLive (Slots₁ (idx₂ j)) (primeSupport secondCommon.val))
      J₂ (fun _ => PUnit.unit)
      (fun i => firstTerm comparison (b₂.reconstruct i) * weight₂ (J₁ (b₂.reconstruct i)).val)
      (fun h i => rowOffset h - Real.log (A.exteriorNorm (J₁ (b₂.reconstruct i)))) χ := by
  let f := originalSecondRectangularFactors Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
    C primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
  refine { f with coefficient_factor := ?_, point_factor := ?_ }
  · intro i hi
    rw [originalSourceModulus x S₁ S₂ S firstCommon b₁ J₁ hJ₁ secondCommon b₂ J₂ hJ₂
      hcommon i hi]
    exact f.coefficient_factor i hi
  · intro h hh i hi
    rw [originalSourceModulus_norm x S₁ S₂ S firstCommon b₁ J₁ hJ₁ secondCommon b₂ J₂ hJ₂
      hcommon i hi]
    exact f.point_factor h hh i hi

/-- The exact scalar belonging to the original columns before they
enter reweighted rows. Both comparison terms have the same scalar. -/
def originalSecondCommonScalar : ℂ :=
  Q.originalCommonScalar x Z t S₁ S₂ S b₁ *
    b₂.bareCommonScalar
      (movingSourceCharacters (data x) Q.correction (Q.moving.append E₁)
        (Q.remaining * exteriorMomentIdeal firstCommon) idx₁)
      Z (fun j => ((data x).geometry.slots (idx₁ j)).length)
      (firstTable false).slotWeight * weight₂ secondCommon.val

/-- In particular the second full common norm power has not been
declared a constant. Its exact factor remains visible to the original
row-profile/common-atom budget. -/
theorem originalSecondCommonScalar_eq (comparison : Bool) :
    originalSecondCommonScalar Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C
      primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ
      secondCommon b₂ secondTilt =
      Q.originalCommonScalar x Z t S₁ S₂ S b₁ *
        b₂.bareCommonScalar
          (movingSourceCharacters (data x) Q.correction (Q.moving.append E₁)
            (Q.remaining * exteriorMomentIdeal firstCommon) idx₁)
          (firstTable comparison).base (firstTable comparison).length
          (firstTable comparison).slotWeight * weight₂ secondCommon.val := by
  cases comparison <;> rfl

/-- The residual factor source uses the actual raw first weights and
all actual retained occurrences; it contains no extracted common scalar. -/
def originalSecondCoreCoefficient (comparison : Bool)
    (i : AllocationColumn K b₂.keep.card) : ℂ :=
  b₂.bareResidualCoefficient
      (movingSourceCharacters (data x) Q.correction (Q.moving.append E₁)
        (Q.remaining * exteriorMomentIdeal firstCommon) idx₁)
      (firstTable comparison).scale₁ (firstTable comparison).scale₂
      (firstTable comparison).base (firstTable comparison).length
      (firstTable comparison).leftWeight (firstTable comparison).rightWeight
      (firstTable comparison).slotWeight i * weight₂ (J₂ i).val

theorem originalSecondSource_to_core
    (hcommon : frozenSourceIdeal b₂.plainDivisor₁ b₂.plainDivisor₂ b₂.keep b₂.witness.2 =
      secondCommon.val)
    (comparison : Bool) (i : AllocationColumn K b₂.keep.card) (hi : i ∈ b₂.residualColumns) :
    firstTerm comparison (b₂.reconstruct i) * weight₂ (J₁ (b₂.reconstruct i)).val =
      originalSecondCommonScalar Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C
        primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ
        secondCommon b₂ secondTilt *
      originalSecondCoreCoefficient Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C
        primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ
        secondCommon b₂ J₂ secondTilt comparison i := by
  rw [firstResidualTerm_eq Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C primes m n
      firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ comparison
      (b₂.reconstruct i) (b₂.original_subset (b₂.reconstruct_mem i hi)),
    originalSourceModulus x S₁ S₂ S firstCommon b₁ J₁ hJ₁ secondCommon b₂ J₂ hJ₂ hcommon i hi,
    originalSecondCommonScalar_eq Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C
      primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ
      secondCommon b₂ secondTilt comparison]
  have h := second_original_to_core (data x) Q.correction (Q.moving.append E₁)
    (Q.remaining * exteriorMomentIdeal firstCommon) idx₁ hroot hemb side χ
    (firstTable comparison) b₂ secondCommon
    (Q.originalCommonScalar x Z t S₁ S₂ S b₁) secondTilt J₂ hJ₂ i hi
  rw [secondResidualCoreDictionary_coefficient] at h
  · exact h
  · exact hi

/-- The public residual rectangle uses the same nominal Gauss scales
as the full source rectangle, but its extracted common scalar belongs
only to the row weight. -/
def originalSecondResidualCoreFactors (comparison : Bool)
    (hcomparison : comparison = true →
      0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂) :
    SecondRectangularFactors rows PUnit side
      (SupportCartesian.plainResidual L₁ (primeSupport secondCommon.val) b₂.plainExtract₁)
      (SupportCartesian.plainResidual L₂ (primeSupport secondCommon.val) b₂.plainExtract₂)
      (fun j => SupportCartesian.primeLive (Slots₁ (idx₂ j)) (primeSupport secondCommon.val))
      J₂ (fun _ => PUnit.unit)
      (originalSecondCoreCoefficient Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C
        primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ
        secondCommon b₂ J₂ secondTilt comparison)
      (fun h i => rowOffset h - Real.log (A.exteriorNorm secondCommon * A.exteriorNorm (J₂ i))) χ := by
  have hG₁ : 0 < G₁ :=
    div_pos (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (idealNorm_pos K _))
      (idealNorm_pos K _)
  have hG₂ : 0 < G₂ :=
    div_pos (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (idealNorm_pos K _))
      (idealNorm_pos K _)
  have hH₁ := actual_left_positive x a Z Y₁ hZ S₁ S₂ S firstCommon b₁
    secondCommon b₂ comparison (fun hc => (hcomparison hc).1)
  have hH₂ := actual_right_positive x a Z Y₂ hZ S₁ S₂ S firstCommon b₁
    secondCommon b₂ comparison (fun hc => (hcomparison hc).2.1)
  let f := secondResidualCoreRectangularFactors rows (data x) Q.correction (Q.moving.append E₁)
    (Q.remaining * exteriorMomentIdeal firstCommon) idx₁ hroot hemb side χ
    (firstTable comparison) b₂ secondCommon secondTilt J₂ hJ₂ hZ
    (fun j => ((data x).geometry.slots (idx₁ j)).length_pos)
    (H₁ comparison) (H₂ comparison) Gslots hH₁ hH₂
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) rowOffset
  refine { f with gaussScale₁ := G₁, gaussScale₂ := G₂,
    gaussScale₁_pos := hG₁, gaussScale₂_pos := hG₂, coefficient_factor := ?_ }
  intro i hi
  rw [normalizedCoefficient_plain_product f.dictionary G₁ G₂ Gslots
    (H₁ comparison) (H₂ comparison) hG₁.le hH₁.le
    (actual_plain_product x a Z Y₁ Y₂ S₁ S₂ S firstCommon b₁
      secondCommon b₂ comparison (fun hc => (hcomparison hc).2.2)) i]
  exact f.coefficient_factor i hi

local notation "coreFactor" => originalSecondResidualCoreFactors Q x W a Z t Y₁ Y₂ hZ
  S₁ S₂ S firstCommon b₁ C primes m n firstRight δ firstTilt ξ hroot hemb
  J₁ hJ₁ hactive rows side χ secondCommon b₂ J₂ hJ₂ secondTilt rowOffset

/-- The complete comparison changes precisely the two original plain
tables. The retained prime occurrences, ray labels, characters and
nominal Gauss scales are the literal main fields. -/
def originalSecondCoreComparison
    (hcomparison : 0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂) :
    SecondCoefficientComparison (coreFactor false (by simp)).dictionary where
  leftAtom := (coreFactor true (fun _ => hcomparison)).dictionary.leftAtom
  rightAtom := (coreFactor true (fun _ => hcomparison)).dictionary.rightAtom
  scale₁ := (coreFactor true (fun _ => hcomparison)).dictionary.scale₁
  scale₂ := (coreFactor true (fun _ => hcomparison)).dictionary.scale₂
  leftWeight := (coreFactor true (fun _ => hcomparison)).dictionary.leftWeight
  rightWeight := (coreFactor true (fun _ => hcomparison)).dictionary.rightWeight
  plain₁ := (coreFactor true (fun _ => hcomparison)).dictionary.plain₁
  plain₂ := (coreFactor true (fun _ => hcomparison)).dictionary.plain₂

local notation "coreComparison" => originalSecondCoreComparison Q x W a Z t Y₁ Y₂ hZ
  S₁ S₂ S firstCommon b₁ C primes m n firstRight δ firstTilt ξ hroot hemb
  J₁ hJ₁ hactive rows side χ secondCommon b₂ J₂ hJ₂ secondTilt rowOffset

@[simp] theorem originalSecondCoreComparison_dictionary
    (hcomparison : 0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂) :
    (coreComparison hcomparison).dictionary =
      (coreFactor true (fun _ => hcomparison)).dictionary := rfl

/-- The whole centered coefficient is preserved at the fixed nominal
normalizer, even though each original plain profile has been compensated
using its own actual comparison length. -/
theorem originalSecondCoreComparison_coefficient
    (hcomparison : 0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂)
    (i : AllocationColumn K b₂.keep.card) (hi : i ∈ b₂.residualColumns) :
    (coreComparison hcomparison).centeredCoefficient
        (Real.sqrt G₁ : ℂ)⁻¹ (Real.sqrt G₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (Gslots j) : ℂ)⁻¹) i =
      originalSecondCoreCoefficient Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C
          primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ
          secondCommon b₂ J₂ secondTilt false i -
        originalSecondCoreCoefficient Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C
          primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ
          secondCommon b₂ J₂ secondTilt true i := by
  rw [SecondCoefficientComparison.centeredCoefficient,
    originalSecondCoreComparison_dictionary]
  exact congrArg₂ (fun z w : ℂ => z - w)
    ((coreFactor false (by simp)).coefficient_factor i hi).symm
    ((coreFactor true (fun _ => hcomparison)).coefficient_factor i hi).symm

/-- The original full common scalar multiplies the complete difference
exactly once. This is the identity used before common-scalar reweighting,
and before either of the actual row Cauchy steps. -/
theorem originalSecondSource_centered_to_core
    (hcommon : frozenSourceIdeal b₂.plainDivisor₁ b₂.plainDivisor₂ b₂.keep b₂.witness.2 =
      secondCommon.val)
    (hcomparison : 0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂)
    (i : AllocationColumn K b₂.keep.card) (hi : i ∈ b₂.residualColumns) :
    firstTerm false (b₂.reconstruct i) * weight₂ (J₁ (b₂.reconstruct i)).val -
        firstTerm true (b₂.reconstruct i) * weight₂ (J₁ (b₂.reconstruct i)).val =
      originalSecondCommonScalar Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C
          primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ
          secondCommon b₂ secondTilt *
        (coreComparison hcomparison).centeredCoefficient
          (Real.sqrt G₁ : ℂ)⁻¹ (Real.sqrt G₂ : ℂ)⁻¹
          (fun j => (Real.sqrt (Gslots j) : ℂ)⁻¹) i := by
  rw [originalSecondSource_to_core Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C
      primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ
      secondCommon b₂ J₂ hJ₂ secondTilt hcommon false i hi,
    originalSecondSource_to_core Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon b₁ C
      primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive side χ
      secondCommon b₂ J₂ hJ₂ secondTilt hcommon true i hi,
    originalSecondCoreComparison_coefficient Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁ C
      primes m n firstRight δ firstTilt ξ hroot hemb J₁ hJ₁ hactive rows side χ
      secondCommon b₂ J₂ hJ₂ secondTilt rowOffset hcomparison i hi,
    mul_sub]

end SameOriginalRectangles

section SameGaussCoefficient

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (C : A.GeneralArithmeticContext σ η hS)
variable {α β : Type*} (left : Finset α) (right : Finset β)
variable (fullI : α → A.Exterior) (fullJ : β → A.Exterior)
variable (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
variable (hDE : DE ∈ commonSupportPool left right
  (fun i => (fullI i).val) (fun j => (fullJ j).val))
variable (φ : 𝓢(mixedEmbedding.euclidean.mixedSpace K, ℂ))
variable (c : α → ℂ) (e : β → ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
variable (tilt : ℝ) (htilt : 0 < tilt) (htiltHalf : tilt ≤ 1 / 2)

local notation "B" => canonicalFirstCommonBlock C left right fullI fullJ DE hDE
local notation "chart" => FirstBlockProfileChart.canonicalLogWithCoefficients
  hΓ μv ν B C left right φ c e finiteTest hlc hcs radius mask tilt htilt htiltHalf
local notation "δ" => sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) mask
local notation "EL" => CanonicalSecondRectangularFactors.firstMovingFactors P R C
  B.primes B.leftMultiplicity B.rightMultiplicity false δ
local notation "ER" => CanonicalSecondRectangularFactors.firstMovingFactors P R C
  B.primes B.leftMultiplicity B.rightMultiplicity true δ

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z ell eps}
variable {M : Finset (HeightOneSpectrum A.R)} {cutoff : ℝ} {hcutoff : 1 ≤ cutoff}
variable (p : FirstBlockPoolData chart pool M cutoff hcutoff)
variable (Sdiv : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle) (ξ : ℝ)

/-- This is the coefficient field of the original amplified main
source, after its genuine first Fourier multiplier. The only local
gate fact is supplied by the live common branch above. -/
theorem main_left_coefficient
    (i : α) (hdiv : Sdiv.val ∣ (p.leftData.ideal i).val) :
    ((p.divisorPools.leftData Sdiv).mainSource
      (FirstGaussPoolData.twistedCoefficient (p.leftDivisorCoefficient Sdiv χ)
        chart.leftPoint ξ)).coefficient i =
      c i * (EL.residueHom (σ := σ) * normLogWeight (tilt - 1) ξ (-1))
        (B.leftResidual i).val := by
  have hg : p.leftDivisorCoefficient Sdiv χ i = p.originalLeftCoefficient i := by
    rw [FirstBlockPoolData.leftDivisorCoefficient, if_pos hdiv]
    change _ * ((SecondColumnSide.left.phase PUnit χ) PUnit.unit : ℂ) = _
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one]
  change p.leftDivisorCoefficient Sdiv χ i * jointPhase ξ (chart.leftPoint i) = _
  rw [hg]
  exact canonical_first_left_twisted (P := P) (R := R) hΓ μv ν C left right
    fullI fullJ DE hDE φ c e finiteTest hlc hcs radius mask tilt htilt htiltHalf ξ i

/-- The right source keeps its original opposite first Fourier
location. No conjugation is added to this coefficient field. -/
theorem main_right_coefficient
    (i : β) (hdiv : Sdiv.val ∣ (p.rightData.ideal i).val) :
    ((p.divisorPools.rightData Sdiv).mainSource
      (FirstGaussPoolData.twistedCoefficient (p.rightDivisorCoefficient Sdiv χ)
        (fun j => -chart.rightPoint j) ξ)).coefficient i =
      e i * (ER.residueHom (σ := σ) * normLogWeight (tilt - 1) ξ 1)
        (B.rightResidual i).val := by
  have hg : p.rightDivisorCoefficient Sdiv χ i = p.originalRightCoefficient i := by
    rw [FirstBlockPoolData.rightDivisorCoefficient, if_pos hdiv]
    change _ * ((SecondColumnSide.right.phase PUnit χ) PUnit.unit : ℂ) = _
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one]
  change p.rightDivisorCoefficient Sdiv χ i * jointPhase ξ (-chart.rightPoint i) = _
  rw [hg]
  exact canonical_first_right_twisted (P := P) (R := R) hΓ μv ν C left right
    fullI fullJ DE hDE φ c e finiteTest hlc hcs radius mask tilt htilt htiltHalf ξ i

/-- Each genuine 1/6/7 error coefficient retains its actual prime norm
power and the full computed reciprocal prime character. -/
theorem error_left_coefficient
    (prime : ExteriorPrime A) (n : ℕ)
    (i : (p.divisorPools.leftData Sdiv).valuationColumns prime n)
    (hdiv : Sdiv.val ∣ (p.leftData.ideal i.val).val) :
    ((p.divisorPools.leftData Sdiv).residualSource prime n
      (FirstGaussPoolData.twistedCoefficient (p.leftDivisorCoefficient Sdiv χ)
        chart.leftPoint ξ)).coefficient i =
      (c i.val * (EL.residueHom (σ := σ) * normLogWeight (tilt - 1) ξ (-1))
        (B.leftResidual i.val).val) * (Q prime : ℂ) ^ n *
          (poolMovingFactors (P := P) (R := R) C prime n).residueValue (σ := σ)
            ((p.divisorPools.leftData Sdiv).residualPresentation prime n i).residual.val := by
  change (p.divisorPools.leftData Sdiv).residualCoefficient prime n _ i = _
  rw [FirstGaussPoolData.residualCoefficient_eq, pool_columnPhase (P := P) (R := R)]
  rw [show FirstGaussPoolData.twistedCoefficient (p.leftDivisorCoefficient Sdiv χ)
      chart.leftPoint ξ i.val =
      c i.val * (EL.residueHom (σ := σ) * normLogWeight (tilt - 1) ξ (-1))
        (B.leftResidual i.val).val from
    main_left_coefficient hΓ μv ν P R C left right fullI fullJ DE hDE φ c e finiteTest
      hlc hcs radius mask tilt htilt htiltHalf p Sdiv χ ξ i.val hdiv]

theorem error_right_coefficient
    (prime : ExteriorPrime A) (n : ℕ)
    (i : (p.divisorPools.rightData Sdiv).valuationColumns prime n)
    (hdiv : Sdiv.val ∣ (p.rightData.ideal i.val).val) :
    ((p.divisorPools.rightData Sdiv).residualSource prime n
      (FirstGaussPoolData.twistedCoefficient (p.rightDivisorCoefficient Sdiv χ)
        (fun j => -chart.rightPoint j) ξ)).coefficient i =
      (e i.val * (ER.residueHom (σ := σ) * normLogWeight (tilt - 1) ξ 1)
        (B.rightResidual i.val).val) * (Q prime : ℂ) ^ n *
          (poolMovingFactors (P := P) (R := R) C prime n).residueValue (σ := σ)
            ((p.divisorPools.rightData Sdiv).residualPresentation prime n i).residual.val := by
  change (p.divisorPools.rightData Sdiv).residualCoefficient prime n _ i = _
  rw [FirstGaussPoolData.residualCoefficient_eq, pool_columnPhase (P := P) (R := R)]
  rw [show FirstGaussPoolData.twistedCoefficient (p.rightDivisorCoefficient Sdiv χ)
      (fun j => -chart.rightPoint j) ξ i.val =
      e i.val * (ER.residueHom (σ := σ) * normLogWeight (tilt - 1) ξ 1)
        (B.rightResidual i.val).val from
    main_right_coefficient hΓ μv ν P R C left right fullI fullJ DE hDE φ c e finiteTest
      hlc hcs radius mask tilt htilt htiltHalf p Sdiv χ ξ i.val hdiv]

variable (p₀ : FirstBlockDirectData chart M cutoff hcutoff)
variable (Ddiv : divisorPool p₀.rightData.columns (fun j => (p₀.rightData.ideal j).val))

/-- The direct regime has exactly the same original left coefficient;
no pool is introduced to obtain this identity. -/
theorem direct_left_coefficient
    (i : α) (hdiv : Ddiv.val ∣ (p₀.leftData.ideal i).val) :
    (p₀.leftData.directSource
      (FirstGaussPoolData.twistedCoefficient (p₀.leftDivisorCoefficient Ddiv χ)
        chart.leftPoint ξ)).coefficient i =
      c i * (EL.residueHom (σ := σ) * normLogWeight (tilt - 1) ξ (-1))
        (B.leftResidual i).val := by
  have hg : p₀.leftDivisorCoefficient Ddiv χ i = p₀.originalLeftCoefficient i := by
    rw [FirstBlockDirectData.leftDivisorCoefficient, if_pos hdiv]
    change _ * ((SecondColumnSide.left.phase PUnit χ) PUnit.unit : ℂ) = _
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one]
  change p₀.leftDivisorCoefficient Ddiv χ i * jointPhase ξ (chart.leftPoint i) = _
  rw [hg]
  exact canonical_first_left_twisted (P := P) (R := R) hΓ μv ν C left right
    fullI fullJ DE hDE φ c e finiteTest hlc hcs radius mask tilt htilt htiltHalf ξ i

/-- The direct right regime also uses the original negative location,
leaving the later allocated coefficient to apply the whole star once. -/
theorem direct_right_coefficient
    (i : β) (hdiv : Ddiv.val ∣ (p₀.rightData.ideal i).val) :
    (p₀.rightData.directSource
      (FirstGaussPoolData.twistedCoefficient (p₀.rightDivisorCoefficient Ddiv χ)
        (fun j => -chart.rightPoint j) ξ)).coefficient i =
      e i * (ER.residueHom (σ := σ) * normLogWeight (tilt - 1) ξ 1)
        (B.rightResidual i).val := by
  have hg : p₀.rightDivisorCoefficient Ddiv χ i = p₀.originalRightCoefficient i := by
    rw [FirstBlockDirectData.rightDivisorCoefficient, if_pos hdiv]
    change _ * ((SecondColumnSide.right.phase PUnit χ) PUnit.unit : ℂ) = _
    rw [CanonicalSecondRectangularFactors.punit_phase, mul_one]
  change p₀.rightDivisorCoefficient Ddiv χ i * jointPhase ξ (-chart.rightPoint i) = _
  rw [hg]
  exact canonical_first_right_twisted (P := P) (R := R) hΓ μv ν C left right
    fullI fullJ DE hDE φ c e finiteTest hlc hcs radius mask tilt htilt htiltHalf ξ i

end SameGaussCoefficient

end HeckeSkeleton.Moments.EngineStep.CanonicalActualSecondRectangles
