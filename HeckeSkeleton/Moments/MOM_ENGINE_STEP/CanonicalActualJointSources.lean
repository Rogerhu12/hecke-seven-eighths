import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalJointAllocatedSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalBoundedChildData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalLogNormLocations

/-!
# Fixed actual sources for both Fourier variables

The original first mode is moved from the computed individual weights
to its literal logarithmic location. The original second row translation
is removed by the exact unit-phase identity, and both modes then live in
the Hilbert product. The actual source, its allocation, and its complete
arithmetic row therefore precede the two Fourier variables.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalActualJointSources

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

def secondLogSlope : SecondColumnSide → ℝ
  | .left => -1
  | .right => 1

theorem pair_location (slope secondSlope x y : ℝ) :
    WithLp.toLp 2 (slope * x, secondSlope * y) =
      x • firstDirection slope + y • secondDirection secondSlope := by
  apply (WithLp.ofLp_injective 2)
  change (slope * x, secondSlope * y) =
    (x * slope + y * 0, x * 0 + y * secondSlope)
  ext <;> ring

section OriginalMode

variable {H : Type*} {k : ℕ}
variable (s : ActualAllocatedSource A ℝ H k)
variable (W₁ W₂ : ℝ → ℂ) (W : Fin k → ℝ → ℂ)
variable (N₁ N₂ : ℝ) (N : Fin k → ℝ)
variable (first₁ first₂ second₁ second₂ : HeckeGeneral.Analysis.NonzeroIdeal K) (δ₁ δ₂ slope : ℝ)

/-- Only the actual computed original profile weights are installed.
All arithmetic, rows, normalizations and finite columns are retained. -/
def originalMode (ξ : ℝ) : ActualAllocatedSource A ℝ H k :=
  { s with
    leftWeight := fun _ I => rawPlainWeight W₁ N₁ first₁ second₁ δ₁ δ₂ ξ slope I
    rightWeight := fun _ I => rawPlainWeight W₂ N₂ first₂ second₂ δ₁ δ₂ ξ slope I
    slotWeight := fun _ j p => rawPrimeWeight (W j) (N j) δ₁ δ₂ ξ slope p }

local notation "x₁" => fun (_ : H) I => slope * Real.log (idealNorm K (second₁ * I))
local notation "x₂" => fun (_ : H) I => slope * Real.log (idealNorm K (second₂ * I))
local notation "xslot" => fun (_ : H) (_ : Fin k) (p : HeightOneSpectrum (𝓞 K)) =>
  slope * Real.log (Ideal.absNorm p.asIdeal : ℝ)

/-- The first-mode factorization is proved at the original individual
plain and prime occurrences; no whole-coefficient identity is assumed. -/
theorem originalMode_eq_withFirstMode (ξ : ℝ) :
    originalMode s W₁ W₂ W N₁ N₂ N first₁ first₂ second₁ second₂ δ₁ δ₂ slope ξ =
      CanonicalJointAllocatedSource.withFirstMode
        (originalMode s W₁ W₂ W N₁ N₂ N first₁ first₂ second₁ second₂ δ₁ δ₂ slope 0)
        x₁ x₂ xslot ξ := by
  have hleft : (fun (_ : H) I => rawPlainWeight W₁ N₁ first₁ second₁ δ₁ δ₂ ξ slope I) =
      fun (_ : H) I => rawPlainWeight W₁ N₁ first₁ second₁ δ₁ δ₂ 0 slope I *
        jointPhase ξ (slope * Real.log (idealNorm K (second₁ * I))) := by
    funext h I
    exact rawPlainWeight_eq_zero_mul_phase W₁ N₁ first₁ second₁ I δ₁ δ₂ ξ slope
  have hright : (fun (_ : H) I => rawPlainWeight W₂ N₂ first₂ second₂ δ₁ δ₂ ξ slope I) =
      fun (_ : H) I => rawPlainWeight W₂ N₂ first₂ second₂ δ₁ δ₂ 0 slope I *
        jointPhase ξ (slope * Real.log (idealNorm K (second₂ * I))) := by
    funext h I
    exact rawPlainWeight_eq_zero_mul_phase W₂ N₂ first₂ second₂ I δ₁ δ₂ ξ slope
  have hslot : (fun (_ : H) j p => rawPrimeWeight (W j) (N j) δ₁ δ₂ ξ slope p) =
      fun (_ : H) j p => rawPrimeWeight (W j) (N j) δ₁ δ₂ 0 slope p *
        jointPhase ξ (slope * Real.log (Ideal.absNorm p.asIdeal : ℝ)) := by
    funext h j p
    exact rawPrimeWeight_eq_zero_mul_phase (W j) (N j) δ₁ δ₂ ξ slope p
  simp only [originalMode, CanonicalJointAllocatedSource.withFirstMode,
    hleft, hright, hslot]

end OriginalMode

section PatternRows

variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [Fintype ι] [DecidableEq ι] {k : ℕ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)
variable (s : ActualAllocatedSource A V rows.live k)

/-- Both actual finite classes are carried by the index type, so the
computed arithmetic dictionary is valid for all of its row indices. -/
def byPatternSector (pattern : ι → Bool)
    (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :
    ActualAllocatedSource A V
      (CanonicalOriginalPhaseCalibration.PatternSector P rows C pattern sector) k :=
  (s.subtypeRows (fun h =>
    actualNonunitPattern C rows.primes rows.leftMultiplicity rows.rightMultiplicity
      (rows.frequency h.val) = pattern)).subtypeRows
        (fun h => (rows.extractedRow C h.val).sector P = sector)

local instance unitSectorFintype :
    Fintype (SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :=
  Fintype.ofFinite _

/-- No class is discarded. This is an exact finite partition of the
original fixed source, before either normalized child is selected. -/
theorem energy_eq_sum_byPatternSector (ξ : V) :
    s.energy (σ := σ) ξ =
      ∑ pattern : ι → Bool, ∑ sector,
        (byPatternSector P rows C s pattern sector).energy (σ := σ) ξ := by
  rw [s.energy_eq_sum_subtypeRows (fun h =>
    actualNonunitPattern C rows.primes rows.leftMultiplicity rows.rightMultiplicity
      (rows.frequency h.val)) ξ]
  apply Finset.sum_congr rfl
  intro pattern _
  exact (s.subtypeRows (fun h =>
    actualNonunitPattern C rows.primes rows.leftMultiplicity rows.rightMultiplicity
      (rows.frequency h.val) = pattern)).energy_eq_sum_subtypeRows
        (fun h => (rows.extractedRow C h.val).sector P) ξ

end PatternRows

section MainSource

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
local notation "frame" => fun ξ => (factors ξ).frame C allocationIdeal selection hne
local notation "rowTranslation" => fun h => -(rowOffset h - Real.log (A.exteriorNorm secondCommon))
local notation "slope" => if firstRight then 1 else -1
local notation "x₁" => fun (_ : rows.live) I => slope * Real.log (idealNorm K (b₂.plainDivisor₁ * I))
local notation "x₂" => fun (_ : rows.live) I => slope * Real.log (idealNorm K (b₂.plainDivisor₂ * I))
local notation "xslot" => fun (_ : rows.live) (_ : Fin b₂.keep.card) (p : HeightOneSpectrum (𝓞 K)) =>
  slope * Real.log (Ideal.absNorm p.asIdeal : ℝ)

/-- The actual row translation is removed without changing its
complete coefficient or finite allocation. -/
def canonicalFrame (ξ : ℝ) : SecondSideFrame (V := ℝ) C rows PUnit side b₂.keep.card :=
  (frame ξ).translateLocations rowTranslation (fun _ => 0) (fun _ _ => 0)

local notation "plainFrame" => canonicalFrame Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S
  firstCommon b₁ C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive
  rows side χ secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
  allocationIdeal selection hne

def source (ξ : ℝ) : ActualAllocatedSource A ℝ rows.live b₂.keep.card :=
  (plainFrame ξ).source

local notation "actualSource" => source Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne

def jointSource : ActualAllocatedSource A (WithLp 2 (ℝ × ℝ)) rows.live b₂.keep.card :=
  CanonicalJointAllocatedSource.jointSource (actualSource 0) x₁ x₂ xslot

local notation "joint" => jointSource Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne

local notation "rawMode" => originalMode (actualSource 0)
  (W.left PUnit.unit t) (W.right PUnit.unit t)
  (fun j => ((data x).geometry.slots (idx₁ (idx₂ j))).profile t)
  (if comparison then Y₁ else Z ^ a.n₁) (if comparison then Y₂ else Z ^ a.n₂)
  (fun j => Z ^ ((data x).geometry.slots (idx₁ (idx₂ j))).length)
  b₁.plainDivisor₁ b₁.plainDivisor₂ b₂.plainDivisor₁ b₂.plainDivisor₂ firstTilt secondTilt slope

/-- This is a definitional inspection of the actually constructed
source. Only its three original weights depend on the first mode. -/
theorem source_originalMode (ξ : ℝ) : actualSource ξ = rawMode ξ := by
  cases side <;> rfl

theorem source_eq_withFirstMode (ξ : ℝ) :
    actualSource ξ = CanonicalJointAllocatedSource.withFirstMode (actualSource 0) x₁ x₂ xslot ξ := by
  rw [source_originalMode Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
    C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
    allocationIdeal selection hne ξ,
    originalMode_eq_withFirstMode]
  rw [← source_originalMode Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
    C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
    allocationIdeal selection hne 0]

/-- Both original Fourier modes act on the same fixed source. -/
theorem source_energy (ξ ζ : ℝ) :
    (actualSource ξ).energy (σ := σ) ζ = (joint).energy (σ := σ) (WithLp.toLp 2 (ξ, ζ)) := by
  rw [source_eq_withFirstMode Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
    C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
    allocationIdeal selection hne ξ]
  exact CanonicalJointAllocatedSource.energy_identity (σ := σ) (actualSource 0) x₁ x₂ xslot ξ ζ

/-- The original actual rectangle, with its real common row radius,
is exactly the fixed joint source divided by the same Gauss scale. -/
theorem frame_energy_eq_joint (ξ ζ : ℝ) :
    (frame ξ).energy ζ =
      (joint).energy (σ := σ) (WithLp.toLp 2 (ξ, ζ)) / (frame 0).normalizationScale := by
  calc
    (frame ξ).energy ζ = (plainFrame ξ).energy ζ :=
      ((frame ξ).translateLocations_energy rowTranslation (fun _ => 0) (fun _ _ => 0) ζ).symm
    _ = (actualSource ξ).energy (σ := σ) ζ / (frame 0).normalizationScale := by
      rw [(plainFrame ξ).energy_eq_div_scale] <;> rfl
    _ = _ := by
      rw [source_energy Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
        C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
        secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
        allocationIdeal selection hne ξ ζ]

theorem source_leftLocation (ξ : ℝ) (h : rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (actualSource ξ).leftLocation h I = secondLogSlope side * Real.log (idealNorm K I) := by
  cases side with
  | left =>
    change -(rowOffset h.val - Real.log (A.exteriorNorm secondCommon)) +
      (rowOffset h.val - Real.log (A.exteriorNorm secondCommon) - Real.log (idealNorm K I)) =
        (-1) * Real.log (idealNorm K I)
    ring
  | right =>
    change -(-(rowOffset h.val - Real.log (A.exteriorNorm secondCommon)) +
      (rowOffset h.val - Real.log (A.exteriorNorm secondCommon) - Real.log (idealNorm K I))) =
        1 * Real.log (idealNorm K I)
    ring

theorem source_rightLocation (ξ : ℝ) (h : rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (actualSource ξ).rightLocation h I = secondLogSlope side * Real.log (idealNorm K I) := by
  cases side with
  | left =>
    change 0 + -Real.log (idealNorm K I) = (-1) * Real.log (idealNorm K I)
    ring
  | right =>
    change -(0 + -Real.log (idealNorm K I)) = 1 * Real.log (idealNorm K I)
    ring

theorem source_slotLocation (ξ : ℝ) (h : rows.live) (j : Fin b₂.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) :
    (actualSource ξ).slotLocation h j p =
      secondLogSlope side * Real.log (Ideal.absNorm p.asIdeal : ℝ) := by
  cases side with
  | left =>
    change 0 + -Real.log (Ideal.absNorm p.asIdeal : ℝ) =
      (-1) * Real.log (Ideal.absNorm p.asIdeal : ℝ)
    ring
  | right =>
    change -(0 + -Real.log (Ideal.absNorm p.asIdeal : ℝ)) =
      1 * Real.log (Ideal.absNorm p.asIdeal : ℝ)
    ring

theorem joint_leftLocation (h : rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (joint).leftLocation h I =
      Real.log (idealNorm K (b₂.plainDivisor₁ * I)) • firstDirection slope +
        Real.log (idealNorm K I) • secondDirection (secondLogSlope side) := by
  change WithLp.toLp 2 (_, (actualSource 0).leftLocation h I) = _
  rw [source_leftLocation Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
    C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
    allocationIdeal selection hne 0 h I]
  exact pair_location _ _ _ _

theorem joint_rightLocation (h : rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (joint).rightLocation h I =
      Real.log (idealNorm K (b₂.plainDivisor₂ * I)) • firstDirection slope +
        Real.log (idealNorm K I) • secondDirection (secondLogSlope side) := by
  change WithLp.toLp 2 (_, (actualSource 0).rightLocation h I) = _
  rw [source_rightLocation Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
    C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
    allocationIdeal selection hne 0 h I]
  exact pair_location _ _ _ _

theorem joint_slotLocation (h : rows.live) (j : Fin b₂.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) :
    (joint).slotLocation h j p =
      Real.log (Ideal.absNorm p.asIdeal : ℝ) • firstDirection slope +
        Real.log (Ideal.absNorm p.asIdeal : ℝ) • secondDirection (secondLogSlope side) := by
  change WithLp.toLp 2 (_, (actualSource 0).slotLocation h j p) = _
  rw [source_slotLocation Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon b₁
    C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
    allocationIdeal selection hne 0 h j p]
  exact pair_location _ _ _ _


/-- These are the same original arithmetic characters, including the
actual empty-mask unit phase, before the second quotient character. -/
theorem joint_characters (h : rows.live) :
    (joint).characters h = movingSourceCharacters (data x) Q.correction
      ((Q.moving.append
        (CanonicalSecondRectangularFactors.firstMovingFactors P R C primes m n firstRight δ)).append
          (CanonicalSecondRectangularFactors.secondMaskMovingFactors P R
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)))
      (Q.remaining * exteriorMomentIdeal firstCommon) (fun j => idx₁ (idx₂ j)) := by
  cases side <;> rfl

theorem joint_row_momentIdeal (h : rows.live) :
    ((joint).row h).momentIdeal = (rows.extractedRow C h).momentIdeal := by
  cases side <;> rfl

theorem joint_row_element (h : rows.live) :
    ((joint).row h).element = (rows.extractedRow C h).element := by
  cases side <;> rfl

theorem joint_extractedFactor (h : rows.live) :
    (joint).extractedFactor h =
      match side with
      | .left => rows.factor C h.val
      | .right => -(rows.factor C h.val) := by
  cases side <;> rfl

theorem joint_base : (joint).base = Z := by
  cases side <;> rfl

theorem joint_leftScale : (joint).scale₁ =
    (if comparison then Y₁ else Z ^ a.n₁) /
      idealNorm K b₁.plainDivisor₁ / idealNorm K b₂.plainDivisor₁ := by
  cases side <;> rfl

theorem joint_rightScale : (joint).scale₂ =
    (if comparison then Y₂ else Z ^ a.n₂) /
      idealNorm K b₁.plainDivisor₂ / idealNorm K b₂.plainDivisor₂ := by
  cases side <;> rfl

theorem joint_length (j : Fin b₂.keep.card) :
    (joint).length j = ((data x).geometry.slots (idx₁ (idx₂ j))).length := by
  cases side <;> rfl

theorem joint_leftWeight (h : rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (joint).leftWeight h I =
      rawPlainWeight (W.left PUnit.unit t) (if comparison then Y₁ else Z ^ a.n₁)
        b₁.plainDivisor₁ b₂.plainDivisor₁ firstTilt secondTilt 0 slope I := by
  cases side <;> rfl

theorem joint_rightWeight (h : rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (joint).rightWeight h I =
      rawPlainWeight (W.right PUnit.unit t) (if comparison then Y₂ else Z ^ a.n₂)
        b₁.plainDivisor₂ b₂.plainDivisor₂ firstTilt secondTilt 0 slope I := by
  cases side <;> rfl

theorem joint_slotWeight (h : rows.live) (j : Fin b₂.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) :
    (joint).slotWeight h j p =
      rawPrimeWeight (((data x).geometry.slots (idx₁ (idx₂ j))).profile t)
        (Z ^ ((data x).geometry.slots (idx₁ (idx₂ j))).length)
        firstTilt secondTilt 0 slope p := by
  cases side <;> rfl

end MainSource

namespace Pool

open CanonicalActualPoolRectangles

section ActualSource

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
local notation "frame" => fun ξ => (factors ξ).frame C allocationIdeal selection hne
local notation "rowTranslation" => fun h => -(rowOffset h - Real.log (A.exteriorNorm secondCommon))
local notation "slope" => if firstRight then 1 else -1
local notation "x₁" => fun (_ : rows.live) I => slope * Real.log (idealNorm K (b₂.plainDivisor₁ * I))
local notation "x₂" => fun (_ : rows.live) I => slope * Real.log (idealNorm K (b₂.plainDivisor₂ * I))
local notation "xslot" => fun (_ : rows.live) (_ : Fin b₂.keep.card) (p : HeightOneSpectrum (𝓞 K)) =>
  slope * Real.log (Ideal.absNorm p.asIdeal : ℝ)

/-- The actual row translation is removed without changing its
complete coefficient or finite allocation. -/
def canonicalFrame (ξ : ℝ) : SecondSideFrame (V := ℝ) C rows PUnit side b₂.keep.card :=
  (frame ξ).translateLocations rowTranslation (fun _ => 0) (fun _ _ => 0)

local notation "plainFrame" => canonicalFrame Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S
  firstCommon p v hv b₁ C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive
  rows side χ secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
  allocationIdeal selection hne

def source (ξ : ℝ) : ActualAllocatedSource A ℝ rows.live b₂.keep.card :=
  (plainFrame ξ).source

local notation "actualSource" => source Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne

def jointSource : ActualAllocatedSource A (WithLp 2 (ℝ × ℝ)) rows.live b₂.keep.card :=
  CanonicalJointAllocatedSource.jointSource (actualSource 0) x₁ x₂ xslot

local notation "joint" => jointSource Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
  C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
  secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison allocationIdeal selection hne

local notation "rawMode" => originalMode (actualSource 0)
  (W.left PUnit.unit t) (W.right PUnit.unit t)
  (fun j => ((data x).geometry.slots (idx₁ (idx₂ j))).profile t)
  (if comparison then Y₁ else Z ^ a.n₁) (if comparison then Y₂ else Z ^ a.n₂)
  (fun j => Z ^ ((data x).geometry.slots (idx₁ (idx₂ j))).length)
  b₁.plainDivisor₁ b₁.plainDivisor₂ b₂.plainDivisor₁ b₂.plainDivisor₂ firstTilt secondTilt slope

/-- This is a definitional inspection of the actually constructed
source. Only its three original weights depend on the first mode. -/
theorem source_originalMode (ξ : ℝ) : actualSource ξ = rawMode ξ := by
  cases side <;> rfl

theorem source_eq_withFirstMode (ξ : ℝ) :
    actualSource ξ = CanonicalJointAllocatedSource.withFirstMode (actualSource 0) x₁ x₂ xslot ξ := by
  rw [source_originalMode Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
    C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
    allocationIdeal selection hne ξ,
    originalMode_eq_withFirstMode]
  rw [← source_originalMode Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
    C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
    allocationIdeal selection hne 0]

/-- Both original Fourier modes act on the same fixed source. -/
theorem source_energy (ξ ζ : ℝ) :
    (actualSource ξ).energy (σ := σ) ζ = (joint).energy (σ := σ) (WithLp.toLp 2 (ξ, ζ)) := by
  rw [source_eq_withFirstMode Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
    C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
    allocationIdeal selection hne ξ]
  exact CanonicalJointAllocatedSource.energy_identity (σ := σ) (actualSource 0) x₁ x₂ xslot ξ ζ

/-- The original actual pool rectangle, with its real common row radius,
is exactly the fixed joint source divided by the same Gauss scale. -/
theorem frame_energy_eq_joint (ξ ζ : ℝ) :
    (frame ξ).energy ζ =
      (joint).energy (σ := σ) (WithLp.toLp 2 (ξ, ζ)) / (frame 0).normalizationScale := by
  calc
    (frame ξ).energy ζ = (plainFrame ξ).energy ζ :=
      ((frame ξ).translateLocations_energy rowTranslation (fun _ => 0) (fun _ _ => 0) ζ).symm
    _ = (actualSource ξ).energy (σ := σ) ζ / (frame 0).normalizationScale := by
      rw [(plainFrame ξ).energy_eq_div_scale] <;> rfl
    _ = _ := by
      rw [source_energy Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
        C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
        secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
        allocationIdeal selection hne ξ ζ]

theorem source_leftLocation (ξ : ℝ) (h : rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (actualSource ξ).leftLocation h I = secondLogSlope side * Real.log (idealNorm K I) := by
  cases side with
  | left =>
    change -(rowOffset h.val - Real.log (A.exteriorNorm secondCommon)) +
      (rowOffset h.val - Real.log (A.exteriorNorm secondCommon) - Real.log (idealNorm K I)) =
        (-1) * Real.log (idealNorm K I)
    ring
  | right =>
    change -(-(rowOffset h.val - Real.log (A.exteriorNorm secondCommon)) +
      (rowOffset h.val - Real.log (A.exteriorNorm secondCommon) - Real.log (idealNorm K I))) =
        1 * Real.log (idealNorm K I)
    ring

theorem source_rightLocation (ξ : ℝ) (h : rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (actualSource ξ).rightLocation h I = secondLogSlope side * Real.log (idealNorm K I) := by
  cases side with
  | left =>
    change 0 + -Real.log (idealNorm K I) = (-1) * Real.log (idealNorm K I)
    ring
  | right =>
    change -(0 + -Real.log (idealNorm K I)) = 1 * Real.log (idealNorm K I)
    ring

theorem source_slotLocation (ξ : ℝ) (h : rows.live) (j : Fin b₂.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) :
    (actualSource ξ).slotLocation h j p =
      secondLogSlope side * Real.log (Ideal.absNorm p.asIdeal : ℝ) := by
  cases side with
  | left =>
    change 0 + -Real.log (Ideal.absNorm p.asIdeal : ℝ) =
      (-1) * Real.log (Ideal.absNorm p.asIdeal : ℝ)
    ring
  | right =>
    change -(0 + -Real.log (Ideal.absNorm p.asIdeal : ℝ)) =
      1 * Real.log (Ideal.absNorm p.asIdeal : ℝ)
    ring

theorem joint_leftLocation (h : rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (joint).leftLocation h I =
      Real.log (idealNorm K (b₂.plainDivisor₁ * I)) • firstDirection slope +
        Real.log (idealNorm K I) • secondDirection (secondLogSlope side) := by
  change WithLp.toLp 2 (_, (actualSource 0).leftLocation h I) = _
  rw [source_leftLocation Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
    C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
    allocationIdeal selection hne 0 h I]
  exact pair_location _ _ _ _

theorem joint_rightLocation (h : rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (joint).rightLocation h I =
      Real.log (idealNorm K (b₂.plainDivisor₂ * I)) • firstDirection slope +
        Real.log (idealNorm K I) • secondDirection (secondLogSlope side) := by
  change WithLp.toLp 2 (_, (actualSource 0).rightLocation h I) = _
  rw [source_rightLocation Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
    C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
    allocationIdeal selection hne 0 h I]
  exact pair_location _ _ _ _

theorem joint_slotLocation (h : rows.live) (j : Fin b₂.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) :
    (joint).slotLocation h j p =
      Real.log (Ideal.absNorm p.asIdeal : ℝ) • firstDirection slope +
        Real.log (Ideal.absNorm p.asIdeal : ℝ) • secondDirection (secondLogSlope side) := by
  change WithLp.toLp 2 (_, (actualSource 0).slotLocation h j p) = _
  rw [source_slotLocation Q x W a Z t Y₁ Y₂ hZ S₁ S₂ S firstCommon p v hv b₁
    C primes m n firstRight δ firstTilt hroot hemb J₁ hJ₁ hactive rows side χ
    secondCommon b₂ J₂ hJ₂ secondTilt rowOffset comparison hcomparison
    allocationIdeal selection hne 0 h j p]
  exact pair_location _ _ _ _


/-- These are the same original arithmetic characters, including the
actual empty-mask unit phase, before the second quotient character. -/
theorem joint_characters (h : rows.live) :
    (joint).characters h = movingSourceCharacters (data x) Q.correction
      (((Q.moving.append
        (CanonicalSecondRectangularFactors.firstMovingFactors P R C primes m n firstRight δ)).append
          (poolMovingFactors (P := P) (R := R) C p v)).append
          (CanonicalSecondRectangularFactors.secondMaskMovingFactors P R
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)))
      (Q.remaining * exteriorMomentIdeal (combinedCommon firstCommon p v)) (fun j => idx₁ (idx₂ j)) := by
  cases side <;> rfl

theorem joint_row_momentIdeal (h : rows.live) :
    ((joint).row h).momentIdeal = (rows.extractedRow C h).momentIdeal := by
  cases side <;> rfl

theorem joint_row_element (h : rows.live) :
    ((joint).row h).element = (rows.extractedRow C h).element := by
  cases side <;> rfl

theorem joint_extractedFactor (h : rows.live) :
    (joint).extractedFactor h =
      match side with
      | .left => rows.factor C h.val
      | .right => -(rows.factor C h.val) := by
  cases side <;> rfl

theorem joint_base : (joint).base = Z := by
  cases side <;> rfl

theorem joint_leftScale : (joint).scale₁ =
    (if comparison then Y₁ else Z ^ a.n₁) /
      idealNorm K b₁.plainDivisor₁ / idealNorm K b₂.plainDivisor₁ := by
  cases side <;> rfl

theorem joint_rightScale : (joint).scale₂ =
    (if comparison then Y₂ else Z ^ a.n₂) /
      idealNorm K b₁.plainDivisor₂ / idealNorm K b₂.plainDivisor₂ := by
  cases side <;> rfl

theorem joint_length (j : Fin b₂.keep.card) :
    (joint).length j = ((data x).geometry.slots (idx₁ (idx₂ j))).length := by
  cases side <;> rfl

theorem joint_leftWeight (h : rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (joint).leftWeight h I =
      rawPlainWeight (W.left PUnit.unit t) (if comparison then Y₁ else Z ^ a.n₁)
        b₁.plainDivisor₁ b₂.plainDivisor₁ firstTilt secondTilt 0 slope I := by
  cases side <;> rfl

theorem joint_rightWeight (h : rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (joint).rightWeight h I =
      rawPlainWeight (W.right PUnit.unit t) (if comparison then Y₂ else Z ^ a.n₂)
        b₁.plainDivisor₂ b₂.plainDivisor₂ firstTilt secondTilt 0 slope I := by
  cases side <;> rfl

theorem joint_slotWeight (h : rows.live) (j : Fin b₂.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) :
    (joint).slotWeight h j p =
      rawPrimeWeight (((data x).geometry.slots (idx₁ (idx₂ j))).profile t)
        (Z ^ ((data x).geometry.slots (idx₁ (idx₂ j))).length)
        firstTilt secondTilt 0 slope p := by
  cases side <;> rfl

end ActualSource

end Pool

end HeckeSkeleton.Moments.EngineStep.CanonicalActualJointSources

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualJointSources.source_eq_withFirstMode
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualJointSources.frame_energy_eq_joint
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualJointSources.joint_leftLocation

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualJointSources.Pool.frame_energy_eq_joint

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualJointSources.energy_eq_sum_byPatternSector

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualJointSources.joint_characters
