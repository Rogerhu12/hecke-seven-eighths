import HeckeSkeleton.ExpansionModels.SourceMomentModels
import HeckeSkeleton.ExpansionModels.WitnessHeightNormalization

/-!
# The detector's actual inverse profile as one independent two-scale family

The normalization is exactly the project's D^(-1/2) finite-sum normalization.
The exponent is -beta+i*nu.  No extra one-half is inserted into the profile.
The cutoff ratio is D/U^t, so the same constructor works for marked and
independent unmarked moments without a subdivision argument.

Six global coordinates suffice: three common physical Mellin coordinates,
half the cutoff exponent t, a bounded finite-presentation code, and the
height anchor T.  Rowwise beta uses sigma(0); the actual frequency is
frequencyScale*tau(0), with the stored tau divided by that fixed positive
scale.  This dimension is fixed
before slots, sectors and the target.  The arithmetic presentation selector
must range over the actual finite source family; smooth-profile and analytic
admissibility estimates remain separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.ExpansionRecipe

open NumberField HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ExpansionRecipe
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

abbrev detectorParameterDimension : ℕ := 6

abbrev DetectorVector := Fin detectorParameterDimension → ℝ

/-- A single fixed finite arithmetic presentation family.  Decoding a
continuous coordinate only selects one of these entries.  No smoothness of
this discrete selector is asserted or needed for taking the maximum of the
separate presentation constants; any derivative theorem must be proved
within a fixed entry before combining the finite family. -/
structure DetectorPresentationFamily (ψ : HeckeCharacter K) where
  count : ℕ
  count_pos : 0 < count
  entry : Fin count → PolynomialPresentation K ψ

/-- Multiplying an original actual ideal test by the physical inverse
cutoff and an everywhere nonzero norm power preserves exact finite support.
The original support is FILTERED; common arithmetic masks remain elsewhere. -/
def cutoffTwistTest (W : IdealTest K) (V : ℝ → ℂ) (R : ℝ)
    (β ν : NonzeroIdeal K → ℝ) : IdealTest K where
  profile u _ y := W.profile u 0 y * V (R * y) *
    profilePower (-(β u : ℂ) + (ν u : ℂ) * Complex.I) y
  support u _ D := (W.support u 0 D).filter
    (fun I => V (R * (idealNorm K I / D)) ≠ 0)
  support_spec u _ D I := by
    rw [Finset.mem_filter, W.support_spec]
    constructor
    · rintro ⟨hW, hV⟩
      exact mul_ne_zero (mul_ne_zero hW hV) (profilePower_ne_zero _ _)
    · intro h
      exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul h),
        right_ne_zero_of_mul (left_ne_zero_of_mul h)⟩

def plainTwistTest (W : IdealTest K) (β ν : NonzeroIdeal K → ℝ) : IdealTest K :=
  W.freezeTwist (fun _ => 0) (fun u => -(β u : ℂ) + (ν u : ℂ) * Complex.I)

theorem cutoffTwistTest_local (W : IdealTest K) (V : ℝ → ℂ) (R : ℝ)
    (β ν β' ν' : NonzeroIdeal K → ℝ) (u : NonzeroIdeal K)
    (hβ : β u = β' u) (hν : ν u = ν' u) :
    (cutoffTwistTest K W V R β ν).profile u =
      (cutoffTwistTest K W V R β' ν').profile u ∧
    (cutoffTwistTest K W V R β ν).support u =
      (cutoffTwistTest K W V R β' ν').support u := by
  constructor
  · funext t y
    simp only [cutoffTwistTest, hβ, hν]
  · rfl

variable (c : TargetContext K)

/-- The inverse family's sole scale inputs are U and D.  Its finite
presentation can be decoded from one fixed global coordinate; no selected
slot set, plain scale or subdivision appears in this definition. -/
def detectorInverseFamily
    (presentation : DetectorPresentationFamily K (targetCharacter K c))
    (W₁ : IdealTest K) (V : ℝ → ℂ) (frequencyScale : ℝ)
    (U D : ℝ) (s : SixthUnitClasses K (places K c))
    (ξ : DetectorVector) (σ τ : NonzeroIdeal K → DetectorVector) :
    MomentData K c.family.omega (targetCharacter K c) :=
  sharedMomentData K (places K c) (probeData K c) (momentRowCharacters K c)
    c.family.omega (targetCharacter K c) (presentation.entry (_root_.ExpansionRecipe.decodePresentation
      presentation.count presentation.count_pos (ξ 4)))
    (zeroSlotGeometry K) Fin.elim0 s
    (cutoffTwistTest K W₁ V (D / U ^ (2 * ξ 3)) (fun u => σ u 0) (fun u => frequencyScale * τ u 0))
    (zeroIdealTest K)

/-- This concrete constructor fills every SourceMomentModels data field
from actual tests.  Supplying the actual presentation choices and physical
slot family is still the source-construction problem; no detector, moment,
calibration equality or admissibility proposition is accepted as a field. -/
def detectorSourceRecipe
    (presentation : DetectorPresentationFamily K (targetCharacter K c))
    (W₁ W₂ : IdealTest K) (V : ℝ → ℂ) (frequencyScale : ℝ)
    (physicalSlot : ∀ Z T, SourceMomentIndex K c Z T →
      SixthUnitClasses K (places K c) → DetectorVector →
      Fin c.geometry.slots → PrimeWindow K)
    (slotCoefficient : ∀ Z T, SourceMomentIndex K c Z T →
      SixthUnitClasses K (places K c) → Fin c.geometry.slots → HeckeCharacter K)
    (heights : ∀ Z T, SourceMomentIndex K c Z T → DetectorVector)
    (realShifts imagShifts : ∀ Z T, SourceMomentIndex K c Z T →
      NonzeroIdeal K → DetectorVector) : SourceModelRecipe K c where
  dimension := detectorParameterDimension
  inverseFamily := detectorInverseFamily K c presentation W₁ V frequencyScale
  plainTest _ _ _ _ _ σ τ := plainTwistTest K W₂ (fun u => σ u 0) (fun u => frequencyScale * τ u 0)
  physicalSlot := physicalSlot
  slotCoefficient := slotCoefficient
  heights := heights
  realShifts := realShifts
  imagShifts := imagShifts

theorem detectorInverseFamily_profile
    (presentation : DetectorPresentationFamily K (targetCharacter K c))
    (W₁ : IdealTest K) (V : ℝ → ℂ) (frequencyScale : ℝ)
    (U D : ℝ) (s : SixthUnitClasses K (places K c))
    (ξ : DetectorVector) (σ τ : NonzeroIdeal K → DetectorVector)
    (u : NonzeroIdeal K) (y : ℝ) :
    (detectorInverseFamily K c presentation W₁ V frequencyScale U D s ξ σ τ).inverseTest.profile u 0 y =
      W₁.profile u 0 y * V ((D / U ^ (2 * ξ 3)) * y) *
        profilePower (-(σ u 0 : ℂ) + ((frequencyScale * τ u 0 : ℝ) : ℂ) * Complex.I) y := rfl

theorem detectorInverseFamily_support
    (presentation : DetectorPresentationFamily K (targetCharacter K c))
    (W₁ : IdealTest K) (V : ℝ → ℂ) (frequencyScale : ℝ)
    (U D : ℝ) (s : SixthUnitClasses K (places K c))
    (ξ : DetectorVector) (σ τ : NonzeroIdeal K → DetectorVector)
    (u : NonzeroIdeal K) :
    (detectorInverseFamily K c presentation W₁ V frequencyScale U D s ξ σ τ).inverseTest.support u 0 D =
      (W₁.support u 0 D).filter
        (fun I => V ((D / U ^ (2 * ξ 3)) * (idealNorm K I / D)) ≠ 0) := rfl


/-- Actual bounded encoding of the one common physical point and one finite
presentation.  The cutoff exponent is stored divided by two. -/
def detectorHeights
    (presentation : DetectorPresentationFamily K (targetCharacter K c))
    (physical : Fin 3 → ℝ) (t : ℝ) (index : Fin presentation.count) (T : ℝ) :
    DetectorVector :=
  _root_.ExpansionRecipe.sourceHeightVector physical t
    (_root_.ExpansionRecipe.finitePresentationCode index) T

theorem detectorHeights_norm
    (presentation : DetectorPresentationFamily K (targetCharacter K c))
    (physical : Fin 3 → ℝ) (t : ℝ) (index : Fin presentation.count) (T : ℝ)
    (hT : 1 ≤ T) (hp : ‖physical‖ ≤ T) (ht : 1 ≤ t ∧ t ≤ 3 / 2) :
    ‖detectorHeights K c presentation physical t index T‖ = T := by
  exact _root_.ExpansionRecipe.sourceHeightVector_norm_eq physical t
    (_root_.ExpansionRecipe.finitePresentationCode index) T hT hp ht
    ⟨_root_.ExpansionRecipe.finitePresentationCode_nonneg index,
      (_root_.ExpansionRecipe.finitePresentationCode_lt_one index).le⟩

theorem detectorHeights_cutoff_exponent
    (presentation : DetectorPresentationFamily K (targetCharacter K c))
    (physical : Fin 3 → ℝ) (t : ℝ) (index : Fin presentation.count) (T : ℝ) :
    2 * detectorHeights K c presentation physical t index T 3 = t := by
  dsimp [detectorHeights, _root_.ExpansionRecipe.sourceHeightVector]
  ring

theorem detectorHeights_presentation
    (presentation : DetectorPresentationFamily K (targetCharacter K c))
    (physical : Fin 3 → ℝ) (t : ℝ) (index : Fin presentation.count) (T : ℝ) :
    _root_.ExpansionRecipe.decodePresentation presentation.count presentation.count_pos
      (detectorHeights K c presentation physical t index T 4) = index :=
  _root_.ExpansionRecipe.decodePresentation_code presentation.count presentation.count_pos index


/-- A detector subdivision with no independently assigned polynomial values.
Both tests are generated from the global two-scale family, with the same
stored real and imaginary parameters. -/
def detectorWitnessRecipe (W₁ W₂ : IdealTest K) (V : ℝ → ℂ) (frequencyScale : ℝ)
    (rows : Finset (FrequencyRow K (places K c))) (U t r w : ℝ)
    (σ τ : NonzeroIdeal K → DetectorVector) : WitnessRecipe K (places K c) where
  rows := rows
  inverseLength := r
  plainLength := w
  inverseTest _ := cutoffTwistTest K W₁ V (U ^ r / U ^ t)
    (fun u => σ u 0) (fun u => frequencyScale * τ u 0)
  plainTest _ := plainTwistTest K W₂ (fun u => σ u 0) (fun u => frequencyScale * τ u 0)

/-- The actual paired data, with the independent inverse family unchanged.
The two plain profiles are exactly equal, and the physical geometry is an
ordinary row-independent input at one common Mellin point. -/
def detectorModelData
    (presentation : DetectorPresentationFamily K (targetCharacter K c))
    (W₁ W₂ : IdealTest K) (V : ℝ → ℂ) (frequencyScale U D : ℝ)
    (s : SixthUnitClasses K (places K c))
    (ξ : DetectorVector) (σ τ : NonzeroIdeal K → DetectorVector)
    (g : SlotGeometry K) (coeff : Fin g.slotCount → HeckeCharacter K) :
    MomentData K c.family.omega (targetCharacter K c) :=
  { detectorInverseFamily K c presentation W₁ V frequencyScale U D s ξ σ τ with
    plainTest₁ := plainTwistTest K W₂ (fun u => σ u 0) (fun u => frequencyScale * τ u 0)
    plainTest₂ := plainTwistTest K W₂ (fun u => σ u 0) (fun u => frequencyScale * τ u 0)
    geometry := g
    slotCoefficient := coeff }

/-- Exact local-witness/global-family inverse calibration.  The hypotheses
are only actual data; no polynomial equality or analytic estimate is a
premise of this constructor identity. -/
theorem detectorWitness_inverse_global
    (presentation : DetectorPresentationFamily K (targetCharacter K c))
    (index : Fin presentation.count) (W₁ W₂ : IdealTest K) (V : ℝ → ℂ)
    (frequencyScale : ℝ) (rows : Finset (FrequencyRow K (places K c)))
    (U t r w T : ℝ) (physical : Fin 3 → ℝ)
    (σ τ : NonzeroIdeal K → DetectorVector)
    (g : SlotGeometry K) (coeff : Fin g.slotCount → HeckeCharacter K)
    (u : FrequencyRow K (places K c)) :
    ((detectorWitnessRecipe K c W₁ W₂ V frequencyScale rows U t r w σ τ).toWitness
      (P := probeData K c) (R := momentRowCharacters K c) (ω := c.family.omega)
      (presentation.entry index) g coeff U).inverseValue u =
      inversePolynomial (detectorInverseFamily K c presentation W₁ V frequencyScale
        U (U ^ r) u.sector (detectorHeights K c presentation physical t index T) σ τ)
        u.ideal.val (U ^ r) 0 := by
  dsimp only [detectorWitnessRecipe, WitnessRecipe.toWitness, WitnessRecipe.data,
    detectorInverseFamily]
  rw [detectorHeights_presentation, detectorHeights_cutoff_exponent]
  rfl

/-- Both paired plain factors calibrate to the very same detector plain
witness, while the row-independent geometry may be re-based separately. -/
theorem detectorWitness_plain_global
    (presentation : DetectorPresentationFamily K (targetCharacter K c))
    (index : Fin presentation.count) (W₁ W₂ : IdealTest K) (V : ℝ → ℂ)
    (frequencyScale : ℝ) (rows : Finset (FrequencyRow K (places K c)))
    (U t r w T : ℝ) (physical : Fin 3 → ℝ)
    (σ τ : NonzeroIdeal K → DetectorVector)
    (g : SlotGeometry K) (coeff : Fin g.slotCount → HeckeCharacter K)
    (g' : SlotGeometry K) (coeff' : Fin g'.slotCount → HeckeCharacter K)
    (u : FrequencyRow K (places K c)) :
    let d := detectorModelData K c presentation W₁ W₂ V frequencyScale U (U ^ r)
      u.sector (detectorHeights K c presentation physical t index T) σ τ g' coeff'
    ((detectorWitnessRecipe K c W₁ W₂ V frequencyScale rows U t r w σ τ).toWitness
      (P := probeData K c) (R := momentRowCharacters K c) (ω := c.family.omega)
      (presentation.entry index) g coeff U).plainValue u =
        plainPolynomial d d.plainTest₁ u.ideal.val (U ^ w) 0 ∧
      plainPolynomial d d.plainTest₁ u.ideal.val (U ^ w) 0 =
        plainPolynomial d d.plainTest₂ u.ideal.val (U ^ w) 0 := by
  constructor
  · let value : Fin presentation.count → ℂ := fun j =>
      ((detectorWitnessRecipe K c W₁ W₂ V frequencyScale rows U t r w σ τ).toWitness
        (P := probeData K c) (R := momentRowCharacters K c) (ω := c.family.omega)
        (presentation.entry j) g coeff U).plainValue u
    change value index = value (_root_.ExpansionRecipe.decodePresentation
      presentation.count presentation.count_pos
      (detectorHeights K c presentation physical t index T 4))
    exact congrArg value (detectorHeights_presentation K c presentation physical t index T).symm
  · rfl

/-- All slots read the same three physical coordinates.  No row parameter
map is an argument, and the number of coordinates is independent of J. -/
def commonPhysicalPoint (ξ : DetectorVector) : Fin 3 → ℝ := fun j => ξ ⟨j.val, by
  change j.val < 6
  omega⟩

def detectorPhysicalSlot
    (time : Fin c.geometry.slots → (Fin 3 → ℝ) → ℝ)
    (power : Fin c.geometry.slots → (Fin 3 → ℝ) → ℂ)
    (ξ : DetectorVector) (j : Fin c.geometry.slots) : PrimeWindow K :=
  (analyticMomentPrimeWindow K c.geometry j).freezeTwist
    (time j (commonPhysicalPoint ξ)) (power j (commonPhysicalPoint ξ))

theorem detectorPhysicalSlot_support
    (time : Fin c.geometry.slots → (Fin 3 → ℝ) → ℝ)
    (power : Fin c.geometry.slots → (Fin 3 → ℝ) → ℂ)
    (ξ : DetectorVector) (j : Fin c.geometry.slots) (P₀ t₀ : ℝ) :
    (detectorPhysicalSlot K c time power ξ j).support t₀ P₀ =
      analyticPrimeSupport K (c.geometry.weight j).toFun P₀ := rfl

end HeckeSkeleton.ExpansionRecipe
