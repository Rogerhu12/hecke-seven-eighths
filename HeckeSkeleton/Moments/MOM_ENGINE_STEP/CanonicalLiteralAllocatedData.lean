import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPhaseCalibration
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Actual Fourier profiles and parameters of one allocated literal source

The Fourier tests use the pre-allocation plain scales.  The two numeric
plain parameters are logarithms of the actual quotient scales, while
the prime geometry uses the same allocation's retained-slot map.  The
original parent time was already frozen by `ProfileData`, so the new
height is zero.  No arithmetic indicator is inserted into a smooth
profile and no nonnegativity of a quotient logarithm is presumed.

The final data constructor calls the existing appended-child constructor
with these profiles and then restricts that same child by the actual
allocation.  Its arithmetic dictionary is the literal phase calibration
already proved from the original three fixed generated elements.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

section Parameters

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (B : ActualColumnAllocation K k) (rectangle : Bool) (m q κ : ℝ)

/-- The raw quotient logarithms may be negative.  The actual clipping
step subsequently handles that case with its recorded clipping cost. -/
def parameters : RealParameters where
  m := m
  r := 0
  z := ∑ i : Fin B.keep.card, d.length (SlotRestriction.index B.keep i)
  q := q
  n₁ := Real.logb d.base (d.scale₁ rectangle / idealNorm K (B.plainDivisor 0))
  n₂ := Real.logb d.base
    (d.scale₂ rectangle / idealNorm K (B.plainDivisor (Fin.succ 0)))
  κ := κ

theorem left_scale :
    d.base ^ (parameters d B rectangle m q κ).n₁ =
      d.scale₁ rectangle / idealNorm K (B.plainDivisor 0) :=
  Real.rpow_logb (zero_lt_one.trans d.base_gt_one) d.base_gt_one.ne'
    (div_pos (d.scale₁_pos rectangle) (idealNorm_pos K _))

theorem right_scale :
    d.base ^ (parameters d B rectangle m q κ).n₂ =
      d.scale₂ rectangle / idealNorm K (B.plainDivisor (Fin.succ 0)) :=
  Real.rpow_logb (zero_lt_one.trans d.base_gt_one) d.base_gt_one.ne'
    (div_pos (d.scale₂_pos rectangle) (idealNorm_pos K _))

@[simp] theorem slot_sum :
    (parameters d B rectangle m q κ).z =
      ∑ i : Fin B.keep.card, d.length (SlotRestriction.index B.keep i) := rfl

theorem slot_sum_nonneg : 0 ≤ (parameters d B rectangle m q κ).z :=
  Finset.sum_nonneg (fun i _ => (d.length_pos (SlotRestriction.index B.keep i)).le)

@[simp] theorem parameters_width :
    (parameters d B rectangle m q κ).m + (parameters d B rectangle m q κ).q = m + q := rfl

@[simp] theorem parameters_kappa : (parameters d B rectangle m q κ).κ = κ := rfl

end Parameters

/-- The original time is frozen in the literal profile table. -/
def height (_ξ : WithLp 2 (ℝ × ℝ)) : ℝ := 0

section Profiles

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (firstSign : ℝ) (negative : Bool)

def preGeometry (ξ : WithLp 2 (ℝ × ℝ)) : SlotGeometry K where
  slotCount := k
  slots i := W.fourierSlot i firstSign negative ξ

def geometry (ξ : WithLp 2 (ℝ × ℝ)) : SlotGeometry K :=
  (preGeometry W firstSign negative ξ).restrictSlots B.keep

@[simp] theorem preGeometry_count (ξ : WithLp 2 (ℝ × ℝ)) :
    (preGeometry W firstSign negative ξ).slotCount = k := rfl

@[simp] theorem geometry_count (ξ : WithLp 2 (ℝ × ℝ)) :
    (geometry W B firstSign negative ξ).slotCount = B.keep.card := rfl

theorem preGeometry_length (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin k) :
    ((preGeometry W firstSign negative ξ).slots i).length = d.length i :=
  W.fourierSlot_length i firstSign negative ξ

theorem geometry_length (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin B.keep.card) :
    ((geometry W B firstSign negative ξ).slots i).length =
      d.length (SlotRestriction.index B.keep i) :=
  W.fourierSlot_length (SlotRestriction.index B.keep i) firstSign negative ξ

theorem geometry_totalLength (ξ : WithLp 2 (ℝ × ℝ)) :
    (geometry W B firstSign negative ξ).totalLength =
      ∑ i : Fin B.keep.card, d.length (SlotRestriction.index B.keep i) := by
  change (∑ i : Fin B.keep.card,
    (W.fourierSlot (SlotRestriction.index B.keep i) firstSign negative ξ).length) = _
  exact Finset.sum_congr rfl (fun i _ =>
    W.fourierSlot_length (SlotRestriction.index B.keep i) firstSign negative ξ)

/-- The chosen allocation uses the original mesh, through its literal
retained-slot embedding. No coarser mesh is introduced. -/
theorem geometry_fitsMesh (mesh : ℝ)
    (hmesh : ∀ i ∈ B.keep, d.length i ≤ mesh) (ξ : WithLp 2 (ℝ × ℝ)) :
    (geometry W B firstSign negative ξ).fitsMesh mesh := by
  intro i
  rw [geometry_length W B firstSign negative ξ i]
  exact hmesh _ (B.keep.equivFin.symm i).property

theorem geometry_slot_sum (rectangle : Bool) (m q κ : ℝ)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    (parameters d B rectangle m q κ).z =
      (geometry W B firstSign negative ξ).totalLength :=
  (geometry_totalLength W B firstSign negative ξ).symm

/-- The phase contains the original product `B₁ * I`; the Fourier
multiplier has not been incorrectly rescaled to the quotient alone. -/
theorem left_profile (rectangle : Bool) (m q κ : ℝ)
    (ξ : WithLp 2 (ℝ × ℝ)) (u I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    d.rectangleLeftWeight rectangle (B.plainDivisor 0 * I) *
        jointPhase ξ (CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.plain firstSign (B.plainDivisor 0 * I))) =
      (W.fourierLeft rectangle firstSign negative ξ).profile u (height ξ)
        (idealNorm K I / d.base ^ (parameters d B rectangle m q κ).n₁) := by
  rw [left_scale d B rectangle m q κ]
  exact (W.fourierLeft_allocated rectangle firstSign negative ξ u 0
    (B.plainDivisor 0) I).symm

theorem right_profile (rectangle : Bool) (m q κ : ℝ)
    (ξ : WithLp 2 (ℝ × ℝ)) (u I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    d.rightWeight rectangle (B.plainDivisor (Fin.succ 0) * I) *
        jointPhase ξ (CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.plain firstSign (B.plainDivisor (Fin.succ 0) * I))) =
      (W.fourierRight rectangle firstSign negative ξ).profile u (height ξ)
        (idealNorm K I / d.base ^ (parameters d B rectangle m q κ).n₂) := by
  rw [right_scale d B rectangle m q κ]
  exact (W.fourierRight_allocated rectangle firstSign negative ξ u 0
    (B.plainDivisor (Fin.succ 0)) I).symm

theorem slot_profile (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin B.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) :
    d.slotWeight (SlotRestriction.index B.keep i) p *
        jointPhase ξ (CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.prime firstSign (SlotRestriction.index B.keep i) p)) =
      ((geometry W B firstSign negative ξ).slots i).profile (height ξ)
        ((Ideal.absNorm p.asIdeal : ℝ) /
          d.base ^ ((geometry W B firstSign negative ξ).slots i).length) := by
  rw [geometry_length W B firstSign negative ξ i]
  exact (W.fourierSlot_eval (SlotRestriction.index B.keep i) firstSign negative ξ 0 p).symm

end Profiles

section ArithmeticData

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

/-- A literal invocation of the existing child constructor, using
computed Fourier tests, then the original allocation's restriction.
The input is raw parent arithmetic, not a selected calibrated child. -/
def data (ξ : WithLp 2 (ℝ × ℝ)) : MomentData K ω ψ :=
  (CanonicalAppendedPhaseCalibration.childData P R parent (F.moving P R oldMoving)
    correction hcorr C p leftMultiplicity rightMultiplicity pattern ν (remaining * extra)
    (d.base ^ (m + q)) inverse (W.fourierLeft rectangle firstSign negative ξ)
    (W.fourierRight rectangle firstSign negative ξ) (preGeometry W firstSign negative ξ)
    index).restrictSlots B.keep

@[simp] theorem data_count (ξ : WithLp 2 (ℝ × ℝ)) :
    (data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative ξ).geometry.slotCount =
        B.keep.card := rfl

theorem data_lengths (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin B.keep.card) :
    ((data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative ξ).geometry.slots i).length =
        d.length (SlotRestriction.index B.keep i) :=
  geometry_length W B firstSign negative ξ i

/-- The literal frozen profiles themselves construct the norm recipe
on every new allowed row; no row-independence field is requested. -/
def normProfiles : NormProfileRecipe
    (data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative) where
  left ξ _ y := (W.fourierLeft rectangle firstSign negative ξ).profile 1 0 y
  right ξ _ y := (W.fourierRight rectangle firstSign negative ξ).profile 1 0 y
  left_eq ξ u _ time y := W.fourierLeft_frozen rectangle firstSign negative ξ u time y
  right_eq ξ u _ time y := W.fourierRight_frozen rectangle firstSign negative ξ u time y

variable {H : Type*}

/-- The same actual pattern-sector row and allocation provide the
arithmetic fields for the computed Fourier data. -/
def actualDictionary (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : CanonicalOriginalPhaseCalibration.PatternSector P S C pattern ν)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    ((CanonicalLiteralPhaseCalibration.sourceCharacters P R F parent oldMoving correction
      remaining extra index).restrictSlots B.keep).Calibration (σ := σ)
      (data P R W B F parent oldMoving correction hcorr C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern ν remaining extra m q inverse index rectangle firstSign
        negative ξ) rfl (S.extractedRow C row.val.val).momentIdeal (S.factor C row.val.val.val)
      (S.extractedRow C row.val.val).element :=
  CanonicalLiteralPhaseCalibration.actualAllocatedCalibration P R F parent oldMoving correction
    hcorr C pattern ν remaining extra (d.base ^ (m + q)) inverse
    (W.fourierLeft rectangle firstSign negative ξ)
    (W.fourierRight rectangle firstSign negative ξ) (preGeometry W firstSign negative ξ)
    index S B hone hroot hemb row

def actualNegativeDictionary (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : CanonicalOriginalPhaseCalibration.PatternSector P S C pattern ν)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    ((CanonicalLiteralPhaseCalibration.sourceCharacters P R F parent oldMoving correction
      remaining extra index).restrictSlots B.keep).Calibration (σ := σ)
      (data P R W B F parent oldMoving correction hcorr C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern ν remaining extra m q inverse index rectangle firstSign
        negative ξ) rfl (S.extractedRow C row.val.val).momentIdeal (-(S.factor C row.val.val.val))
      (S.extractedRow C row.val.val).element :=
  CanonicalLiteralPhaseCalibration.actualNegativeAllocatedCalibration P R F parent oldMoving
    correction hcorr C pattern ν remaining extra (d.base ^ (m + q)) inverse
    (W.fourierLeft rectangle firstSign negative ξ)
    (W.fourierRight rectangle firstSign negative ξ) (preGeometry W firstSign negative ξ)
    index S B hone hroot hemb row

end ArithmeticData

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.left_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.geometry_fitsMesh
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.left_profile
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.right_profile
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.slot_profile
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.normProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.actualDictionary
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.actualNegativeDictionary
