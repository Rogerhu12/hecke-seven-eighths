import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingOriginalArithmeticAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOriginalAtlas
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondFactorHybridBridge
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonCoefficientExtraction

/-!
# Literal original atoms give the two rectangular term dictionaries

The finite reciprocity group of the actual canonical source is `PUnit`.
Its phase is consequently one at every actual phase label.  The two
plain atoms and every prime atom below are computed from their original
characters, complete coprimality mask, norm profiles and central scales.
No whole-column identity or completed coefficient dictionary is supplied.

The last section applies the construction to the actual moving-row
arithmetic atoms.  Their old moving character stays in the background
coefficient, and the old full mask is retained.  The computed original
Cartesian reindex has exactly these rectangular coefficients.  Common
support extraction then uses the same two quotient scales and the same
frozen scalar for both rectangles, including when there are no slots.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralTerms

variable {k : ℕ}

/-- Every actual canonical finite phase, not just a selected phase. -/
@[simp] theorem phase_unit (phase : PUnit.{1} →* Circle) :
    (phase PUnit.unit : ℂ) = 1 := by
  change (phase 1 : ℂ) = 1
  rw [map_one, Circle.coe_one]

/-- The source atom is evaluated on the original nonzero ideal.
The total extension at zero is never used on an actual Cartesian plain
support; it agrees with the convention already used by the allocator. -/
def plainAtom (T : FixedChildCharacters K k) (N : ℝ)
    (w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  (Real.sqrt N : ℂ)⁻¹ *
    (sourcePlainCoefficient T.plain T.plainTwist T.mask (sourceMomentIdeal I) *
      w (sourceMomentIdeal I))

def primeAtom (T : FixedChildCharacters K k) (Z : ℝ) (length : Fin k → ℝ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : Fin k) (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (Real.sqrt (Z ^ length i) : ℂ)⁻¹ *
    (sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask p * w i p)

/-- A genuine single-term dictionary is constructed from the original
arithmetic and profile factors.  Neither a coefficient identity nor a
polynomial identity is an input. -/
def dictionary (T : FixedChildCharacters K k) (phase : PUnit.{1} →* Circle)
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ) :
    SecondCoefficientTermDictionary T phase S₁ S₂ S where
  leftAtom := plainAtom T N₁ w₁
  rightAtom := plainAtom T N₂ w₂
  slotAtom := primeAtom T Z length w
  leftRay _ := PUnit.unit
  rightRay _ := PUnit.unit
  slotRay _ _ := PUnit.unit
  scale₁ := N₁
  scale₂ := N₂
  base := Z
  length := length
  leftWeight := w₁
  rightWeight := w₂
  slotWeight := w
  plain₁ I _ := by simp only [phase_unit, mul_one] <;> rfl
  plain₂ I _ := by simp only [phase_unit, mul_one] <;> rfl
  prime i p _ := by simp only [phase_unit, mul_one] <;> rfl

@[simp] theorem dictionary_coefficient
    (T : FixedChildCharacters K k) (phase : PUnit.{1} →* Circle)
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) :
    (dictionary T phase S₁ S₂ S N₁ N₂ Z length w₁ w₂ w).coefficient i =
      rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i := rfl

@[simp] theorem dictionary_ray
    (T : FixedChildCharacters K k) (phase : PUnit.{1} →* Circle)
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) :
    (dictionary T phase S₁ S₂ S N₁ N₂ Z length w₁ w₂ w).ray i = PUnit.unit :=
  Subsingleton.elim _ _

/-- The extra original Gauss normalizations are independent of the
central normalizations already present in each original atom. -/
def factors (T : FixedChildCharacters K k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (G₁ G₂ : ℝ) (G : Fin k → ℝ) : SecondColumnFactors K PUnit.{1} k where
  leftAtom := plainAtom T N₁ w₁
  rightAtom := plainAtom T N₂ w₂
  slotAtom := primeAtom T Z length w
  leftRay _ := PUnit.unit
  rightRay _ := PUnit.unit
  slotRay _ _ := PUnit.unit
  leftNormalizer := (Real.sqrt G₁ : ℂ)⁻¹
  rightNormalizer := (Real.sqrt G₂ : ℂ)⁻¹
  slotNormalizer i := (Real.sqrt (G i) : ℂ)⁻¹

def factorIdentification
    (T : FixedChildCharacters K k) (phase : PUnit.{1} →* Circle)
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (G₁ G₂ : ℝ) (G : Fin k → ℝ) :
    (dictionary T phase S₁ S₂ S N₁ N₂ Z length w₁ w₂ w).FactorIdentification
      (factors T N₁ N₂ Z length w₁ w₂ w G₁ G₂ G) where
  left_atom _ _ := rfl
  right_atom _ _ := rfl
  slot_atom _ _ _ := rfl
  left_ray _ _ := rfl
  right_ray _ _ := rfl
  slot_ray _ _ _ := rfl

/-- The literal factor table retains the exact extra Gauss scalar once. -/
theorem factors_coefficient
    (T : FixedChildCharacters K k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (G₁ G₂ : ℝ) (G : Fin k → ℝ) (i : AllocationColumn K k) :
    (factors T N₁ N₂ Z length w₁ w₂ w G₁ G₂ G).coefficient i =
      extraGaussNormalizer G₁ G₂ G *
        rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i := by
  simp only [factors, SecondColumnFactors.coefficient, plainAtom, primeAtom,
    rawBareSourceCoefficient, FixedChildCharacters.bareCoefficient,
    childCartesianCoefficient, Finset.prod_mul_distrib, extraGaussNormalizer,
    SecondCoefficientTermDictionary.centralNormalizer]
  ring

section Extraction

variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ S P)

/-- Computed residual dictionary on the actual occurrence-support
branch.  The two quotient scales and every retained slot index are the
ones used by the original Cartesian reconstruction. -/
def residualDictionary
    (T : FixedChildCharacters K k) (phase : PUnit.{1} →* Circle)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ) :
    SecondCoefficientTermDictionary (T.restrictSlots b.keep) phase
      (SupportCartesian.plainResidual S₁ P b.plainExtract₁)
      (SupportCartesian.plainResidual S₂ P b.plainExtract₂)
      (fun j => SupportCartesian.primeLive (S (SlotRestriction.index b.keep j)) P) :=
  dictionary (T.restrictSlots b.keep) phase _ _ _
    (N₁ / idealNorm K b.plainDivisor₁) (N₂ / idealNorm K b.plainDivisor₂)
    Z (fun i => length (SlotRestriction.index b.keep i))
    (fun I => w₁ (b.plainDivisor₁ * I)) (fun I => w₂ (b.plainDivisor₂ * I))
    (fun i => w (SlotRestriction.index b.keep i))

/-- This is the actual original coefficient, evaluated at the genuine
reconstructed tuple, not an arbitrary complete-polynomial hypothesis. -/
theorem reconstructed_coefficient
    (T : FixedChildCharacters K k) (phase : PUnit.{1} →* Circle)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w (b.reconstruct i) =
      b.bareCommonScalar T Z length w *
        (residualDictionary b T phase N₁ N₂ Z length w₁ w₂ w).coefficient i :=
  b.raw_bare_extract T N₁ N₂ Z length w₁ w₂ w i hi

/-- One common scalar transports both literal rectangles.  Their
comparison scales remain independent and the prime product stays
inside the complete subtraction. -/
theorem reconstructed_centered_coefficient
    (T : FixedChildCharacters K k) (phase : PUnit.{1} →* Circle)
    (centered : Bool) (X₁ X₂ Y₁ Y₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    (rawBareSourceCoefficient T X₁ X₂ Z length w₁ w₂ w (b.reconstruct i) -
      if centered then rawBareSourceCoefficient T Y₁ Y₂ Z length v₁ v₂ w (b.reconstruct i)
        else 0) =
      b.bareCommonScalar T Z length w *
        ((residualDictionary b T phase X₁ X₂ Z length w₁ w₂ w).coefficient i -
          if centered then (residualDictionary b T phase Y₁ Y₂ Z length v₁ v₂ w).coefficient i
            else 0) := by
  have hx := reconstructed_coefficient b T phase X₁ X₂ Z length w₁ w₂ w i hi
  have hy := reconstructed_coefficient b T phase Y₁ Y₂ Z length v₁ v₂ w i hi
  cases centered <;>
    simp only [Bool.false_eq_true, if_false, if_true, sub_zero, hx, hy, mul_sub]

end Extraction
end CanonicalLiteralTerms

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The characters of the literal original row-independent atoms.
The fixed moving factor is not spuriously required to belong to theta. -/
def literalSourceCharacters (ξ : X) : FixedChildCharacters K (data ξ).geometry.slotCount :=
  CanonicalOriginalPhaseCalibration.sourceCharacters (data ξ)
    (Q.correction * Q.moving.character) Q.arithmeticMask id

theorem arithmeticAtoms_literal_plain (ξ : X) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (Q.arithmeticAtoms ξ).leftArithmetic I =
      sourcePlainCoefficient (Q.literalSourceCharacters ξ).plain
        (Q.literalSourceCharacters ξ).plainTwist (Q.literalSourceCharacters ξ).mask I := by
  simp only [arithmeticAtoms, completeIdealFixedTwistArithmeticAtoms,
    literalSourceCharacters, CanonicalOriginalPhaseCalibration.sourceCharacters,
    sourcePlainCoefficient, CanonicalOriginalPhaseCalibration.coefficient_one,
    mul_one, CanonicalOriginalPhaseCalibration.originalCoprimeMask]

theorem arithmeticAtoms_literal_right (ξ : X) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (Q.arithmeticAtoms ξ).rightArithmetic I =
      sourcePlainCoefficient (Q.literalSourceCharacters ξ).plain
        (Q.literalSourceCharacters ξ).plainTwist (Q.literalSourceCharacters ξ).mask I :=
  Q.arithmeticAtoms_literal_plain ξ I

theorem arithmeticAtoms_literal_prime (ξ : X) (i : Fin (data ξ).geometry.slotCount)
    (p : HeightOneSpectrum (𝓞 K)) :
    (Q.arithmeticAtoms ξ).primeArithmetic i p =
      sourcePrimeCoefficient ((Q.literalSourceCharacters ξ).slot i)
        ((Q.literalSourceCharacters ξ).slotTwist i) (Q.literalSourceCharacters ξ).mask p := by
  simp only [arithmeticAtoms, completeIdealFixedTwistArithmeticAtoms,
    literalSourceCharacters, CanonicalOriginalPhaseCalibration.sourceCharacters,
    sourcePrimeCoefficient, primeCoefficient_one, mul_one,
    CanonicalOriginalPhaseCalibration.originalCoprimeMask, id_eq]

/-- Both plain scales and all original prime profiles are read from the
same actual constant-atom source. -/
def literalOriginalDictionary (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (comparison : Bool)
    (phase : PUnit.{1} →* Circle) :
    let raw := ((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂
    SecondCoefficientTermDictionary (Q.literalSourceCharacters ξ) phase
      raw.originalPlain₁ raw.originalPlain₂ raw.exteriorSlots :=
  CanonicalLiteralTerms.dictionary (Q.literalSourceCharacters ξ) phase _ _ _
    (if comparison then Y₁ else Z ^ a.n₁) (if comparison then Y₂ else Z ^ a.n₂)
    Z (fun i => ((data ξ).geometry.slots i).length)
    (fun I => W.left PUnit.unit t (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁)))
    (fun I => W.right PUnit.unit t (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂)))
    (fun i p => ((data ξ).geometry.slots i).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots i).length))

/-- This identity has no support or nonemptiness premise: the original
index changes only the two nonzero-ideal proofs, keeping every slot. -/
theorem literalOriginalDictionary_rectangle (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (comparison : Bool)
    (phase : PUnit.{1} →* Circle)
    (i : AllocationColumn K (data ξ).geometry.slotCount) :
    let atoms := (Q.arithmeticAtoms ξ).constantAtoms W a Z t
    (atoms.values Y₁ Y₂).rectangle comparison ((atoms.raw Y₁ Y₂).originalIndex i) =
      (Q.literalOriginalDictionary ξ W a Z t Y₁ Y₂ comparison phase).coefficient i := by
  dsimp only
  simp only [ParentRawAtoms.ConstantValues.rectangle, ParentConstantAtoms.values,
    ParentRawAtoms.originalIndex, ParentConstantAtoms.leftValue, ParentConstantAtoms.rightValue,
    ParentConstantAtoms.primeValue, ParentArithmeticAtoms.constantAtoms,
    Q.arithmeticAtoms_literal_plain, Q.arithmeticAtoms_literal_right,
    Q.arithmeticAtoms_literal_prime]
  rfl

/-- The whole centered original coefficient is identified only after
both individual atom dictionaries have been computed. -/
theorem literalOriginalDictionary_centered (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (phase : PUnit.{1} →* Circle)
    (i : AllocationColumn K (data ξ).geometry.slotCount) :
    let atoms := (Q.arithmeticAtoms ξ).constantAtoms W a Z t
    (atoms.values Y₁ Y₂).coefficient centered ((atoms.raw Y₁ Y₂).originalIndex i) =
      (Q.literalOriginalDictionary ξ W a Z t Y₁ Y₂ false phase).coefficient i -
        if centered then (Q.literalOriginalDictionary ξ W a Z t Y₁ Y₂ true phase).coefficient i
          else 0 := by
  dsimp only
  unfold ParentRawAtoms.ConstantValues.coefficient
  rw [Q.literalOriginalDictionary_rectangle, Q.literalOriginalDictionary_rectangle]

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralTerms.dictionary
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralTerms.reconstructed_centered_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalDictionary_rectangle
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalDictionary_centered
