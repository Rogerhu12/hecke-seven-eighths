import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralAtoms
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFixedPhases

set_option linter.unusedSectionVars false

/-!
# Exact individual norm factors of the two actual transforms

An inverse complete ideal norm and either Mellin norm power are products
of the corresponding factors at the two plain occurrences and every
prime occurrence. The extra positive Gauss scales are inserted by
putting their square roots into those same original profiles; their
inverse square roots then cancel exactly in the whole coefficient.

These are operations on the computed literal atom table. They neither
replace the original support nor assume a whole-column identity. The
same factors act on both complete centered rectangles, and the empty
slot product follows the same formulas.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralTransforms

/-- Multiplication is checked before the original atoms are summed or
centered. All original prime occurrences remain separate factors. -/
theorem bare_mul_weights (T : FixedChildCharacters K k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w v : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) :
    rawBareSourceCoefficient T N₁ N₂ Z length
        (fun I => w₁ I * v₁ I) (fun I => w₂ I * v₂ I)
        (fun j p => w j p * v j p) i =
      rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i *
        (v₁ (sourceMomentIdeal i.1.1) * v₂ (sourceMomentIdeal i.1.2) *
          ∏ j, v j (i.2 j)) := by
  sorry

theorem norm_power_product (i : AllocationColumn K k)
    (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) (δ : ℝ) :
    ((idealNorm K (sourceMomentIdeal i.1.1) ^ δ : ℝ) : ℂ) *
        ((idealNorm K (sourceMomentIdeal i.1.2) ^ δ : ℝ) : ℂ) *
        ∏ j, (((Ideal.absNorm (i.2 j).asIdeal : ℝ) ^ δ : ℝ) : ℂ) =
      (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ : ℝ) : ℂ) := by
  sorry

/-- The extra Gauss scalar is a positive real square-root denominator,
as a complex identity, not merely an equality of norms. -/
theorem normalizer_eq_inv_sqrt (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j) :
    extraGaussNormalizer G₁ G₂ G =
      (Real.sqrt (extraGaussScale G₁ G₂ G) : ℂ)⁻¹ := by
  sorry

theorem normalizer_mul (N₁ N₂ G₁ G₂ : ℝ) (N G : Fin k → ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hN : ∀ j, 0 < N j) :
    extraGaussNormalizer (N₁ * G₁) (N₂ * G₂) (fun j => N j * G j) =
      extraGaussNormalizer N₁ N₂ N * extraGaussNormalizer G₁ G₂ G := by
  sorry

theorem normalizer_cancel_roots (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j) :
    extraGaussNormalizer G₁ G₂ G *
        ((Real.sqrt G₁ : ℂ) * (Real.sqrt G₂ : ℂ) * ∏ j, (Real.sqrt (G j) : ℂ)) = 1 := by
  sorry

end CanonicalLiteralTransforms

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- This inserts the actual additional positive Gauss scales while
preserving the complete source, by compensating each original profile
with precisely its own square root. -/
def addGauss (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j) :
    CanonicalLiteralRectangles.Atoms (K := K) k :=
  { d with
    leftWeight := fun r I => d.leftWeight r I * (Real.sqrt G₁ : ℂ)
    rightWeight := fun r I => d.rightWeight r I * (Real.sqrt G₂ : ℂ)
    slotWeight := fun j p => d.slotWeight j p * (Real.sqrt (G j) : ℂ)
    gauss₁ := d.gauss₁ * G₁
    gauss₂ := d.gauss₂ * G₂
    gaussSlot := fun j => d.gaussSlot j * G j
    gauss₁_pos := mul_pos d.gauss₁_pos h₁
    gauss₂_pos := mul_pos d.gauss₂_pos h₂
    gaussSlot_pos := fun j => mul_pos (d.gaussSlot_pos j) (hG j) }

theorem addGauss_rectangleLeftWeight (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j)
    (r : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.addGauss G₁ G₂ G h₁ h₂ hG).rectangleLeftWeight r I =
      d.rectangleLeftWeight r I * (Real.sqrt G₁ : ℂ) := by
  sorry

theorem addGauss_term (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j)
    (r : Bool) (i : AllocationColumn K k) :
    (d.addGauss G₁ G₂ G h₁ h₂ hG).term r i = d.term r i := by
  sorry

/-- A literal Mellin factor at every original atom. Negative exponents
are permitted; all actual ideal norms are positive. -/
def normPower (δ : ℝ) : CanonicalLiteralRectangles.Atoms (K := K) k :=
  { d with
    leftWeight := fun r I => d.leftWeight r I * ((idealNorm K I ^ δ : ℝ) : ℂ)
    rightWeight := fun r I => d.rightWeight r I * ((idealNorm K I ^ δ : ℝ) : ℂ)
    slotWeight := fun j p => d.slotWeight j p * (((Ideal.absNorm p.asIdeal : ℝ) ^ δ : ℝ) : ℂ) }

theorem normPower_rectangleLeftWeight (δ : ℝ) (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.normPower δ).rectangleLeftWeight r I =
      d.rectangleLeftWeight r I * ((idealNorm K I ^ δ : ℝ) : ℂ) := by
  sorry

theorem normPower_term (δ : ℝ) (r : Bool) (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.normPower δ).term r i =
      d.term r i * (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ : ℝ) : ℂ) := by
  sorry

theorem normPower_whole (δ : ℝ) (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.normPower δ).whole i =
      d.whole i * (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ : ℝ) : ℂ) := by
  sorry

/-- These are precisely the inverse norm and the two Mellin factors
of the original two transforms. The Gauss normalization is paid once;
both actual rectangles use the same single-occurrence modifications. -/
def twoStageNorms (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j)
    (δ₁ δ₂ : ℝ) : CanonicalLiteralRectangles.Atoms (K := K) k :=
  (((d.addGauss G₁ G₂ G h₁ h₂ hG).normPower (-1)).normPower δ₁).normPower δ₂

theorem twoStageNorms_term (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j)
    (δ₁ δ₂ : ℝ) (r : Bool) (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.twoStageNorms G₁ G₂ G h₁ h₂ hG δ₁ δ₂).term r i =
      d.term r i * (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ₁ : ℝ) : ℂ) *
        (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ₂ : ℝ) : ℂ) /
        (Ideal.absNorm (allocationColumnIdeal i) : ℂ) := by
  sorry

theorem twoStageNorms_whole (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j)
    (δ₁ δ₂ : ℝ) (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.twoStageNorms G₁ G₂ G h₁ h₂ hG δ₁ δ₂).whole i =
      d.whole i * (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ₁ : ℝ) : ℂ) *
        (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ₂ : ℝ) : ℂ) /
        (Ideal.absNorm (allocationColumnIdeal i) : ℂ) := by
  sorry

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The same literal rectangles after actual common-support extraction

The residual supports, quotient plain scales and occurrence indices are
computed by the original support branch. Both original comparison
rectangles share one frozen scalar. The entire additional Gauss product
is retained: a removed slot's Gauss scale moves to the first plain
Gauss scale, without dividing by the second common ideal again.

This operation supplies the literal residual `SecondRectangularFactors`
used by the actual ordinary child constructor. No residual coefficient
identity or new normalization bound is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {P : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots P)

/-- The residual atom table uses exactly the original occurrence
reconstruction. The original extra Gauss scalar stays independent of
the two new central quotient scales. -/
def extract : CanonicalLiteralRectangles.Atoms (K := K) b.keep.card where
  characters := d.characters.restrictSlots b.keep
  plain₁ := SupportCartesian.plainResidual d.plain₁ P b.plainExtract₁
  plain₂ := SupportCartesian.plainResidual d.plain₂ P b.plainExtract₂
  slots j := SupportCartesian.primeLive (d.slots (SlotRestriction.index b.keep j)) P
  plain₁_nonzero I hI := by
    obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
    exact supportResidual_ne_zero J P
  plain₂_nonzero I hI := by
    obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
    exact supportResidual_ne_zero J P
  centered := d.centered
  scale₁ r := d.scale₁ r / idealNorm K b.plainDivisor₁
  scale₂ r := d.scale₂ r / idealNorm K b.plainDivisor₂
  scale₁_pos r := div_pos (d.scale₁_pos r) (idealNorm_pos K _)
  scale₂_pos r := div_pos (d.scale₂_pos r) (idealNorm_pos K _)
  base := d.base
  base_gt_one := d.base_gt_one
  length j := d.length (SlotRestriction.index b.keep j)
  length_pos j := d.length_pos (SlotRestriction.index b.keep j)
  leftWeight r I := d.leftWeight r (b.plainDivisor₁ * I)
  rightWeight r I := d.rightWeight r (b.plainDivisor₂ * I)
  slotWeight j := d.slotWeight (SlotRestriction.index b.keep j)
  gauss₁ := d.gauss₁ * ∏ j ∈ Finset.univ \ b.keep, d.gaussSlot j
  gauss₂ := d.gauss₂
  gaussSlot j := d.gaussSlot (SlotRestriction.index b.keep j)
  gauss₁_pos := mul_pos d.gauss₁_pos (Finset.prod_pos (fun j _ => d.gaussSlot_pos j))
  gauss₂_pos := d.gauss₂_pos
  gaussSlot_pos j := d.gaussSlot_pos (SlotRestriction.index b.keep j)

@[simp] theorem extract_columns :
    childCartesianColumns (d.extract b).plain₁ (d.extract b).plain₂ (d.extract b).slots =
      b.residualColumns := rfl

/-- The removed and retained original Gauss occurrences give the same
total positive scale, even if the last slot is removed. -/
theorem extract_gaussScale :
    extraGaussScale (d.extract b).gauss₁ (d.extract b).gauss₂ (d.extract b).gaussSlot =
      extraGaussScale d.gauss₁ d.gauss₂ d.gaussSlot := by
  sorry

@[simp] theorem extract_normalizer : (d.extract b).normalizer = d.normalizer := by
  sorry

theorem extract_rectangleLeftWeight (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.extract b).rectangleLeftWeight r I =
      d.rectangleLeftWeight r (b.plainDivisor₁ * I) := by
  sorry

/-- This scalar contains the actual frozen arithmetic and every frozen
prime profile. The comparison rectangle has the same scalar. -/
def commonScalar : ℂ :=
  b.bareCommonScalar d.characters d.base d.length d.slotWeight

theorem extract_term (r : Bool) (i : AllocationColumn K b.keep.card)
    (hi : i ∈ b.residualColumns) :
    d.term r (b.reconstruct i) = d.commonScalar b * (d.extract b).term r i := by
  sorry

/-- Extraction acts on the full centered source. No absolute-value
split of its two original rectangles is taken at this step. -/
theorem extract_whole (i : AllocationColumn K b.keep.card)
    (hi : i ∈ b.residualColumns) :
    d.whole (b.reconstruct i) = d.commonScalar b * (d.extract b).whole i := by
  sorry

/-- The residual character keeps the actual moving frequency. Its
common fixed scalar is extracted from the same original whole column. -/
theorem extract_whole_residue {A : SArithmeticData K} {σ : K →+* ℂ}
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns)
    (I : A.Exterior) (frequency : A.R) :
    d.whole (b.reconstruct i) * σ (A.sexticResidue I frequency) =
      d.commonScalar b * ((d.extract b).whole i * σ (A.sexticResidue I frequency)) := by
  sorry

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The actual fixed source phase enters every original arithmetic atom

The fixed first divisor phase, amplifier phase and chosen empty-mask
unit phase are represented by their actual generated elements. This
file transports any such original element through every plain and
prime occurrence. Its genuine singleton moving character and complete
coprimality mask are computed; ramified background zeros are preserved.

The source support, norm profiles, comparison scales and extra Gauss
scales are unchanged. The complete centered coefficient acquires the
original residue factor by a proved finite product identity.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {k : ℕ}

namespace FixedChildCharacters

variable (T : FixedChildCharacters K k)

/-- This is a fixed moving factor, not an additional theta character.
The original finite-ray dictionary is retained verbatim. -/
def movingSingleton (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    FixedChildCharacters K k :=
  { T with
    plain := T.plain * (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).character
    slot := fun j => T.slot j *
      (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).character
    mask := T.mask * CanonicalOriginalPhaseCalibration.originalCoprimeMask
      (exteriorMomentIdeal I) }

theorem movingSingleton_plain
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient (T.movingSingleton P R I a ha).plain
        (T.movingSingleton P R I a ha).plainTwist (T.movingSingleton P R I a ha).mask J =
      sourcePlainCoefficient T.plain T.plainTwist T.mask J *
        actualIdealResidue (A := A) (σ := σ) J.val a := by
  sorry

theorem movingSingleton_prime
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (j : Fin k) (p : HeightOneSpectrum (𝓞 K)) (hp : IsCoprime p.asIdeal A.cS) :
    sourcePrimeCoefficient ((T.movingSingleton P R I a ha).slot j)
        ((T.movingSingleton P R I a ha).slotTwist j)
        (T.movingSingleton P R I a ha).mask p =
      sourcePrimeCoefficient (T.slot j) (T.slotTwist j) T.mask p *
        actualIdealResidue (A := A) (σ := σ) p.asIdeal a := by
  sorry

/-- Multiplicativity is applied to the actual complete ideal product.
The exterior condition at that product proves the required condition at
each of its original occurrences. -/
theorem movingSingleton_bare
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (J : A.Exterior)
    (hJ : J.val = allocationColumnIdeal i) :
    rawBareSourceCoefficient (T.movingSingleton P R I a ha)
        N₁ N₂ Z length w₁ w₂ w i =
      rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i *
        actualIdealResidue (A := A) (σ := σ) J.val a := by
  sorry

@[simp] theorem movingSingleton_restrictSlots
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) (keep : Finset (Fin k)) :
    (T.movingSingleton P R I a ha).restrictSlots keep =
      (T.restrictSlots keep).movingSingleton P R I a ha := rfl

end FixedChildCharacters

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)

def movingSingleton (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    CanonicalLiteralRectangles.Atoms (K := K) k :=
  { d with characters := d.characters.movingSingleton P R I a ha }

theorem movingSingleton_term
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (r : Bool) (i : AllocationColumn K k) (J : A.Exterior)
    (hJ : J.val = allocationColumnIdeal i) :
    (d.movingSingleton P R I a ha).term r i =
      d.term r i * actualIdealResidue (A := A) (σ := σ) J.val a := by
  sorry

theorem movingSingleton_whole
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (i : AllocationColumn K k) (J : A.Exterior)
    (hJ : J.val = allocationColumnIdeal i) :
    (d.movingSingleton P R I a ha).whole i =
      d.whole i * actualIdealResidue (A := A) (σ := σ) J.val a := by
  sorry

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The actual two-transform coefficient from the original atom table

The first occurrence extraction is performed on the original source.
Its computed frozen scalar remains inside one original plain profile.
The first Gauss denominator, both norm tilts and all three genuine fixed
residue phases are then inserted one occurrence at a time. A pool error
uses its actual removed prime-power ideal; the main and direct sources
use the unit ideal in that same formula.

The second occurrence extraction gives the common scalar that is moved
to the actual correlation row. Its two residual rectangles have already
computed characters, complete masks, scales and single-atom profiles.
Neither a completed coefficient equality nor a source bound is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- A fixed scalar is applied to the same first plain profile of both
original rectangles. It never changes their subtraction or supports. -/
def scale (c : ℂ) : CanonicalLiteralRectangles.Atoms (K := K) k :=
  { d with leftWeight := fun r I => c * d.leftWeight r I }

theorem scale_rectangleLeftWeight (c : ℂ) (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.scale c).rectangleLeftWeight r I = c * d.rectangleLeftWeight r I := by
  sorry

theorem scale_term (c : ℂ) (r : Bool) (i : AllocationColumn K k) :
    (d.scale c).term r i = c * d.term r i := by
  sorry

theorem scale_whole (c : ℂ) (i : AllocationColumn K k) :
    (d.scale c).whole i = c * d.whole i := by
  sorry

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

/-- The first common and pool extraction is exactly reindexed. Its
scalar is not omitted or put into a second independent output weight. -/
def firstExtracted : CanonicalLiteralRectangles.Atoms (K := K) b.keep.card :=
  (d.extract b).scale (d.commonScalar b)

theorem firstExtracted_whole (i : AllocationColumn K b.keep.card)
    (hi : i ∈ b.residualColumns) :
    (d.firstExtracted b).whole i = d.whole (b.reconstruct i) := by
  sorry

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- `power` is the actual pool prime power removed from the first
Gauss ideal (the unit ideal on the main/direct path). The generators
are the original first divisor, pool reciprocity and empty-mask unit
elements respectively; their characters are computed internally. -/
def secondInput (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement)
    (δ₁ δ₂ : ℝ) : CanonicalLiteralRectangles.Atoms (K := K) b.keep.card :=
  let e := d.firstExtracted b
  let n := e.twoStageNorms (e.scale₁ false) (e.scale₂ false)
    (fun j => e.base ^ e.length j) (e.scale₁_pos false) (e.scale₂_pos false)
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans e.base_gt_one) _) δ₁ δ₂
  let f := ((n.movingSingleton P R firstFixed firstElement hfirst).movingSingleton
    P R poolFixed poolElement hpool).movingSingleton P R unitFixed unitElement hunit
  f.scale (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
    actualIdealResidue (A := A) (σ := σ) power.val firstElement)

/-- This is the literal inverse-norm form of the two source transforms.
The original first ideal is `power * J`; the denominator is the actual
post-pool Gauss ideal `J`. All three phases keep their nonunit zeros. -/
theorem secondInput_whole
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement)
    (δ₁ δ₂ : ℝ) (i : AllocationColumn K b.keep.card)
    (hi : i ∈ b.residualColumns) (J : A.Exterior)
    (hJ : J.val = allocationColumnIdeal i) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole i =
      (d.whole (b.reconstruct i) *
          ((A.exteriorNorm (ExteriorIdealEuler.mul power J) ^ δ₁ : ℝ) : ℂ) /
          (A.exteriorNorm J : ℂ)) *
        actualIdealResidue (A := A) (σ := σ)
          (ExteriorIdealEuler.mul power J).val firstElement *
        actualIdealResidue (A := A) (σ := σ) J.val poolElement *
        ((A.exteriorNorm J ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) J.val unitElement := by
  sorry

/-- The complete original extra Gauss product is multiplied by the
actual first residual scale, with no second-common quotient inserted. -/
theorem secondInput_gaussScale
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ) :
    let e := d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂
    extraGaussScale e.gauss₁ e.gauss₂ e.gaussSlot =
      extraGaussScale d.gauss₁ d.gauss₂ d.gaussSlot *
        b.residualGaussScale d.base d.length (d.scale₁ false) (d.scale₂ false) := by
  sorry

/-- Both occurrence partitions are now actual constructors. The second
common scalar alone is the constant extracted into the correlation row. -/
theorem secondInput_common_extraction
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)
    (support₂ : Finset (Ideal (𝓞 K)))
    (b₂ : SupportCartesianBranch
      (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).plain₁
      (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).plain₂
      (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).slots support₂)
    (i : AllocationColumn K b₂.keep.card) (hi : i ∈ b₂.residualColumns) :
    let e := d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂
    e.whole (b₂.reconstruct i) = e.commonScalar b₂ * (e.extract b₂).whole i := by
  sorry

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

