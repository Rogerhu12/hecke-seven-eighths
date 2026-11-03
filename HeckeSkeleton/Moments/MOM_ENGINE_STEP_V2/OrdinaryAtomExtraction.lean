import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryAtomModel

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact extraction with the prescribed unit Gauss normalization

The original common scalar is a finite product of frozen arithmetic
and prime-profile factors. The two comparison rectangles use that same
scalar. The output table has the exact quotient plain scales and the
actual retained occurrence indices.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace OrdinaryAtomTable

variable (d : OrdinaryAtomTable (K := K) k)
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {deletion : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ S deletion)

def commonScalar : ℂ :=
  b.bareCommonScalar d.characters d.base d.length d.slotWeight

/-- The output normalization is fixed to one. The theorem below
retains the input normalizer explicitly, so no scalar is discarded. -/
def unitGaussExtract : OrdinaryAtomTable (K := K) b.keep.card where
  characters := d.characters.restrictSlots b.keep
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
  gauss₁ := 1
  gauss₂ := 1
  gaussSlot _ := 1
  gauss₁_pos := zero_lt_one
  gauss₂_pos := zero_lt_one
  gaussSlot_pos _ := zero_lt_one

@[simp] theorem unitGaussExtract_normalizer :
    (d.unitGaussExtract b).normalizer = 1 := by
  simp [unitGaussExtract, normalizer, extraGaussNormalizer,
    SecondCoefficientTermDictionary.centralNormalizer]

theorem unitGaussExtract_comparisonWeight (r : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.unitGaussExtract b).comparisonWeight r I =
      d.comparisonWeight r (b.plainDivisor₁ * I) := by
  unfold comparisonWeight unitGaussExtract
  split_ifs <;> rfl

theorem unitGaussExtract_term (r : Bool) (i : AllocationColumn K b.keep.card)
    (hi : i ∈ b.residualColumns) :
    d.term r (b.reconstruct i) =
      d.normalizer * d.commonScalar b * (d.unitGaussExtract b).term r i := by
  have he : (d.unitGaussExtract b).term r i =
      b.bareResidualCoefficient d.characters (d.scale₁ r) (d.scale₂ r)
        d.base d.length (d.comparisonWeight r) (d.rightWeight r) d.slotWeight i := by
    rw [term, d.unitGaussExtract_normalizer b, one_mul,
      funext (d.unitGaussExtract_comparisonWeight b r)]
    rfl
  rw [he]
  change d.normalizer * rawBareSourceCoefficient d.characters
    (d.scale₁ r) (d.scale₂ r) d.base d.length
    (d.comparisonWeight r) (d.rightWeight r) d.slotWeight (b.reconstruct i) = _
  rw [b.raw_bare_extract d.characters (d.scale₁ r) (d.scale₂ r) d.base d.length
    (d.comparisonWeight r) (d.rightWeight r) d.slotWeight i hi]
  exact (mul_assoc _ _ _).symm

theorem unitGaussExtract_whole (i : AllocationColumn K b.keep.card)
    (hi : i ∈ b.residualColumns) :
    d.whole (b.reconstruct i) =
      d.normalizer * d.commonScalar b * (d.unitGaussExtract b).whole i := by
  unfold whole
  rw [d.unitGaussExtract_term b false i hi, d.unitGaussExtract_term b true i hi,
    ← mul_sub]

end OrdinaryAtomTable
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryAtomTable.unitGaussExtract_whole
