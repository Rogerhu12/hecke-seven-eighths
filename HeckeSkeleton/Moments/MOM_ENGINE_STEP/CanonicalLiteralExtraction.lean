import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralTransforms

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

namespace HeckeSkeleton.Moments.EngineStep

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
  have hsplit : (∏ j, d.gaussSlot j) =
      (∏ j ∈ Finset.univ \ b.keep, d.gaussSlot j) *
        ∏ j, d.gaussSlot (SlotRestriction.index b.keep j) := by
    simpa only [Finset.sdiff_eq_filter, Finset.mem_univ, true_and] using
      (SlotRestriction.product_extend b.keep (fun _ => PUnit.unit)
        (fun _ => PUnit.unit) (fun j _ => d.gaussSlot j))
  change (d.gauss₁ * ∏ j ∈ Finset.univ \ b.keep, d.gaussSlot j) * d.gauss₂ *
      (∏ j, d.gaussSlot (SlotRestriction.index b.keep j)) =
    d.gauss₁ * d.gauss₂ * ∏ j, d.gaussSlot j
  rw [hsplit]
  ring

@[simp] theorem extract_normalizer : (d.extract b).normalizer = d.normalizer := by
  unfold normalizer
  rw [CanonicalLiteralTransforms.normalizer_eq_inv_sqrt _ _ _
      (d.extract b).gauss₁_pos (d.extract b).gauss₂_pos (d.extract b).gaussSlot_pos,
    CanonicalLiteralTransforms.normalizer_eq_inv_sqrt _ _ _
      d.gauss₁_pos d.gauss₂_pos d.gaussSlot_pos,
    d.extract_gaussScale b]

theorem extract_rectangleLeftWeight (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.extract b).rectangleLeftWeight r I =
      d.rectangleLeftWeight r (b.plainDivisor₁ * I) := by
  unfold rectangleLeftWeight extract
  split_ifs <;> rfl

/-- This scalar contains the actual frozen arithmetic and every frozen
prime profile. The comparison rectangle has the same scalar. -/
def commonScalar : ℂ :=
  b.bareCommonScalar d.characters d.base d.length d.slotWeight

theorem extract_term (r : Bool) (i : AllocationColumn K b.keep.card)
    (hi : i ∈ b.residualColumns) :
    d.term r (b.reconstruct i) = d.commonScalar b * (d.extract b).term r i := by
  have hres : (d.extract b).term r i =
      d.normalizer * b.bareResidualCoefficient d.characters (d.scale₁ r) (d.scale₂ r)
        d.base d.length (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight i := by
    rw [term, d.extract_normalizer b,
      funext (d.extract_rectangleLeftWeight b r)]
    rfl
  rw [hres]
  change d.normalizer * rawBareSourceCoefficient d.characters
      (d.scale₁ r) (d.scale₂ r) d.base d.length
      (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight (b.reconstruct i) = _
  rw [b.raw_bare_extract d.characters (d.scale₁ r) (d.scale₂ r) d.base d.length
    (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight i hi]
  unfold commonScalar
  ring

/-- Extraction acts on the full centered source. No absolute-value
split of its two original rectangles is taken at this step. -/
theorem extract_whole (i : AllocationColumn K b.keep.card)
    (hi : i ∈ b.residualColumns) :
    d.whole (b.reconstruct i) = d.commonScalar b * (d.extract b).whole i := by
  unfold whole
  rw [d.extract_term b false i hi, d.extract_term b true i hi]
  ring

/-- The residual character keeps the actual moving frequency. Its
common fixed scalar is extracted from the same original whole column. -/
theorem extract_whole_residue {A : SArithmeticData K} {σ : K →+* ℂ}
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns)
    (I : A.Exterior) (frequency : A.R) :
    d.whole (b.reconstruct i) * σ (A.sexticResidue I frequency) =
      d.commonScalar b * ((d.extract b).whole i * σ (A.sexticResidue I frequency)) := by
  rw [d.extract_whole b i hi]
  ring

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.extract_gaussScale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.extract_whole
