import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralTerms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralLocations

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# One table for the original two comparison rectangles

The table records individual occurrences, before a Cartesian carrier is
chosen. A support extraction changes the two plain scales and retains
the named original slot occurrences. The ordinary factor constructor
then uses this same table on the actual leaf carrier. No coefficient or
polynomial identity is a field of this table.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]

/-- The two comparison profiles share every prime occurrence and every
extra Gauss factor. The absent comparison has the literal zero first
plain weight. -/
structure OrdinaryAtomTable (k : ℕ) where
  characters : FixedChildCharacters K k
  centered : Bool
  scale₁ : Bool → ℝ
  scale₂ : Bool → ℝ
  scale₁_pos : ∀ r, 0 < scale₁ r
  scale₂_pos : ∀ r, 0 < scale₂ r
  base : ℝ
  base_gt_one : 1 < base
  length : Fin k → ℝ
  length_pos : ∀ j, 0 < length j
  leftWeight : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  rightWeight : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  slotWeight : Fin k → HeightOneSpectrum (𝓞 K) → ℂ
  gauss₁ : ℝ
  gauss₂ : ℝ
  gaussSlot : Fin k → ℝ
  gauss₁_pos : 0 < gauss₁
  gauss₂_pos : 0 < gauss₂
  gaussSlot_pos : ∀ j, 0 < gaussSlot j

namespace OrdinaryAtomTable

variable {k : ℕ} (d : OrdinaryAtomTable (K := K) k)

def comparisonWeight (r : Bool) : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ :=
  if r && !d.centered then fun _ => 0 else d.leftWeight r

def dictionary (phase : PUnit.{1} →* Circle)
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K))) (r : Bool) :
    SecondCoefficientTermDictionary d.characters phase S₁ S₂ S :=
  CanonicalLiteralTerms.dictionary d.characters phase S₁ S₂ S
    (d.scale₁ r) (d.scale₂ r) d.base d.length
    (d.comparisonWeight r) (d.rightWeight r) d.slotWeight

def normalizer : ℂ := extraGaussNormalizer d.gauss₁ d.gauss₂ d.gaussSlot

def term (r : Bool) (i : AllocationColumn K k) : ℂ :=
  d.normalizer * rawBareSourceCoefficient d.characters (d.scale₁ r) (d.scale₂ r)
    d.base d.length (d.comparisonWeight r) (d.rightWeight r) d.slotWeight i

def whole (i : AllocationColumn K k) : ℂ := d.term false i - d.term true i

theorem term_false (i : AllocationColumn K k) :
    d.term false i = d.normalizer * rawBareSourceCoefficient d.characters
      (d.scale₁ false) (d.scale₂ false) d.base d.length
      (d.leftWeight false) (d.rightWeight false) d.slotWeight i := by
  simp only [term, comparisonWeight, Bool.false_and, Bool.false_eq_true, if_false]

theorem term_true (i : AllocationColumn K k) :
    d.term true i = if d.centered then d.normalizer *
      rawBareSourceCoefficient d.characters (d.scale₁ true) (d.scale₂ true)
        d.base d.length (d.leftWeight true) (d.rightWeight true) d.slotWeight i else 0 := by
  cases hc : d.centered <;>
    simp [term, comparisonWeight, hc, rawBareSourceCoefficient,
      FixedChildCharacters.bareCoefficient, childCartesianCoefficient]

theorem whole_eq (i : AllocationColumn K k) :
    d.whole i = d.normalizer *
      (rawBareSourceCoefficient d.characters (d.scale₁ false) (d.scale₂ false)
          d.base d.length (d.leftWeight false) (d.rightWeight false) d.slotWeight i -
        if d.centered then rawBareSourceCoefficient d.characters
          (d.scale₁ true) (d.scale₂ true) d.base d.length
          (d.leftWeight true) (d.rightWeight true) d.slotWeight i else 0) := by
  rw [whole, d.term_false, d.term_true]
  cases d.centered <;>
    simp only [Bool.false_eq_true, if_false, if_true, sub_zero, mul_zero, mul_sub]

/-- A fixed original common scalar stays in the same plain occurrence
of both rectangles. -/
def scale (z : ℂ) : OrdinaryAtomTable (K := K) k :=
  { d with leftWeight := fun r I => z * d.leftWeight r I }

theorem scale_comparisonWeight (z : ℂ) (r : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.scale z).comparisonWeight r I = z * d.comparisonWeight r I := by
  unfold comparisonWeight scale
  split_ifs <;> simp only [mul_zero]

theorem scale_term (z : ℂ) (r : Bool) (i : AllocationColumn K k) :
    (d.scale z).term r i = z * d.term r i := by
  have hw := funext (d.scale_comparisonWeight z r)
  unfold term
  rw [hw]
  simp only [scale, rawBareSourceCoefficient, FixedChildCharacters.bareCoefficient,
    childCartesianCoefficient, normalizer]
  ring

theorem scale_whole (z : ℂ) (i : AllocationColumn K k) :
    (d.scale z).whole i = z * d.whole i := by
  rw [whole, d.scale_term z false i, d.scale_term z true i]
  exact (mul_sub z _ _).symm

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual Fourier locations are the individual residual log
norms, with the original first-transform sign. -/
def factors (R : ActualSecondCorrelationRows A σ H ι)
    (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (h₁ : ∀ I ∈ S₁, I ≠ 0) (h₂ : ∀ I ∈ S₂, I ≠ 0)
    (ideal : AllocationColumn K k → A.Exterior)
    (hideal : ∀ i ∈ childCartesianColumns S₁ S₂ S,
      (ideal i).val = allocationColumnIdeal i)
    (firstSign : ℝ) (r : Bool) :
    SecondRectangularFactors R PUnit.{1} side S₁ S₂ S ideal (fun _ => PUnit.unit)
      (d.term r)
      (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
        (CanonicalLiteralLocations.plain firstSign) (CanonicalLiteralLocations.prime firstSign)) χ where
  characters := d.characters
  dictionary := d.dictionary (side.phase PUnit.{1} χ) S₁ S₂ S r
  base_gt_one := d.base_gt_one
  length_pos := d.length_pos
  plain₁_nonzero := h₁
  plain₂_nonzero := h₂
  ideal_product := hideal
  gaussScale₁ := d.gauss₁
  gaussScale₂ := d.gauss₂
  gaussSlotScale := d.gaussSlot
  gaussScale₁_pos := d.gauss₁_pos
  gaussScale₂_pos := d.gauss₂_pos
  gaussSlotScale_pos := d.gaussSlot_pos
  coefficient_factor i _ := by
    rw [SecondCoefficientTermDictionary.normalizedCoefficient_eq]
    rfl
  ray_factor _ _ := Subsingleton.elim _ _
  leftLocation _ := CanonicalLiteralLocations.plain firstSign
  rightLocation _ := CanonicalLiteralLocations.plain firstSign
  slotLocation _ := CanonicalLiteralLocations.prime firstSign
  point_factor _ _ _ _ := rfl

end OrdinaryAtomTable
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryAtomTable.whole_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryAtomTable.scale_whole
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryAtomTable.factors
