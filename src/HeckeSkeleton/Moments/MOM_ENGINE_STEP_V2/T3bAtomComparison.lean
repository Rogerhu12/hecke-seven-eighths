import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryAtomModel
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalBinding

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The two original atom tables form one exceptional comparison

The table's prime atoms, finite phases and extra Gauss factors are
literally shared.  Only the two original plain scales and weights change.
This constructs the comparison from individual atoms on every row,
without any nonexceptional-row restriction.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]

namespace OrdinaryAtomTable

variable {k : ℕ} (d : OrdinaryAtomTable (K := K) k)
variable (phase : PUnit.{1} →* Circle)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))

/-- Both comparison plain atoms are read from the same original table. -/
def t3bComparison : SecondCoefficientComparison (d.dictionary phase S₁ S₂ S false) where
  leftAtom := (d.dictionary phase S₁ S₂ S true).leftAtom
  rightAtom := (d.dictionary phase S₁ S₂ S true).rightAtom
  scale₁ := d.scale₁ true
  scale₂ := d.scale₂ true
  leftWeight := d.comparisonWeight true
  rightWeight := d.rightWeight true
  plain₁ := (d.dictionary phase S₁ S₂ S true).plain₁
  plain₂ := (d.dictionary phase S₁ S₂ S true).plain₂

@[simp] theorem t3bComparison_dictionary :
    (d.t3bComparison phase S₁ S₂ S).dictionary = d.dictionary phase S₁ S₂ S true := rfl

/-- The complete subtraction uses the original common Gauss scalar. -/
theorem t3bComparison_centeredCoefficient (i : AllocationColumn K k) :
    (d.t3bComparison phase S₁ S₂ S).centeredCoefficient
      (Real.sqrt d.gauss₁ : ℂ)⁻¹ (Real.sqrt d.gauss₂ : ℂ)⁻¹
      (fun j => (Real.sqrt (d.gaussSlot j) : ℂ)⁻¹) i = d.whole i := by
  unfold SecondCoefficientComparison.centeredCoefficient
  rw [d.t3bComparison_dictionary]
  simp only [SecondCoefficientTermDictionary.normalizedCoefficient_eq]
  rfl

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The comparison also supplies the existing original-atom frame
interface; its factor identifications hold on the entire Cartesian set. -/
def t3bOriginalComparison (R : ActualSecondCorrelationRows A σ H ι)
    (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
    (h₁ : ∀ I ∈ S₁, I ≠ 0) (h₂ : ∀ I ∈ S₂, I ≠ 0)
    (ideal : AllocationColumn K k → A.Exterior)
    (hideal : ∀ i ∈ childCartesianColumns S₁ S₂ S,
      (ideal i).val = allocationColumnIdeal i)
    (firstSign : ℝ) :
    SecondOriginalComparison
      (d.factors R side χ S₁ S₂ S h₁ h₂ ideal hideal firstSign false) where
  comparison := d.t3bComparison (side.phase PUnit.{1} χ) S₁ S₂ S
  original := CanonicalLiteralTerms.factors d.characters
    (d.scale₁ true) (d.scale₂ true) d.base d.length
    (d.comparisonWeight true) (d.rightWeight true) d.slotWeight
    d.gauss₁ d.gauss₂ d.gaussSlot
  factors := CanonicalLiteralTerms.factorIdentification d.characters
    (side.phase PUnit.{1} χ) S₁ S₂ S
    (d.scale₁ true) (d.scale₂ true) d.base d.length
    (d.comparisonWeight true) (d.rightWeight true) d.slotWeight
    d.gauss₁ d.gauss₂ d.gaussSlot
  gaussScale₁ := d.gauss₁
  gaussScale₂ := d.gauss₂
  gaussScale₁_nonneg := d.gauss₁_pos.le
  leftNormalizer := rfl
  rightNormalizer := rfl
  slotNormalizer := rfl
  plain_product := rfl

theorem t3bOriginalComparison_wholeCoefficient
    (R : ActualSecondCorrelationRows A σ H ι)
    (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
    (h₁ : ∀ I ∈ S₁, I ≠ 0) (h₂ : ∀ I ∈ S₂, I ≠ 0)
    (ideal : AllocationColumn K k → A.Exterior)
    (hideal : ∀ i ∈ childCartesianColumns S₁ S₂ S,
      (ideal i).val = allocationColumnIdeal i)
    (firstSign : ℝ) (i : AllocationColumn K k) :
    (d.t3bOriginalComparison S₁ S₂ S R side χ h₁ h₂ ideal hideal firstSign).wholeCoefficient i =
      d.whole i := by
  change d.term false i -
    (CanonicalLiteralTerms.factors d.characters
      (d.scale₁ true) (d.scale₂ true) d.base d.length
      (d.comparisonWeight true) (d.rightWeight true) d.slotWeight
      d.gauss₁ d.gauss₂ d.gaussSlot).coefficient i = _
  rw [CanonicalLiteralTerms.factors_coefficient]
  rfl

end OrdinaryAtomTable
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryAtomTable.t3bComparison_centeredCoefficient
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryAtomTable.t3bOriginalComparison
