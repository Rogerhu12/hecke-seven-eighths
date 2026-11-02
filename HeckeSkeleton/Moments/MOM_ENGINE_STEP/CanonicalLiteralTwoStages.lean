import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralMovingTwist

set_option linter.unusedSectionVars false

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

namespace HeckeSkeleton.Moments.EngineStep

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
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.secondInput_whole
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.secondInput_gaussScale
