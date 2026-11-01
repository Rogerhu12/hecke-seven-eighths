import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralMovingTwist

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
  unfold rectangleLeftWeight scale
  split_ifs <;> simp only [mul_zero]

theorem scale_term (c : ℂ) (r : Bool) (i : AllocationColumn K k) :
    (d.scale c).term r i = c * d.term r i := by
  have hw := funext (d.scale_rectangleLeftWeight c r)
  unfold term
  rw [hw]
  simp only [scale, rawBareSourceCoefficient, FixedChildCharacters.bareCoefficient,
    childCartesianCoefficient, normalizer]
  ring

theorem scale_whole (c : ℂ) (i : AllocationColumn K k) :
    (d.scale c).whole i = c * d.whole i := by
  unfold whole
  rw [d.scale_term c false i, d.scale_term c true i]
  ring

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

/-- The first common and pool extraction is exactly reindexed. Its
scalar is not omitted or put into a second independent output weight. -/
def firstExtracted : CanonicalLiteralRectangles.Atoms (K := K) b.keep.card :=
  (d.extract b).scale (d.commonScalar b)

theorem firstExtracted_whole (i : AllocationColumn K b.keep.card)
    (hi : i ∈ b.residualColumns) :
    (d.firstExtracted b).whole i = d.whole (b.reconstruct i) := by
  rw [firstExtracted, scale_whole, d.extract_whole b i hi]

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
  have hnorm : A.exteriorNorm (ExteriorIdealEuler.mul power J) =
      A.exteriorNorm power * A.exteriorNorm J := by
    change (Ideal.absNorm (power.val * J.val) : ℝ) = _
    rw [map_mul, Nat.cast_mul] <;> rfl
  have hN : (Ideal.absNorm (allocationColumnIdeal i) : ℝ) = A.exteriorNorm J := by
    change _ = (Ideal.absNorm J.val : ℝ)
    rw [hJ]
  have hNc : (Ideal.absNorm (allocationColumnIdeal i) : ℂ) = (A.exteriorNorm J : ℂ) := by
    exact_mod_cast hN
  unfold secondInput
  dsimp only
  rw [scale_whole,
    movingSingleton_whole _ P R hroot hemb unitFixed unitElement hunit i J hJ,
    movingSingleton_whole _ P R hroot hemb poolFixed poolElement hpool i J hJ,
    movingSingleton_whole _ P R hroot hemb firstFixed firstElement hfirst i J hJ,
    twoStageNorms_whole _ _ _ _ _ _ _ δ₁ δ₂ i hi,
    d.firstExtracted_whole b i hi, hN, hNc, hnorm,
    Real.mul_rpow (A.exteriorNorm_pos power).le (A.exteriorNorm_pos J).le]
  change _ = _ * actualIdealResidue (A := A) (σ := σ) (power.val * J.val) firstElement * _ * _ * _
  rw [actualIdealResidue_ideal_mul, Complex.ofReal_mul]
  ring

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
  dsimp only [secondInput, scale, movingSingleton, twoStageNorms, normPower,
    addGauss, firstExtracted]
  have he := d.extract_gaussScale b
  change extraGaussScale
      ((d.extract b).gauss₁ * ((d.extract b).scale₁ false))
      ((d.extract b).gauss₂ * ((d.extract b).scale₂ false))
      (fun j => (d.extract b).gaussSlot j * ((d.extract b).base ^ (d.extract b).length j)) = _
  calc
    _ = extraGaussScale (d.extract b).gauss₁ (d.extract b).gauss₂
          (d.extract b).gaussSlot *
        extraGaussScale ((d.extract b).scale₁ false) ((d.extract b).scale₂ false)
          (fun j => (d.extract b).base ^ (d.extract b).length j) := by
      simp only [extraGaussScale, Finset.prod_mul_distrib]
      ring
    _ = _ := by rw [he] <;> rfl

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
    e.whole (b₂.reconstruct i) = e.commonScalar b₂ * (e.extract b₂).whole i :=
  extract_whole _ b₂ i hi

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.secondInput_whole
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.secondInput_gaussScale
