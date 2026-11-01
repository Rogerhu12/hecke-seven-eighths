import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSourceCoefficients
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSecondStages

/-!
# The original unamplified coefficients in the literal atom table

The direct source, including the zero-slot entrance, uses the very same
original two rectangles and fixed first-divisor phase.  Its pool power
and pool phase are the unit ideal and element.  No prime pool, pool
density or amplified row set appears in this construction.

Both equalities are proved from the actual direct coefficient fields
and the original occurrence index.  The second norm tilt and the
chosen inverse empty-mask unit remain literal.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

local notation "original" => (Q.arithmeticAtoms ξ).constantAtoms W a Z t
local notation "raw" => original.raw Y₁ Y₂
local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
local notation "c" => (original.values Y₁ Y₂).coefficient centered

variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock
  (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).columnExterior
  (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).columnExterior DE)
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
variable (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁half : δ₁ ≤ 1 / 2)
variable {M : Finset (HeightOneSpectrum A.R)} {cutoff : ℝ} {hcutoff : 1 ≤ cutoff}
variable (p : FirstBlockDirectData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns φ
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half) M cutoff hcutoff)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)
variable (support : Finset (Ideal (𝓞 K)))
variable (branch : SupportCartesianBranch
  (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
  (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
  (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots support)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)

include hroot hemb

/-- The direct left source uses the unit pool power in the same atom
construction.  The actual empty-mask divisor unit remains unchanged. -/
theorem canonicalLeftDirect_secondInput
    (i : (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).Column)
    (hi : i ∈ p.leftData.columns)
    (j : AllocationColumn K branch.keep.card) (hj : j ∈ branch.residualColumns)
    (hindex : i = raw.originalIndex (branch.reconstruct j))
    (hideal : (b.leftResidual i).val = allocationColumnIdeal j)
    (hSi : S.val ∣ (p.leftData.ideal i).val)
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) :
    (seed.secondInput (σ := σ) branch P R (unitExterior A) firstFixed
      (unitExterior A) (unitExterior A)
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
      hfirst (unitExterior_generates A)
      CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂).whole j =
      p.leftDivisorCoefficient S χ i *
        ((A.exteriorNorm (b.leftResidual i) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (b.leftResidual i).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  have hunit : ExteriorIdealEuler.mul (unitExterior A) (b.leftResidual i) =
      b.leftResidual i := by
    apply Subtype.ext
    change 1 * (b.leftResidual i).val = _
    exact one_mul _
  rw [Q.literalOriginalAtoms_secondInput_whole ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    support branch hroot hemb (unitExterior A) firstFixed (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂ j hj
    (b.leftResidual i) hideal, ← hindex, hunit,
    actualIdealResidue_frequency_one, mul_one]
  have ha : A.IsAllowed C.correction.B
      (Units.mk0 (b.leftGenerator i : K)
        (by exact_mod_cast (b.left_generates i).1)) := by
    have he := p.leftData.allowed i hi
    simpa only [p.left_generator] using he
  have hχ : (fixedLeftPhase PUnit χ PUnit.unit : ℂ) = 1 := by
    change ((fixedLeftPhase PUnit χ) (1 : PUnit) : ℂ) = 1
    rw [map_one, Circle.coe_one]
  unfold FirstBlockDirectData.leftDivisorCoefficient
  rw [if_pos hSi, hχ, mul_one]
  have he := FirstBlockProfileChart.canonicalLog_leftSourceCoefficient hΓ μv ν b C
    raw.exteriorColumns raw.exteriorColumns φ c c finiteTest hlc hcs radius
    δ₁ hδ₁ hδ₁half D i ha
  change p.originalLeftCoefficient i = _ at he
  rw [he]
  ring

/-- The direct right source has the same unit-power specialization and
retains the original right first phase. -/
theorem canonicalRightDirect_secondInput
    (i : (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).Column)
    (hi : i ∈ p.rightData.columns)
    (j : AllocationColumn K branch.keep.card) (hj : j ∈ branch.residualColumns)
    (hindex : i = raw.originalIndex (branch.reconstruct j))
    (hideal : (b.rightResidual i).val = allocationColumnIdeal j)
    (hSi : S.val ∣ (p.rightData.ideal i).val)
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) :
    (seed.secondInput (σ := σ) branch P R (unitExterior A) firstFixed
      (unitExterior A) (unitExterior A)
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
      hfirst (unitExterior_generates A)
      CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂).whole j =
      p.rightDivisorCoefficient S χ i *
        ((A.exteriorNorm (b.rightResidual i) ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (b.rightResidual i).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  have hunit : ExteriorIdealEuler.mul (unitExterior A) (b.rightResidual i) =
      b.rightResidual i := by
    apply Subtype.ext
    change 1 * (b.rightResidual i).val = _
    exact one_mul _
  rw [Q.literalOriginalAtoms_secondInput_whole ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    support branch hroot hemb (unitExterior A) firstFixed (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂ j hj
    (b.rightResidual i) hideal, ← hindex, hunit,
    actualIdealResidue_frequency_one, mul_one]
  have ha : A.IsAllowed C.correction.B
      (Units.mk0 (b.rightGenerator i : K)
        (by exact_mod_cast (b.right_generates i).1)) := by
    have he := p.rightData.allowed i hi
    simpa only [p.right_generator] using he
  have hχ : (fixedRightPhase PUnit χ PUnit.unit : ℂ) = 1 := by
    change ((fixedRightPhase PUnit χ) (1 : PUnit) : ℂ) = 1
    rw [map_one, Circle.coe_one]
  unfold FirstBlockDirectData.rightDivisorCoefficient
  rw [if_pos hSi, hχ, mul_one]
  have he := FirstBlockProfileChart.canonicalLog_rightSourceCoefficient hΓ μv ν b C
    raw.exteriorColumns raw.exteriorColumns φ c c finiteTest hlc hcs radius
    δ₁ hδ₁ hδ₁half D i ha
  change p.originalRightCoefficient i = _ at he
  rw [he]
  ring

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftDirect_secondInput
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightDirect_secondInput
