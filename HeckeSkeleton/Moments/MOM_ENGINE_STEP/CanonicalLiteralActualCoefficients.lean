import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSourceCoefficients

/-!
# The actual original parent coefficients in the two-stage atom table

This specializes the chart and pool calculations to the original
parent's computed coefficient and original nonzero-ideal index.  The
only transport inputs identify individual occurrence indices and ideal
products in the actual Cartesian cover.  In particular no complete
coefficient, polynomial, energy or mass identity is an input.

The expression on the right is exactly the input of the second
canonical logarithmic chart, including its own norm tilt and the
chosen inverse empty-mask unit.  Both signs of the first Cauchy source
use the same construction, with the actual corresponding first phase.
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
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z ell eps}
variable {M : Finset (HeightOneSpectrum A.R)} {cutoff : ℝ} {hcutoff : 1 ≤ cutoff}
variable (p : FirstBlockPoolData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns φ
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half) pool M cutoff hcutoff)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)
variable (support : Finset (Ideal (𝓞 K)))
variable (branch : SupportCartesianBranch
  (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
  (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
  (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots support)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)

include hroot hemb

/-- The main left source uses the unit pool power in the same atom
construction.  The actual empty-mask divisor unit remains unchanged. -/
theorem canonicalLeftMain_secondInput
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
  rw [FirstBlockPoolData.canonicalLog_leftDivisorCoefficient hΓ μv ν b C
    raw.exteriorColumns raw.exteriorColumns φ c c finiteTest hlc hcs radius D
    δ₁ hδ₁ hδ₁half p S χ i hi hSi]
  ring

/-- The main right source has the same unit-power specialization and
retains the original right first phase. -/
theorem canonicalRightMain_secondInput
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
  rw [FirstBlockPoolData.canonicalLog_rightDivisorCoefficient hΓ μv ν b C
    raw.exteriorColumns raw.exteriorColumns φ c c finiteTest hlc hcs radius D
    δ₁ hδ₁ hδ₁half p S χ i hi hSi]
  ring

/-- The genuine left error source at the original valuation index is
the computed original atom table.  Both required dictionary identities
are supplied by the actual original-support pool cover. -/
theorem canonicalLeftPool_secondInput
    (q : ExteriorPrime A) (n : ℕ)
    (i : (p.divisorPools.leftData S).valuationColumns q n)
    (j : AllocationColumn K branch.keep.card) (hj : j ∈ branch.residualColumns)
    (hindex : i.val = raw.originalIndex (branch.reconstruct j))
    (hideal : ((p.divisorPools.leftData S).residualPresentation q n i).residual.val =
      allocationColumnIdeal j)
    (hSi : S.val ∣ (p.leftData.ideal i.val).val)
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) :
    (seed.secondInput (σ := σ) branch P R (powerIdeal q n) firstFixed
      (powerIdeal q (2 * n)) (unitExterior A)
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      (generator C q ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
      hfirst (generator_power_generates C q (2 * n))
      CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂).whole j =
      (p.divisorPools.leftData S).residualCoefficient q n
          (p.leftDivisorCoefficient S χ) i *
        ((A.exteriorNorm
          ((p.divisorPools.leftData S).residualPresentation q n i).residual ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ)
          ((p.divisorPools.leftData S).residualPresentation q n i).residual.val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  let J := ((p.divisorPools.leftData S).residualPresentation q n i).residual
  have hold : b.leftResidual i.val = ExteriorIdealEuler.mul (powerIdeal q n) J := by
    apply Subtype.ext
    have he := ((p.divisorPools.leftData S).residualPresentation q n i).reconstructed
    simpa only [p.divisorPools.left_ideal S, p.left_ideal] using he
  rw [Q.literalOriginalAtoms_secondInput_whole ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    support branch hroot hemb (powerIdeal q n) firstFixed (powerIdeal q (2 * n))
    (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q (2 * n))
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂ j hj J hideal,
    ← hindex, ← hold]
  rw [FirstBlockPoolData.canonicalLog_leftResidualCoefficient hΓ μv ν b C
    raw.exteriorColumns raw.exteriorColumns φ c c finiteTest hlc hcs radius D
    δ₁ hδ₁ hδ₁half p S χ q n i hSi]

/-- The genuine right error source uses its original complementary
first phase. The stored second right column is conjugated later by the
same hybrid leaf; no premature conjugation occurs in this identity. -/
theorem canonicalRightPool_secondInput
    (q : ExteriorPrime A) (n : ℕ)
    (i : (p.divisorPools.rightData S).valuationColumns q n)
    (j : AllocationColumn K branch.keep.card) (hj : j ∈ branch.residualColumns)
    (hindex : i.val = raw.originalIndex (branch.reconstruct j))
    (hideal : ((p.divisorPools.rightData S).residualPresentation q n i).residual.val =
      allocationColumnIdeal j)
    (hSi : S.val ∣ (p.rightData.ideal i.val).val)
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) :
    (seed.secondInput (σ := σ) branch P R (powerIdeal q n) firstFixed
      (powerIdeal q (2 * n)) (unitExterior A)
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      (generator C q ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
      hfirst (generator_power_generates C q (2 * n))
      CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂).whole j =
      (p.divisorPools.rightData S).residualCoefficient q n
          (p.rightDivisorCoefficient S χ) i *
        ((A.exteriorNorm
          ((p.divisorPools.rightData S).residualPresentation q n i).residual ^ δ₂ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ)
          ((p.divisorPools.rightData S).residualPresentation q n i).residual.val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  let J := ((p.divisorPools.rightData S).residualPresentation q n i).residual
  have hold : b.rightResidual i.val = ExteriorIdealEuler.mul (powerIdeal q n) J := by
    apply Subtype.ext
    have he := ((p.divisorPools.rightData S).residualPresentation q n i).reconstructed
    simpa only [p.divisorPools.right_ideal S, p.right_ideal] using he
  rw [Q.literalOriginalAtoms_secondInput_whole ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    support branch hroot hemb (powerIdeal q n) firstFixed (powerIdeal q (2 * n))
    (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (generator C q ^ (2 * n)) (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (generator_power_generates C q (2 * n))
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂ j hj J hideal,
    ← hindex, ← hold]
  rw [FirstBlockPoolData.canonicalLog_rightResidualCoefficient hΓ μv ν b C
    raw.exteriorColumns raw.exteriorColumns φ c c finiteTest hlc hcs radius D
    δ₁ hδ₁ hδ₁half p S χ q n i hSi]

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftPool_secondInput
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightPool_secondInput
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftMain_secondInput
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightMain_secondInput
