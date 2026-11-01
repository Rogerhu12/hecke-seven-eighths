import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectAtomCosts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormFactorTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralResidualScalarCost
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFactorFreeAtomCosts

/-!
# Sharp residual scalar costs on the actual direct tables

Each scalar is computed on the same first-extracted table used by the
actual source. The complete residual scale factor is taken before the
second common extraction. Original individual profile windows prove
the estimate, including the full frozen ideal and any actual pool power.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum
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

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {bound : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) bound)
variable (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)

variable (hprime : ∀ j, Function.support (profiles.primeRep j t) ⊆ Set.Ioo (1 : ℝ) 2)

include profiles hzero ht hprime

/-- The complete actual first scalar includes the residual profile
factor once. Its decay is the original total degree, with only the
explicit pair of fixed Mellin tilts left over. -/
theorem literalLeftDirectResidualScalar_norm_le
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hwindow : window ⊆ Set.Iic annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (δ₂ : ℝ) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (label : (p.leftSourceCover raw.originalAtlas S χ).labels) :
    ‖(literalLeftDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label) *
      ((literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).normProfileFactor δ₁ δ₂ : ℂ)‖ ≤
      Real.sqrt ((CanonicalLiteralFirstScalarCost.atomBudget annulus bound) ^ cap) *
        Z ^ ((a.n₁ + a.n₂ + (data ξ).geometry.totalLength) * (-1 / 2 + δ₁ + δ₂)) := by
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.1 label
  let I := primePowerProduct b.primes b.leftMultiplicity
  have hfrozen : frozenSourceIdeal branch.plainDivisor₁ branch.plainDivisor₂
      branch.keep branch.witness.2 = I.val :=
    (branch.frozenSourceIdeal_eq.trans
      (raw.originalAtlas.branch_product (primeSupport DE.1) DE.1 label)).trans
        b.common_left.symm
  have hfactor : (literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).normProfileFactor δ₁ δ₂ =
      seed.twoStageProfileFactor branch δ₁ δ₂ := by
    simp only [literalLeftDirectAtoms, CanonicalLiteralRectangles.Atoms.normProfileFactor,
      CanonicalLiteralRectangles.Atoms.deleteMask_scaleProduct,
      CanonicalLiteralRectangles.Atoms.onAtlas_scaleProduct,
      CanonicalLiteralRectangles.Atoms.secondInput_scaleProduct,
      CanonicalLiteralRectangles.Atoms.twoStageProfileFactor, branch]
  have hbound := Q.literalOriginalAtoms_residualScalar_norm_le ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    C profiles hzero ht hprime annulus hannulus hwindow cap hcap branch I (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    δ₁ δ₂ hδ₁.le hδ₂ hδ hfrozen (by change (1 : Ideal (𝓞 K)) ∣ I.val; exact one_dvd _)
  rw [hfactor]
  calc
    _ = ‖(seed.twoStageProfileFactor branch δ₁ δ₂ : ℂ) *
      (literalLeftDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label)‖ := congrArg norm (mul_comm _ _)
    _ ≤ _ := hbound

/-- The complete actual first scalar includes the residual profile
factor once. Its decay is the original total degree, with only the
explicit pair of fixed Mellin tilts left over. -/
theorem literalRightDirectResidualScalar_norm_le
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hwindow : window ⊆ Set.Iic annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (δ₂ : ℝ) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (label : (p.rightSourceCover raw.originalAtlas S χ).labels) :
    ‖(literalRightDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label) *
      ((literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).normProfileFactor δ₁ δ₂ : ℂ)‖ ≤
      Real.sqrt ((CanonicalLiteralFirstScalarCost.atomBudget annulus bound) ^ cap) *
        Z ^ ((a.n₁ + a.n₂ + (data ξ).geometry.totalLength) * (-1 / 2 + δ₁ + δ₂)) := by
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.2 label
  let I := primePowerProduct b.primes b.rightMultiplicity
  have hfrozen : frozenSourceIdeal branch.plainDivisor₁ branch.plainDivisor₂
      branch.keep branch.witness.2 = I.val :=
    (branch.frozenSourceIdeal_eq.trans
      (raw.originalAtlas.branch_product (primeSupport DE.1) DE.2 label)).trans
        b.common_right.symm
  have hfactor : (literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).normProfileFactor δ₁ δ₂ =
      seed.twoStageProfileFactor branch δ₁ δ₂ := by
    simp only [literalRightDirectAtoms, CanonicalLiteralRectangles.Atoms.normProfileFactor,
      CanonicalLiteralRectangles.Atoms.deleteMask_scaleProduct,
      CanonicalLiteralRectangles.Atoms.onAtlas_scaleProduct,
      CanonicalLiteralRectangles.Atoms.secondInput_scaleProduct,
      CanonicalLiteralRectangles.Atoms.twoStageProfileFactor, branch]
  have hbound := Q.literalOriginalAtoms_residualScalar_norm_le ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    C profiles hzero ht hprime annulus hannulus hwindow cap hcap branch I (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    δ₁ δ₂ hδ₁.le hδ₂ hδ hfrozen (by change (1 : Ideal (𝓞 K)) ∣ I.val; exact one_dvd _)
  rw [hfactor]
  calc
    _ = ‖(seed.twoStageProfileFactor branch δ₁ δ₂ : ℂ) *
      (literalRightDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label)‖ := congrArg norm (mul_comm _ _)
    _ ≤ _ := hbound

/-- The actual redistributed table retains the original squared
profile budget for every common and allocation occurrence. -/
theorem literalLeftDirectRedistributedAtoms_primeAtomCost_le
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (label : (p.leftSourceCover raw.originalAtlas S χ).labels)
    (i : Fin ((p.leftSourceCover raw.originalAtlas S χ).branch label).slotCount)
    (prime : HeightOneSpectrum (𝓞 K)) :
    ((literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).redistributeNormFactors δ₁ δ₂).primeAtomCost i prime ≤ bound ^ 2 := by
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.1 label
  let T := (p.leftSourceCover raw.originalAtlas S χ).branch label
  have e := literalLeftDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  let input := seed.secondInput (σ := σ) branch P R (unitExterior A) firstFixed
    (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  change ((input.onAtlas T (congrArg Sigma.fst e).symm).redistributeNormFactors
    δ₁ δ₂).primeAtomCost i prime ≤ bound ^ 2
  rw [← CanonicalLiteralRectangles.Atoms.redistributeNormFactors_onAtlas,
    CanonicalLiteralRectangles.Atoms.primeAtomCost_onAtlas,
    CanonicalLiteralRectangles.Atoms.secondInput_redistributeNormFactors]
  exact Q.literalOriginalAtoms_redistributedSecondInput_primeAtomCost_le ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ profiles hzero ht hprime branch (unitExterior A) firstFixed
    (unitExterior A) (unitExterior A) _ 1 _ hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂ hδ _ prime

/-- The actual redistributed table retains the original squared
profile budget for every common and allocation occurrence. -/
theorem literalRightDirectRedistributedAtoms_primeAtomCost_le
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (label : (p.rightSourceCover raw.originalAtlas S χ).labels)
    (i : Fin ((p.rightSourceCover raw.originalAtlas S χ).branch label).slotCount)
    (prime : HeightOneSpectrum (𝓞 K)) :
    ((literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).redistributeNormFactors δ₁ δ₂).primeAtomCost i prime ≤ bound ^ 2 := by
  let branch := raw.originalAtlas.branch (primeSupport DE.1) DE.2 label
  let T := (p.rightSourceCover raw.originalAtlas S χ).branch label
  have e := literalRightDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  let input := seed.secondInput (σ := σ) branch P R (unitExterior A) firstFixed
    (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂
  change ((input.onAtlas T (congrArg Sigma.fst e).symm).redistributeNormFactors
    δ₁ δ₂).primeAtomCost i prime ≤ bound ^ 2
  rw [← CanonicalLiteralRectangles.Atoms.redistributeNormFactors_onAtlas,
    CanonicalLiteralRectangles.Atoms.primeAtomCost_onAtlas,
    CanonicalLiteralRectangles.Atoms.secondInput_redistributeNormFactors]
  exact Q.literalOriginalAtoms_redistributedSecondInput_primeAtomCost_le ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ profiles hzero ht hprime branch (unitExterior A) firstFixed
    (unitExterior A) (unitExterior A) _ 1 _ hfirst (unitExterior_generates A)
    CanonicalLiteralFixedPhases.emptyDivisorInverse_generates δ₁ δ₂ hδ _ prime

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectResidualScalar_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightDirectResidualScalar_norm_le

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectRedistributedAtoms_primeAtomCost_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightDirectRedistributedAtoms_primeAtomCost_le
