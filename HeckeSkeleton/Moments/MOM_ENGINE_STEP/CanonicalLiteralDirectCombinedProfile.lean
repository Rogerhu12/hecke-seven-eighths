import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralResidualDirectScalarCost
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstResidualProfileCost

/-!
# The actual first profile and both residual scalars

These estimates concern the original direct, main or valuation source
and two of its actual labels. The scalar pair is proved from the original
individual profile window before combining it with the first Poisson
weight. The mask divisor and active modulus keep their exact norm
identities; the complete pool power remains in each frozen ideal.

The equality specifying `p.weightBound` is metadata of the canonical
first block, and is reflexive for its canonical construction. No scalar
pair bound or estimate for an entire transformed source is an input.
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

namespace CanonicalFirstResidualProfileCost

/-- The two individual residual-scalar bounds retain the full original
negative degree after their square-root costs are multiplied. -/
theorem normPair_le_of_residualBounds
    {Z total δ₁ δ₂ atomCost : ℝ} {left right : ℂ}
    (hZ : 0 < Z) (hcost : 0 ≤ atomCost)
    (hleft : ‖left‖ ≤ Real.sqrt atomCost * Z ^ (total * (-1 / 2 + δ₁ + δ₂)))
    (hright : ‖right‖ ≤ Real.sqrt atomCost * Z ^ (total * (-1 / 2 + δ₁ + δ₂))) :
    ‖left‖ * ‖right‖ ≤ atomCost * Z ^ (-total + 2 * total * (δ₁ + δ₂)) := by
  have h := mul_le_mul hleft hright (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hZ.le _))
  apply h.trans_eq
  calc
    _ = (Real.sqrt atomCost * Real.sqrt atomCost) *
        (Z ^ (total * (-1 / 2 + δ₁ + δ₂)) *
          Z ^ (total * (-1 / 2 + δ₁ + δ₂))) := by ring
    _ = _ := by
      rw [Real.mul_self_sqrt hcost, ← Real.rpow_add hZ]
      congr 2
      ring

end CanonicalFirstResidualProfileCost

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

/-- The original left direct first weight pays the two
actual redistributed scalars with their full negative degree. -/
theorem literalLeftDirectCombinedProfile_le
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (labelL labelR : (p.leftSourceCover raw.originalAtlas S χ).labels)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {bound : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) bound)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hwindow : window ⊆ Set.Iic annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (hweight : p.weightBound = CanonicalFirstLog.rowWeightBound
      (actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity) radius D δ₁)
    (m qLength mask active : ℝ)
    (hradius : radius.val = Z ^ (-m))
    (hmask : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val = Z ^ mask)
    (hactive : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity).modulus,
        (actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity).nonzero⟩).val = Z ^ active) :
    p.weightBound *
      (‖(literalLeftDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ labelL) *
        ((literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
          firstFixed hfirst δ₂ labelL).normProfileFactor δ₁ δ₂ : ℂ)‖ *
        ‖(literalLeftDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ labelR) *
        ((literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
          firstFixed hfirst δ₂ labelR).normProfileFactor δ₁ δ₂ : ℂ)‖) ≤
      (orbitalFieldFactor K * (CanonicalLiteralFirstScalarCost.atomBudget annulus bound) ^ cap) *
        Z ^ ((m + qLength) -
          (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + qLength + mask + active) +
          CanonicalFirstResidualProfileCost.tiltError m
            (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) mask active δ₁ δ₂) := by
  have hL := literalLeftDirectResidualScalar_norm_le
    (profiles := profiles) (hzero := hzero) (ht := ht) (hprime := hprime)
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst annulus hannulus hwindow cap hcap δ₂ hδ₂ hδ labelL
  have hR := literalLeftDirectResidualScalar_norm_le
    (profiles := profiles) (hzero := hzero) (ht := ht) (hprime := hprime)
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst annulus hannulus hwindow cap hcap δ₂ hδ₂ hδ labelR
  have hpair := CanonicalFirstResidualProfileCost.normPair_le_of_residualBounds
    (zero_lt_one.trans hZ) (pow_nonneg
      (zero_le_one.trans (CanonicalLiteralFirstScalarCost.atomBudget_one annulus bound)) cap) hL hR
  rw [hweight]
  exact CanonicalFirstLog.rowWeightBound_mul_scalarPair_le
    (actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity) radius D
    Z m qLength (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) mask active δ₁ δ₂
    ((CanonicalLiteralFirstScalarCost.atomBudget annulus bound) ^ cap) _ _
    (zero_lt_one.trans hZ) hradius hmask hactive hpair

/-- The original right direct first weight pays the two
actual redistributed scalars with their full negative degree. -/
theorem literalRightDirectCombinedProfile_le
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (labelL labelR : (p.rightSourceCover raw.originalAtlas S χ).labels)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {bound : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) bound)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hwindow : window ⊆ Set.Iic annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (hweight : p.weightBound = CanonicalFirstLog.rowWeightBound
      (actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity) radius D δ₁)
    (m qLength mask active : ℝ)
    (hradius : radius.val = Z ^ (-m))
    (hmask : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val = Z ^ mask)
    (hactive : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity).modulus,
        (actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity).nonzero⟩).val = Z ^ active) :
    p.weightBound *
      (‖(literalRightDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ labelL) *
        ((literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
          firstFixed hfirst δ₂ labelL).normProfileFactor δ₁ δ₂ : ℂ)‖ *
        ‖(literalRightDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ labelR) *
        ((literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
          firstFixed hfirst δ₂ labelR).normProfileFactor δ₁ δ₂ : ℂ)‖) ≤
      (orbitalFieldFactor K * (CanonicalLiteralFirstScalarCost.atomBudget annulus bound) ^ cap) *
        Z ^ ((m + qLength) -
          (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + qLength + mask + active) +
          CanonicalFirstResidualProfileCost.tiltError m
            (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) mask active δ₁ δ₂) := by
  have hL := literalRightDirectResidualScalar_norm_le
    (profiles := profiles) (hzero := hzero) (ht := ht) (hprime := hprime)
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst annulus hannulus hwindow cap hcap δ₂ hδ₂ hδ labelL
  have hR := literalRightDirectResidualScalar_norm_le
    (profiles := profiles) (hzero := hzero) (ht := ht) (hprime := hprime)
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst annulus hannulus hwindow cap hcap δ₂ hδ₂ hδ labelR
  have hpair := CanonicalFirstResidualProfileCost.normPair_le_of_residualBounds
    (zero_lt_one.trans hZ) (pow_nonneg
      (zero_le_one.trans (CanonicalLiteralFirstScalarCost.atomBudget_one annulus bound)) cap) hL hR
  rw [hweight]
  exact CanonicalFirstLog.rowWeightBound_mul_scalarPair_le
    (actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity) radius D
    Z m qLength (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) mask active δ₁ δ₂
    ((CanonicalLiteralFirstScalarCost.atomBudget annulus bound) ^ cap) _ _
    (zero_lt_one.trans hZ) hradius hmask hactive hpair

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFirstResidualProfileCost.normPair_le_of_residualBounds
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectCombinedProfile_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightDirectCombinedProfile_le
