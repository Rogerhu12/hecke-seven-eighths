import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectComputedProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFactorFreeProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormFactorTransport

/-!
# Computed profiles for the redistributed actual direct tables

Each constructor starts with the original parent window and the same
first extraction. The positive factor of every retained occurrence is
moved into the original first scalar before normalization. The complete
source is preserved by the proved redistribution identity.

The return value uses the actual atlas, its original full deletion,
the combined original scalar, and the identity plain balance. Every
Schwartz representative and bound is constructed internally. No child
window or whole-source estimate is an input.
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

namespace CanonicalLiteralFullKappaInput.ComputedProfiles

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window : Set ℝ} {s : Finset (ℕ × ℕ)} {B : ℝ}

/-- Transport the already constructed profiles while keeping the
combined scalar equal to the actual destination table's scalar. -/
def onAtlasThenRedistributeScale (c : ℂ) (δ₁ δ₂ : ℝ)
    (T : ComputedProfiles
      ((W.redistributeNormFactors δ₁ δ₂).scale (c * (d.normProfileFactor δ₁ δ₂ : ℂ))⁻¹)
      window s B)
    {A : SArithmeticData K} {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (atlas : SourceCartesianAtlas columns ideal) (count : k = atlas.slotCount) :
    ComputedProfiles
      (((W.onAtlas atlas count).redistributeNormFactors δ₁ δ₂).scale
        (c * ((d.onAtlas atlas count).normProfileFactor δ₁ δ₂ : ℂ))⁻¹) window s B := by
  cases count
  exact (T.onAtlas atlas rfl).reprofile
    (((W.onAtlas atlas rfl).redistributeNormFactors δ₁ δ₂).scale
      (c * ((d.onAtlas atlas rfl).normProfileFactor δ₁ δ₂ : ℂ))⁻¹)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

@[simp] theorem onAtlasThenRedistributeScale_bound (c : ℂ) (δ₁ δ₂ : ℝ)
    (T : ComputedProfiles
      ((W.redistributeNormFactors δ₁ δ₂).scale (c * (d.normProfileFactor δ₁ δ₂ : ℂ))⁻¹)
      window s B)
    {A : SArithmeticData K} {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (atlas : SourceCartesianAtlas columns ideal) (count : k = atlas.slotCount) :
    (onAtlasThenRedistributeScale c δ₁ δ₂ T atlas count).bound = T.bound := by
  cases count
  rfl

def deleteMaskThenRedistributeScale (c : ℂ) (δ₁ δ₂ : ℝ)
    (T : ComputedProfiles
      ((W.redistributeNormFactors δ₁ δ₂).scale (c * (d.normProfileFactor δ₁ δ₂ : ℂ))⁻¹)
      window s B)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ComputedProfiles
      (((W.deleteMask M).redistributeNormFactors δ₁ δ₂).scale
        (c * ((d.deleteMask M).normProfileFactor δ₁ δ₂ : ℂ))⁻¹) window s B :=
  (T.deleteMask M).reprofile
    (((W.deleteMask M).redistributeNormFactors δ₁ δ₂).scale
      (c * ((d.deleteMask M).normProfileFactor δ₁ δ₂ : ℂ))⁻¹)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

@[simp] theorem deleteMaskThenRedistributeScale_bound (c : ℂ) (δ₁ δ₂ : ℝ)
    (T : ComputedProfiles
      ((W.redistributeNormFactors δ₁ δ₂).scale (c * (d.normProfileFactor δ₁ δ₂ : ℂ))⁻¹)
      window s B)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (deleteMaskThenRedistributeScale c δ₁ δ₂ T M).bound = T.bound := rfl

@[simp] theorem balanceOne_bound (T : ComputedProfiles W window s B) :
    T.balanceOne.bound = T.bound := rfl

end CanonicalLiteralFullKappaInput.ComputedProfiles

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
local notation "raw" => (original).raw Y₁ Y₂
local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
local notation "c" => ((original).values Y₁ Y₂).coefficient centered

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

variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (s : Finset (ℕ × ℕ)) (bound : ℝ) (hbound : 0 ≤ bound)
variable (originalWindow : RawProfileWindow rowDomain heightDomain window
  (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)) (data ξ) bound)
variable (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
variable (hcompact : IsCompact window) (hwindow : window ⊆ Set.Ioi 0)
variable (hprime : ∀ j, Function.support (originalWindow.primeRep j t) ⊆ Set.Ioo (1 : ℝ) 2)

/-- All profile data are constructed for this same actual table,
with the complete positive factor charged in its first scalar. -/
def literalLeftDirectFactorFreeComputedProfiles
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.leftSourceCover (raw).originalAtlas S χ).labels) :
    let actual := literalLeftDirectProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href originalWindow hreference ht hwindow
      firstFixed hfirst δ₂ label
    let atoms := literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label
    let scalar := literalLeftDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((((actual.redistributeNormFactors δ₁ δ₂).profiles).scale
        (scalar * (atoms.normProfileFactor δ₁ δ₂ : ℂ))⁻¹).balancePlain (fun _ => 1))
      window s bound := by
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.1 label
  let scalar := literalLeftDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  have hallowed : (data ξ).allowedRow reference :=
    (((data ξ).rows_spec _ reference).mp (Finset.mem_filter.mp href).1).1
  let initial := Q.literalFactorFreeComputedProfiles (σ := σ) ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ reference hallowed s bound hbound originalWindow hreference ht
    hcompact hwindow hprime branch (unitExterior A) firstFixed (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A) CanonicalLiteralFixedPhases.emptyDivisorInverse_generates
    δ₁ δ₂
  have e := literalLeftDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  exact (CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenRedistributeScale
    scalar δ₁ δ₂
    (CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenRedistributeScale
      scalar δ₁ δ₂ initial ((p.leftSourceCover (raw).originalAtlas S χ).branch label) (congrArg Sigma.fst e).symm)
    (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))).balanceOne

/-- The coefficient remains the explicit original seed bound,
before any Fourier variable or child is chosen. -/
theorem literalLeftDirectFactorFreeComputedProfiles_bound
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.leftSourceCover (raw).originalAtlas S χ).labels) :
    (literalLeftDirectFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href s bound hbound originalWindow hreference ht hcompact hwindow hprime
      firstFixed hfirst δ₂ label).bound =
      let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.1 label
      fun r => bound + bound * CanonicalLogProfiles.shapeCoefficient window hcompact hwindow
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s) *
          (1 + CanonicalLiteralBalancedSchwartz.factor seed branch δ₁ δ₂ r) := by
  unfold literalLeftDirectFactorFreeComputedProfiles
  simp only [CanonicalLiteralFullKappaInput.ComputedProfiles.balanceOne_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenRedistributeScale_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenRedistributeScale_bound] <;> rfl

/-- All profile data are constructed for this same actual table,
with the complete positive factor charged in its first scalar. -/
def literalRightDirectFactorFreeComputedProfiles
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.rightSourceCover (raw).originalAtlas S χ).labels) :
    let actual := literalRightDirectProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href originalWindow hreference ht hwindow
      firstFixed hfirst δ₂ label
    let atoms := literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label
    let scalar := literalRightDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((((actual.redistributeNormFactors δ₁ δ₂).profiles).scale
        (scalar * (atoms.normProfileFactor δ₁ δ₂ : ℂ))⁻¹).balancePlain (fun _ => 1))
      window s bound := by
  let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.2 label
  let scalar := literalRightDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  have hallowed : (data ξ).allowedRow reference :=
    (((data ξ).rows_spec _ reference).mp (Finset.mem_filter.mp href).1).1
  let initial := Q.literalFactorFreeComputedProfiles (σ := σ) ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ reference hallowed s bound hbound originalWindow hreference ht
    hcompact hwindow hprime branch (unitExterior A) firstFixed (unitExterior A) (unitExterior A)
    (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    1 (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A))
    hfirst (unitExterior_generates A) CanonicalLiteralFixedPhases.emptyDivisorInverse_generates
    δ₁ δ₂
  have e := literalRightDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ label
  exact (CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenRedistributeScale
    scalar δ₁ δ₂
    (CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenRedistributeScale
      scalar δ₁ δ₂ initial ((p.rightSourceCover (raw).originalAtlas S χ).branch label) (congrArg Sigma.fst e).symm)
    (literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp))).balanceOne

/-- The coefficient remains the explicit original seed bound,
before any Fourier variable or child is chosen. -/
theorem literalRightDirectFactorFreeComputedProfiles_bound
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (label : (p.rightSourceCover (raw).originalAtlas S χ).labels) :
    (literalRightDirectFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      reference href s bound hbound originalWindow hreference ht hcompact hwindow hprime
      firstFixed hfirst δ₂ label).bound =
      let branch := (raw).originalAtlas.branch (primeSupport DE.1) DE.2 label
      fun r => bound + bound * CanonicalLogProfiles.shapeCoefficient window hcompact hwindow
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s) *
          (1 + CanonicalLiteralBalancedSchwartz.factor seed branch δ₁ δ₂ r) := by
  unfold literalRightDirectFactorFreeComputedProfiles
  simp only [CanonicalLiteralFullKappaInput.ComputedProfiles.balanceOne_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.deleteMaskThenRedistributeScale_bound,
    CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenRedistributeScale_bound] <;> rfl

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectFactorFreeComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectFactorFreeComputedProfiles_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightDirectFactorFreeComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightDirectFactorFreeComputedProfiles_bound
