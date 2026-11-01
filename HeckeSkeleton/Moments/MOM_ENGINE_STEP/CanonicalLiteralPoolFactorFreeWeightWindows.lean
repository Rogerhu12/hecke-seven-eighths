import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolOriginalWeightWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralResidualPoolScalarCost

/-!
# Original windows after exact residual-factor redistribution

The actual table keeps its supports, scales, slot count and complete
Gauss product. Those fields are copied from its original window
certificate. The only changed field, the cost of each prime atom,
is proved for the redistributed profile using the original prime
support in `(1, 2)`. The fixed slot budget remains `max 1 bound^2`.

The complete first frozen ideal, including any valuation power,
is retained before any normalized child is chosen.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
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
variable {floor padding : ℝ}

/-- Original per-occurrence windows for the actual redistributed left
main table, with its full first frozen ideal unchanged. -/
def literalLeftMainFactorFreeOriginalWeightWindows
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (label : (p.leftSourceCovers (raw).originalAtlas S χ).main.labels)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {bound : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) bound)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
    (annulus : ℝ) (hannulus : 1 ≤ annulus)
    (hwindow : ∀ x ∈ window, x ≤ annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding) :
    ((literalLeftMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).redistributeNormFactors δ₁ δ₂).OriginalWeightWindows
        centered cap bound annulus Z
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) DE.1 := by
  let previous := literalLeftMainOriginalWeightWindows
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδ label profiles hzero ht hprime
    annulus hannulus hwindow cap hcap domain
  refine {
    slots := previous.slots
    prime_atoms := ?_
    prime_norm := previous.prime_norm
    present_scale := previous.present_scale
    gauss_lower := previous.gauss_lower }
  intro i prime
  exact (literalLeftMainRedistributedAtoms_primeAtomCost_le
    (profiles := profiles) (hzero := hzero) (ht := ht) (hprime := hprime)
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδ label i prime).trans
      (CanonicalLiteralMassProfilePower.slotBudget_atom bound)

/-- Original per-occurrence windows for the actual redistributed right
main table, with its full first frozen ideal unchanged. -/
def literalRightMainFactorFreeOriginalWeightWindows
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (label : (p.rightSourceCovers (raw).originalAtlas S χ).main.labels)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {bound : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) bound)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
    (annulus : ℝ) (hannulus : 1 ≤ annulus)
    (hwindow : ∀ x ∈ window, x ≤ annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding) :
    ((literalRightMainAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ label).redistributeNormFactors δ₁ δ₂).OriginalWeightWindows
        centered cap bound annulus Z
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) DE.2 := by
  let previous := literalRightMainOriginalWeightWindows
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδ label profiles hzero ht hprime
    annulus hannulus hwindow cap hcap domain
  refine {
    slots := previous.slots
    prime_atoms := ?_
    prime_norm := previous.prime_norm
    present_scale := previous.present_scale
    gauss_lower := previous.gauss_lower }
  intro i prime
  exact (literalRightMainRedistributedAtoms_primeAtomCost_le
    (profiles := profiles) (hzero := hzero) (ht := ht) (hprime := hprime)
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδ label i prime).trans
      (CanonicalLiteralMassProfilePower.slotBudget_atom bound)

/-- Original per-occurrence windows for the actual redistributed left
pool table, with its full first frozen ideal unchanged. -/
def literalLeftPoolFactorFreeOriginalWeightWindows
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (q : pool.primes) (n : ℕ)
    (label : ((p.leftSourceCovers (raw).originalAtlas S χ).residual q n).labels)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {bound : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) bound)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
    (annulus : ℝ) (hannulus : 1 ≤ annulus)
    (hwindow : ∀ x ∈ window, x ≤ annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding) :
    ((literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ q n label).redistributeNormFactors δ₁ δ₂).OriginalWeightWindows
        centered cap bound annulus Z
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) (DE.1 * q.val.val.asIdeal ^ n) := by
  let previous := literalLeftPoolOriginalWeightWindows
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδ q n label profiles hzero ht hprime
    annulus hannulus hwindow cap hcap domain
  refine {
    slots := previous.slots
    prime_atoms := ?_
    prime_norm := previous.prime_norm
    present_scale := previous.present_scale
    gauss_lower := previous.gauss_lower }
  intro i prime
  exact (literalLeftPoolRedistributedAtoms_primeAtomCost_le
    (profiles := profiles) (hzero := hzero) (ht := ht) (hprime := hprime)
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδ q n label i prime).trans
      (CanonicalLiteralMassProfilePower.slotBudget_atom bound)

/-- Original per-occurrence windows for the actual redistributed right
pool table, with its full first frozen ideal unchanged. -/
def literalRightPoolFactorFreeOriginalWeightWindows
    (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes
        b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (δ₂ : ℝ) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (q : pool.primes) (n : ℕ)
    (label : ((p.rightSourceCovers (raw).originalAtlas S χ).residual q n).labels)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {bound : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) bound)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
    (annulus : ℝ) (hannulus : 1 ≤ annulus)
    (hwindow : ∀ x ∈ window, x ≤ annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding) :
    ((literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
      firstFixed hfirst δ₂ q n label).redistributeNormFactors δ₁ δ₂).OriginalWeightWindows
        centered cap bound annulus Z
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) (DE.2 * q.val.val.asIdeal ^ n) := by
  let previous := literalRightPoolOriginalWeightWindows
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδ q n label profiles hzero ht hprime
    annulus hannulus hwindow cap hcap domain
  refine {
    slots := previous.slots
    prime_atoms := ?_
    prime_norm := previous.prime_norm
    present_scale := previous.present_scale
    gauss_lower := previous.gauss_lower }
  intro i prime
  exact (literalRightPoolRedistributedAtoms_primeAtomCost_le
    (profiles := profiles) (hzero := hzero) (ht := ht) (hprime := hprime)
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδ q n label i prime).trans
      (CanonicalLiteralMassProfilePower.slotBudget_atom bound)

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftMainFactorFreeOriginalWeightWindows
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightMainFactorFreeOriginalWeightWindows
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolFactorFreeOriginalWeightWindows
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolFactorFreeOriginalWeightWindows
