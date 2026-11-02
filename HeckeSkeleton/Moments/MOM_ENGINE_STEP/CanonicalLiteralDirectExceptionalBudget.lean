import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectExceptionalBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalCommonBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualPredicates
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalOrdinaryMagnitude
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalFirstSupport

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# The actual left direct exceptional leaf from original inputs

The original first common block fixes the direct geometry. The same
first atlas and second allocation construct its exceptional sides.
The live original fibre proves the row-profile window; its unchanged
common extraction proves both original scalar factors are nonzero.
All atom, profile, support and row-mass conclusions are constructed
before the fixed-character primitive is applied.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum CommonSupportMass

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
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable (step supportError : ℝ) (hsupportError : 0 ≤ supportError)
local notation "first" => OriginalNominalGeometry.canonicalDirect
  (a := a) (Z := Z) (step := step) (b.literalLeftCoordinates D)
    supportError (zero_lt_one.trans hZ) hsupportError
local notation "retainedScale" => (first).retainedScale
local notation "g" => (first).enlargement
local notation "hscale" => (first).retainedScale_pos
variable (cutoff₂ : ℝ) (hcutoff₂ : 1 ≤ cutoff₂)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)


variable (hδsum : δ₁ + δ₂ ≤ 1 / 2)
variable (lo hi : ℝ) (hlo : 0 < lo)
variable (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive ψ (data ξ).theta
  (Set.Icc lo hi))
variable (ε widthMax columnLoss cutoffExponent : ℝ) (hε : 0 < ε)
variable (hwidthMax : 0 ≤ widthMax) (hcolumnLoss : 0 ≤ columnLoss)
variable (hcutoffExponent : 0 ≤ cutoffExponent)
local notation "maskExponent" => CanonicalLiteralExceptionalPhysicalBox.maskExponent
  widthMax columnLoss cutoffExponent
local notation "hmaskExponent" => CanonicalLiteralExceptionalPhysicalBox.maskExponent_nonneg
  hwidthMax hcolumnLoss hcutoffExponent
local notation "orders" => CanonicalLiteralExceptionalUnifiedChoice.orders
  (A := A) (σ := σ) (η := η) (hS := htrace) primitive ε maskExponent hε hmaskExponent
local notation "heightOrder" => CanonicalLiteralExceptionalUnifiedChoice.heightOrder
  (A := A) (σ := σ) (η := η) (hS := htrace) primitive ε maskExponent hε hmaskExponent
variable (originalBound annulus : ℝ) (hamplitude : 1 ≤ originalBound) (hannulus : 1 ≤ annulus)
local notation "horiginalBound" => zero_le_one.trans hamplitude
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
variable (originalWindow : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi)
  (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
  (data ξ) originalBound)
variable (hreference : reference ∈ rowDomain) (htime : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (originalWindow.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable (hupper : hi ≤ annulus) (hlower : annulus⁻¹ ≤ lo)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)

section LeftDirectExceptionalBudget

variable (hnorm : ∀ h ∈ p.leftData.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool p.leftData.columns p.leftData.columns
  (fun i => (p.leftData.ideal i).val) (fun i => (p.leftData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool p.leftData.columns p.leftData.columns
  (fun i => (p.leftData.ideal i).val) (fun i => (p.leftData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (p.leftSourceCover (raw).originalAtlas S χ)
local notation "firstPoint" => (fun i => -Real.log (A.exteriorNorm (b.leftResidual i)))

local notation "firstFixed" => b.literalLeftFixed D
local notation "hfirst" => b.literalLeftFixed_generates C D
local notation "fixedPhases" => CanonicalLiteralActualCharacters.unamplifiedPhases
  firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity
    b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst

variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
local notation "exceptional" => (stage).supported.gated.literalHybridPredicates
  cover cover P R fixedPhases Q.moving Q.correction (data ξ).theta
variable (F : SchwartzMap ℝ ℂ)
variable (j : v.AllocationKey)

local notation "oldLeftAtoms" => literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.1
local notation "oldRightAtoms" => literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.2.1
local notation "oldLeftScalar" => literalLeftDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.1
local notation "oldRightScalar" => literalLeftDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.2.1
local notation "leftAtoms" => (oldLeftAtoms).redistributeNormFactors δ₁ δ₂
local notation "rightAtoms" => (oldRightAtoms).redistributeNormFactors δ₁ δ₂
local notation "leftScalar" => oldLeftScalar * ((oldLeftAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => oldRightScalar * ((oldRightAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "leftBalance" => (fun _ : Bool => (1 : ℝ))
local notation "rightBalance" => (fun _ : Bool => (1 : ℝ))
local notation "extra" => literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp)
local notation "source" => p.leftData.directSource (p.leftDivisorCoefficient S χ)
local notation "secondPattern" => v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel
local notation "secondSector" => v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel

variable (hS : Squarefree S.val)
variable (hfiber : ((stage).supported.gated.fiberCoveredLeaf cover cover exceptional F
  firstPoint ⟨v, j⟩).Live)
local notation "hlive" => (v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hfiber

local notation "construction" => literalLeftDirectExceptionalExtraction
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (hroot := hroot) (hemb := hemb) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    («retainedScale» := retainedScale) («g» := g) («hscale» := hscale)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := dimension) (width := width)
    (domain := domain) (hnorm := hnorm) (character := character) (dyad := dyad)
    (v := v) («exceptional» := exceptional) (F := F) («firstFixed» := firstFixed)
    («hfirst» := hfirst) (j := j) (hS := hS) («hlive» := hlive)
local notation "sides" => literalLeftDirectExceptionalSides
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (reference := reference) (href := href) («orders» := orders)
    (amplitude := originalBound) (hamplitude := horiginalBound)
    (originalWindow := originalWindow) (hreference := hreference) (ht := htime)
    (hcompact := isCompact_Icc) (hpositive := fun _ hy => lt_of_lt_of_le hlo hy.1)
    (hprime := hprime) (v := v) («exceptional» := exceptional) (kernel := F)
    (j := j) («hlive» := hlive) («firstFixed» := firstFixed) («hfirst» := hfirst)

local notation "rawRows" => v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel
local notation "characters" => (rawRows).literalFiniteCharacters C P R fixedPhases
  Q.moving Q.correction secondPattern secondSector (data ξ).theta
variable (thetaPair : (data ξ).theta × (data ξ).theta)
local notation "hpredicate" =>
  (show (v.leaf exceptional F firstPoint j).exceptional = (characters).exceptional from rfl)
local notation "classRows" =>
  (v.literalSupportedRows leftAtoms rightAtoms).restrictRows ((characters).thetaClass thetaPair)
local notation "branchL" => (raw).originalAtlas.branch (primeSupport DE.1) DE.1 v.2.2.1
local notation "branchR" => (raw).originalAtlas.branch (primeSupport DE.1) DE.1 v.2.2.2.1
local notation "dictionaryL" => literalLeftDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
  hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.1
local notation "dictionaryR" => literalLeftDirectCover_dictionary hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered
  hZ hY₁ hY₂ b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.2.1
local notation "maskL" => CanonicalLiteralExceptionalCommonBudget.placedAtoms_mask (σ := σ)
  Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ fixedPhases (unitExterior A) δ₁ δ₂ extra
    branchL v.literalLeftParent (congrArg Sigma.fst dictionaryL).symm
local notation "maskR" => CanonicalLiteralExceptionalCommonBudget.placedAtoms_mask (σ := σ)
  Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ fixedPhases (unitExterior A) δ₁ δ₂ extra
    branchR v.literalRightParent (congrArg Sigma.fst dictionaryR).symm
local notation "commonL" => v.literalLeftCommonAtoms leftAtoms maskL
local notation "commonR" => v.literalRightCommonAtoms rightAtoms maskR
local notation "hclass" => ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_nonunitLabelStable
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half source retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad v.1 v.2.1
local notation "hsector" => ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_sectorLabelStable
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half source retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad v.1 v.2.1
local notation "hrow" => ActualGaussStage.canonicalSector_fiberLeaf_rowProfile_one
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half source retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad cover cover exceptional F firstPoint ⟨v,j⟩ hfiber
local notation "factoryRows" => CanonicalLiteralExceptionalFactory.rows v.chart P R
  cutoff₂ hcutoff₂ v.rowLabel fixedPhases (data ξ) Q.moving Q.correction commonL commonR thetaPair
local notation "factoryMass" => CanonicalLiteralExceptionalArithmetic.actualMass v.chart P R hclass
  cutoff₂ hcutoff₂ v.rowLabel fixedPhases (data ξ) Q.moving Q.correction commonL commonR thetaPair
  (v.literalLeftCommonAtoms_ideal leftAtoms maskL) (v.literalRightCommonAtoms_ideal rightAtoms maskR)
    1 (by norm_num) hrow
local notation "secondGeometry" => CanonicalLiteralExceptionalNumbers.geometry v.chart
  cutoff₂ hcutoff₂ v.rowLabel first
local notation "firstTotal" => (first).skeleton.A + ((first).skeleton.q + (first).skeleton.R + (first).skeleton.E)
local notation "normalization" => firstLeftAllowance Z firstTotal (first).ideals.first.val (first).ideals.opposite.val
local notation "outer" => (construction).val.stripOuter leftScalar rightScalar
  (construction).property.2.1 (construction).property.2.2
local notation "magnitude" z => ((outer).thetaClassLeaf characters thetaPair).exceptionalIntegrand z

variable (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (slotLoss loss : ℝ) (hslotLossNonneg : 0 ≤ slotLoss) (hloss : 0 ≤ loss)
variable (hslotLoss : annulus ≤ Z ^ (2 * slotLoss))
variable (hslots : (cap : ℝ) * slotLoss ≤ loss / 16)
variable (hstep : 0 ≤ step) (hq : 0 ≤ a.q)
variable (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta)
variable (hplaces : CanonicalLiteralExceptionalArithmetic.thetaBadPrimes (data ξ).theta ⊆ A.Sf)
variable (hwidth : a.m + a.q ≤ widthMax)
variable (hthreshold : max 2 (Ideal.absNorm A.cS : ℝ) ≤ Z)
variable (hsupport : supportError ≤ loss / 16) (hvolume : ε ≤ loss / 16)
variable (hcutoffPaid : CanonicalLiteralExceptionalGeometry.paidCutoff columnLoss cutoffExponent 0 / 6 ≤ loss / 16)
variable (hcutoffPower : cutoff₂ ≤ Z ^ cutoffExponent)
variable (hactiveColumns : ∀ i ∈ (source).columns, (source).coefficient i ≠ 0 →
  A.exteriorNorm ((source).ideal i) ≤ Z ^
    ((first).skeleton.A - (first).skeleton.c - (first).skeleton.w + columnLoss))
variable (hDE : DE ∈ commonSupportPool (raw).exteriorColumns (raw).exteriorColumns
  (fun i => ((raw).columnExterior i).val) (fun i => ((raw).columnExterior i).val))
variable (horiginalColumns : ∀ i ∈ (raw).exteriorColumns,
  A.exteriorNorm ((raw).columnExterior i) ≤ Z ^ widthMax)
variable (holdOriginal : A.exteriorNorm (Q.moving.effectiveFullSupport Q.remaining) ≤ Z ^ a.q)

local notation "fixedCoefficient" => CanonicalLiteralExceptionalSourceBudget.coefficient
  (A := A) (σ := σ) (η := η) (hS := htrace) primitive ε widthMax columnLoss cutoffExponent
    hε hwidthMax hcolumnLoss hcutoffExponent δ₁ δ₂ annulus cap
local notation "profileDegree" => CanonicalLiteralExceptionalSourceBudget.profileDegree cap
local notation "commonDegree" => CanonicalLiteralExceptionalAtomBudget.commonDegree cap
local notation "radical" => (Ideal.absNorm (commonRadical
  (primePowerProduct v.block.primes v.block.leftMultiplicity).val
  (primePowerProduct v.block.primes v.block.rightMultiplicity).val) : ℝ)


include href hlo domain hS hfiber originalWindow hreference htime hprime hupper hlower
  hamplitude hannulus hcap hδsum hslotLossNonneg hloss hslotLoss hslots hstep hq hone hplaces
  hroot hemb hwidth hthreshold hsupport hvolume hcutoffPaid hcutoffPower hactiveColumns
  hDE horiginalColumns holdOriginal in
/-- The same stored left-direct theta leaf is bounded using only its
original atom window, original physical windows, and the fixed-character
single-ideal primitive. All actual row and common-atom estimates are
constructed internally; the original profile exponent is explicit. -/
theorem literalLeftDirectExceptional_pointwise
    (hcentered : centered = true) (hpadding : 0 ≤ padding) (z : ℝ × ℝ) :
    magnitude z / normalization ≤
      (annulus ^ cap * orbitalFieldFactor K * (Γ.index : ℝ) * fixedCoefficient) *
        originalBound ^ (profileDegree + commonDegree) *
        (1 + fourierHeight (WithLp.toLp 2 z)) ^ heightOrder *
        Z ^ (padding + 3 * step + loss / 2) / radical *
        Z ^ (-idealLogLength Z j.1.val) := by
  sorry

include href hlo domain hS hfiber originalWindow hreference htime hprime hupper hlower
  hamplitude hannulus hcap hδsum hslotLossNonneg hloss hslotLoss hslots hstep hq hone hplaces
  hroot hemb hsupport hcutoffPaid hcutoffPower hactiveColumns in
/-- The same stored left-direct theta leaf is bounded using only its
original atom window, original physical windows, and the fixed-character
single-ideal primitive. All actual row and common-atom estimates are
constructed internally; the original profile exponent is explicit. -/
theorem literalLeftDirectOrdinaryExceptional_pointwise
    (hcentered : centered = false) (z : ℝ × ℝ) :
    magnitude z / normalization ≤
      (annulus ^ cap * orbitalFieldFactor K * (Γ.index : ℝ) * fixedCoefficient) *
        originalBound ^ (profileDegree + commonDegree) *
        (1 + fourierHeight (WithLp.toLp 2 z)) ^ heightOrder *
        Z ^ (3 * step + loss / 2) / radical *
        Z ^ (-idealLogLength Z j.1.val) := by
  sorry

end LeftDirectExceptionalBudget
end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectExceptional_pointwise

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectOrdinaryExceptional_pointwise
