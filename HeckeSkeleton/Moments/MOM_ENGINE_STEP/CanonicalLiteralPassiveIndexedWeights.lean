import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveCapacityMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstCombinedAllowance

/-!
# The original arithmetic index for the actual passive family

The first Poisson profile is combined with the two actual extracted
scalars. The old shared divisor is charged by the original frozen pair
cost, once, while the later passive divisors remain independent.
Their inverse square-root norms may be discarded only after their
actual nonzero integral ideals have supplied lower bounds of one.

The family, capacities and chosen children are those of the actual
passive construction. Both original Möbius coefficients and common
radicals remain in the same original arithmetic index. The complete
slot cost is three powers of the original cap.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open CommonSupportMass
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralActualProfiles PrimeCancellation.Analytic

variable {K : Type} [Field K] [NumberField K]



variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable {ν : Measure (FiniteAdeleRing (𝓞 K) K)} [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

local instance canonicalLiteralPassiveIndexedWeightsCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable {ι : Type*} (G : ActualGaussSource C ι)
variable (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ G.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
variable (character : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))
variable (LC RC : SourceCartesianCover G.columns G.ideal)
variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad).supported.gated.CoveredClassKey LC RC)
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad).supported.gated.CoverHybridPredicates LC RC)
variable (firstKernel : SchwartzMap ℝ ℂ) (x : ι → ℝ) (j : v.AllocationKey)
variable (hlive : (v.leaf exceptional firstKernel x j).Live) (firstSign : ℝ)
variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)
variable (leftScalar rightScalar : ℂ)
variable (leftBalance rightBalance : Bool → ℝ)
variable (hleftBalance : ∀ r, 0 < leftBalance r)
variable (hrightBalance : ∀ r, 0 < rightBalance r)
variable (firstSupport : Finset (Ideal (𝓞 K)))
variable (hfirst : ∀ p ∈ firstSupport, Prime p)
variable (leftProfiles : ProfileSupport (v.literalLeftAtoms leftAtoms)
  ((primeSupport A.cS ∪ firstSupport) ∪ primeSupport v.1.val.1))
variable (rightProfiles : ProfileSupport (v.literalRightAtoms rightAtoms)
  ((primeSupport A.cS ∪ firstSupport) ∪ primeSupport v.1.val.1))
variable (hbaseLeft : (v.literalLeftAtoms leftAtoms).base = Z)
variable (hbaseRight : (v.literalRightAtoms rightAtoms).base = Z)
variable {ω ψ : HeckeCharacter K}
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (choice : CanonicalLiteralPassiveSource.PhaseChoice F C)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (hextra : extra = literalDeletionIdeal firstSupport hfirst)
variable (leftRecipe : CanonicalLiteralActualCharacters.Recipe P Rchar F parent oldMoving
  correction remaining extra (v.literalLeftAtoms leftAtoms))
variable (rightRecipe : CanonicalLiteralActualCharacters.Recipe P Rchar F parent oldMoving
  correction remaining extra (v.literalRightAtoms rightAtoms))
variable (profileBound : ℝ) (hprofileBound : 0 ≤ profileBound)
variable (hprofile : ∀ h ∈ (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).rows,
  ‖v.chart.weight h‖ ≤ profileBound)
variable (a : RealParameters) (step : ℝ)
variable (geometry : OriginalNominalGeometry (K := K) a Z step)
variable (hretained : geometry.retainedScale = retainedScale)
variable (henlargement : geometry.enlargement = g)
variable (hsecond : geometry.ideals.second.val =
  (primePowerProduct v.block.primes v.block.leftMultiplicity).val)
variable (hopposite : geometry.ideals.secondOpposite.val =
  (primePowerProduct v.block.primes v.block.rightMultiplicity).val)
variable (hunit : geometry.ideals.unitPart.val =
  (secondPatternUnitIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity
    (v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel)).val)
variable (hnonunit : geometry.ideals.nonunitPart.val =
  (secondPatternNonunitIdeal v.block.primes
    (v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel)).val)
variable (columnLoss cutoffExponent : ℝ)
variable (hcolumnLoss : 0 ≤ columnLoss) (hcutoffExponent : 0 ≤ cutoffExponent)
variable (hcutoffPower : cutoff ≤ Z ^ cutoffExponent)
variable (hactiveColumns : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
  A.exteriorNorm (G.ideal i) ≤
    Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss))
variable (hpaidSupport : A.exteriorNorm ((choice.phases.moving P Rchar oldMoving).effectiveFullSupport
  remaining) ≤
    Z ^ (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E + geometry.skeleton.wo))
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (hbackground : parent.plainBackground⁻¹ ∈ parent.theta ∨
  ¬ FiniteOrder parent.plainBackground)
variable (hslot : ∀ i, parent.slotCoefficient i ∈ parent.theta)
variable (hexceptional : (v.leaf exceptional firstKernel x j).exceptional = fun h =>
  (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).literalCharacter C P Rchar F oldMoving
    correction (v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel)
    (v.chart.originalSector P ∅ cutoff hcutoff v.rowLabel) h ∈ parent.theta)

local notation "rootLength" => idealLogLength Z
  (secondSixthRootIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity).val
local notation "paidCutoff" => 2 * columnLoss + cutoffExponent
local notation "m" => geometry.literalRowParameter paidCutoff
local notation "q" => geometry.literalSupportParameter rootLength
local notation "rectangles" =>
  v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance
local notation "leftTable" => ((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹).balancePlain leftBalance
local notation "rightTable" => ((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹).balancePlain rightBalance
local notation "leftTests" => (leftProfiles.profiles.scale leftScalar⁻¹).balancePlain leftBalance
local notation "rightTests" => (rightProfiles.profiles.scale rightScalar⁻¹).balancePlain rightBalance

local notation "normalizationRows" =>
  (v.literalSupportedRows leftAtoms rightAtoms).withColumnConstants leftScalar rightScalar
local notation "ordinaryRows" => normalizationRows.restrictRows
  (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
local notation "allocation" => v.literalAllocation exceptional firstKernel x j hlive
local notation "pattern" => v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel
local notation "sector" => v.chart.originalSector P ∅ cutoff hcutoff v.rowLabel

variable {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered parent a Z Y₁ Y₂ floor padding)
variable (direct : geometry.tag = .direct → parent.geometry.slotCount = 0)
variable (hsmall : 2 * (2 * columnLoss + cutoffExponent) ≤ step)
variable (error : ℝ) (herror : 0 ≤ error)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh)
variable {originalRows : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {originalHeights : Set ℝ} {originalOrders : Finset (ℕ × ℕ)}
variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi) (orders : Finset (ℕ × ℕ))
variable {originalBound : ℝ}
variable (original : RawProfileWindow originalRows originalHeights (Set.Icc lo hi)
  originalOrders parent originalBound)
variable (hreference : reference ∈ originalRows) (htime : time ∈ originalHeights)
variable (horders : orders ⊆ originalOrders)
variable (leftComputed : CanonicalLiteralFullKappaInput.ComputedProfiles
  ((leftProfiles.profiles.scale leftScalar⁻¹).balancePlain leftBalance)
  (Set.Icc lo hi) orders originalBound)
variable (rightComputed : CanonicalLiteralFullKappaInput.ComputedProfiles
  ((rightProfiles.profiles.scale rightScalar⁻¹).balancePlain rightBalance)
  (Set.Icc lo hi) orders originalBound)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (δ analyticHeight : ℝ) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)

local notation "leftAllocation" => (rectangles.leftFrame C false).allocation
local notation "rightAllocation" => (rectangles.rightFrame C false).allocation
local notation "leftPaid" => CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining
  (fun i => leftRecipe.slots.index (SlotRestriction.index leftAllocation.keep i))
local notation "rightPaid" => CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining
  (fun i => rightRecipe.slots.index (SlotRestriction.index rightAllocation.keep i))

local notation "production" =>
  v.literalPassiveNormalizedFamily
    (P := P) (Rchar := Rchar) (δ₂ := δ₂)
    (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (G := G)
    (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension)
    (width := width) (character := character) (dyad := dyad)
    (LC := LC) (RC := RC) (exceptional := exceptional)
    (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms) (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance) (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance) (firstSupport := firstSupport) (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (choice := choice) (parent := parent)
    (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step)
    (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit)
    (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport) (reference := reference)
    (time := time) (hone := hone) (hroot := hroot)
    (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct)
    (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh)
    (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := original) (hreference := hreference) (htime := htime)
    (horders := horders) (leftComputed := leftComputed) (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi)

local notation "originalFrozenPair" =>
  CanonicalLiteralRectangles.Atoms.originalFrozenPairCost
    leftTable rightTable leftAllocation rightAllocation

local notation "allowanceProof" =>
  v.literalPassiveNormalizedFamily_allowance_coarse_from_original_atoms
    (P := P) (Rchar := Rchar) (δ₂ := δ₂)
    (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (G := G)
    (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension)
    (width := width) (character := character) (dyad := dyad)
    (LC := LC) (RC := RC) (exceptional := exceptional)
    (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms) (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance) (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance) (firstSupport := firstSupport) (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (choice := choice) (parent := parent)
    (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step)
    (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit)
    (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport) (reference := reference)
    (time := time) (hone := hone) (hroot := hroot)
    (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct)
    (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh)
    (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := original) (hreference := hreference) (htime := htime)
    (horders := horders) (leftComputed := leftComputed) (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi)

variable
    (cap : ℕ)
    (hcountL : (LC.branch v.2.2.1).slotCount ≤ cap)
    (hcountR : (RC.branch v.2.2.2.1).slotCount ≤ cap)
    (atomBound : ℝ) (hAtomBound : 1 ≤ atomBound)
    (hcostL : ∀ i p, leftAtoms.primeAtomCost i p ≤ atomBound)
    (hcostR : ∀ i p, rightAtoms.primeAtomCost i p ≤ atomBound)
    (hprimeL : leftAtoms.PrimeNormWindow hi)
    (hprimeR : rightAtoms.PrimeNormWindow hi)
    (hslotsL : ∀ i, v.literalLeftParent.reindex.slots i = leftAtoms.slots i)
    (hslotsR : ∀ i, v.literalRightParent.reindex.slots i = rightAtoms.slots i)
    (hfirstL : ∀ r, r = false ∨ leftAtoms.centered = true →
      leftAtoms.scaleProduct r * (Ideal.absNorm geometry.literalFirstExtraction.val : ℝ) ≤
        hi ^ cap * Z ^ (a.n₁ + a.n₂ + a.z))
    (hfirstR : ∀ r, r = false ∨ rightAtoms.centered = true →
      rightAtoms.scaleProduct r * (Ideal.absNorm geometry.literalFirstExtraction.val : ℝ) ≤
        hi ^ cap * Z ^ (a.n₁ + a.n₂ + a.z))
    (hgaussL : Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w) ≤
      leftAtoms.gaussScale)
    (hgaussR : Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w) ≤
      rightAtoms.gaussScale)
    (herrorPos : 0 < error)
    (hannulusThreshold : OriginalPairAllowanceProduction.annulusThreshold hi error ≤ Z)
    (hscaleThreshold : hi ^ (2 * cap) ≤ Z ^ error)
    (hsupportError : geometry.supportError ≤ error)
    (hphysicalError : 2 * columnLoss + cutoffExponent ≤ error)
    (firstNormalization : ℝ)
    (hfirstNormalization : firstNormalization =
      firstLeftAllowance Z (geometry.skeleton.A +
        (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E))
        geometry.ideals.first.val geometry.ideals.opposite.val)

variable {branch : TwoDivisorCommonBranch (K := K)}
variable {Ray₁ Ray₂ : Type*}
  [CommGroup Ray₁] [Fintype Ray₁] [CommGroup Ray₂] [Fintype Ray₂]
variable (index : branch.Index)
variable (hleftIndex : v.1.val.1 = index.2.2.1.val.1.1)
variable (hrightIndex : v.1.val.2 = index.2.2.1.val.1.2)
variable (hdivisorIndex : j.1.val = index.2.2.2.1.val)
variable (parentWidth total rawProfile firstCost tilt : ℝ)
variable (hrawProfile : 0 ≤ rawProfile) (hfirstCost : 0 ≤ firstCost)
variable (hcombinedProfile : rawProfile * (‖leftScalar‖ * ‖rightScalar‖) ≤
  firstCost * Z ^ (parentWidth - total + tilt))
variable (hD : index.1.val.1.1 ≠ 0) (hE : index.1.val.1.2 ≠ 0)
variable (hsupportFirst : primeSupport index.1.val.1.1 = primeSupport index.1.val.1.2)
variable (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
variable (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle)

local notation "rowCost" =>
  (Γ.index : ℝ) * profileBound * atomBound ^ (3 * cap) * orbitalFieldFactor K
local notation "scalarPair" => ‖leftScalar‖ * ‖rightScalar‖
local notation "remainingExponent" =>
  geometry.skeleton.wo + geometry.tag.poolLength step + 5 * error / 3 + mesh
local notation "firstFactor" =>
  firstOriginalAllowanceWeight Z parentWidth total rawProfile index.1.val.1.1 index.1.val.1.2 *
    ‖(moebius index.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
    ‖(moebius index.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖

include hcountL hcountR hAtomBound hcostL hcostR hprimeL hprimeR hslotsL hslotsR
  hfirstL hfirstR hgaussL hgaussR herrorPos hannulusThreshold hscaleThreshold
  hsupportError hphysicalError hfirstNormalization
  hleftIndex hrightIndex hdivisorIndex hrawProfile hfirstCost hcombinedProfile hD hE hsupportFirst in
/-- The actual old frozen cost and the same passive child weight
are paid together with the original first Poisson profile. -/
theorem literalPassiveNormalizedFamily_index_from_combined_atoms :
    ∀ analyticLeft analyticRight heightLeft heightRight
      (b : (production analyticLeft analyticRight heightLeft heightRight).active Finset.univ),
      firstFactor * (originalFrozenPair *
        (production analyticLeft analyticRight heightLeft heightRight).weight Finset.univ 0 b /
          firstNormalization) ≤
        firstCost * rowCost * Z ^ (remainingExponent + tilt) * branch.indexWeight index := by
  intro analyticLeft analyticRight heightLeft heightRight b
  let family := production analyticLeft analyticRight heightLeft heightRight
  have hz : 0 < Z := zero_lt_one.trans domain.scale
  have hsecondWeight := allowanceProof cap hcountL hcountR atomBound hAtomBound
    hcostL hcostR hprimeL hprimeR hslotsL hslotsR hfirstL hfirstR hgaussL hgaussR
    herrorPos hannulusThreshold hscaleThreshold hsupportError hphysicalError
    firstNormalization hfirstNormalization 0 analyticLeft analyticRight heightLeft heightRight b
  simp only [Real.rpow_zero, mul_one] at hsecondWeight
  have hfirstWeight := firstOriginalAllowanceWeight_mul_le_radical
    Z parentWidth total rawProfile scalarPair firstCost tilt domain.scale hfirstCost
    hcombinedProfile index.1.val.1.1 index.1.val.1.2 hD hE hsupportFirst
  have hfirstNonneg := firstOriginalAllowanceWeight_nonneg Z parentWidth total
    rawProfile hz hrawProfile index.1.val.1.1 index.1.val.1.2
  have hconstant : 0 ≤ rowCost :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hprofileBound)
        (pow_nonneg (zero_le_one.trans hAtomBound) _)) (orbitalFieldFactor_nonneg K)
  have hsecondRest : 0 ≤ rowCost * Z ^ remainingExponent *
      (1 / (Ideal.absNorm (commonRadical v.1.val.1 v.1.val.2) : ℝ)) /
        (Ideal.absNorm j.1.val : ℝ) :=
    div_nonneg
      (mul_nonneg (mul_nonneg hconstant (Real.rpow_nonneg hz.le _))
        (one_div_nonneg.mpr (Nat.cast_nonneg _))) (Nat.cast_nonneg _)
  have hpair :
      firstOriginalAllowanceWeight Z parentWidth total rawProfile
          index.1.val.1.1 index.1.val.1.2 *
          ((originalFrozenPair * family.weight Finset.univ 0 b) / firstNormalization) ≤
        (firstCost * rowCost * Z ^ (remainingExponent + tilt)) /
          (Ideal.absNorm (commonRadical index.1.val.1.1 index.1.val.1.2) : ℝ) *
          (1 / (Ideal.absNorm (commonRadical v.1.val.1 v.1.val.2) : ℝ)) /
          (Ideal.absNorm j.1.val : ℝ) := by
    calc
      _ ≤ firstOriginalAllowanceWeight Z parentWidth total rawProfile
          index.1.val.1.1 index.1.val.1.2 *
          (((Γ.index : ℝ) * (profileBound * ‖leftScalar‖ * ‖rightScalar‖) *
            atomBound ^ (3 * cap) * orbitalFieldFactor K) * Z ^ remainingExponent *
              (1 / (Ideal.absNorm (commonRadical v.1.val.1 v.1.val.2) : ℝ)) /
                (Ideal.absNorm j.1.val : ℝ)) :=
        mul_le_mul_of_nonneg_left hsecondWeight hfirstNonneg
      _ = (firstOriginalAllowanceWeight Z parentWidth total rawProfile
            index.1.val.1.1 index.1.val.1.2 * scalarPair) *
          (rowCost * Z ^ remainingExponent *
            (1 / (Ideal.absNorm (commonRadical v.1.val.1 v.1.val.2) : ℝ)) /
              (Ideal.absNorm j.1.val : ℝ)) := by ring
      _ ≤ (firstCost * Z ^ tilt /
            (Ideal.absNorm (commonRadical index.1.val.1.1 index.1.val.1.2) : ℝ)) *
          (rowCost * Z ^ remainingExponent *
            (1 / (Ideal.absNorm (commonRadical v.1.val.1 v.1.val.2) : ℝ)) /
              (Ideal.absNorm j.1.val : ℝ)) :=
        mul_le_mul_of_nonneg_right hfirstWeight hsecondRest
      _ = _ := by
        rw [Real.rpow_add hz remainingExponent tilt]
        ring
  have hcoeff :
      ‖(moebius index.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
        ‖(moebius index.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖ ≤
      ‖(moebius index.2.1.val : ℂ)‖ * ‖(moebius index.2.2.2.1.val : ℂ)‖ := by
    have hc₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (fixed_phase_coefficient_norm Ray₁ phase₁ χ₁) (norm_nonneg _))
      (norm_nonneg (moebius index.2.2.2.1.val : ℂ))
    simpa only [mul_one] using mul_le_mul hc₁ (fixed_phase_coefficient_norm Ray₂ phase₂ χ₂)
      (norm_nonneg _) (by positivity)
  have hupper : 0 ≤
      (firstCost * rowCost * Z ^ (remainingExponent + tilt)) /
        (Ideal.absNorm (commonRadical index.1.val.1.1 index.1.val.1.2) : ℝ) *
        (1 / (Ideal.absNorm (commonRadical v.1.val.1 v.1.val.2) : ℝ)) /
        (Ideal.absNorm j.1.val : ℝ) :=
    div_nonneg (mul_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg hfirstCost hconstant)
        (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
      (one_div_nonneg.mpr (Nat.cast_nonneg _))) (Nat.cast_nonneg _)
  have h := mul_le_mul hpair hcoeff (by positivity) hupper
  convert h using 1 <;>
    simp only [TwoDivisorCommonBranch.indexWeight, hleftIndex, hrightIndex, hdivisorIndex] <;> ring

local notation "indexProof" =>
  v.literalPassiveNormalizedFamily_index_from_combined_atoms
    (P := P) (Rchar := Rchar) (δ₂ := δ₂)
    (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (G := G)
    (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff)
    (hcutoff := hcutoff) (hnorm := hnorm) (dimension := dimension)
    (width := width) (character := character) (dyad := dyad)
    (LC := LC) (RC := RC) (exceptional := exceptional)
    (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms) (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance) (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance) (firstSupport := firstSupport) (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
    (F := F) (choice := choice) (parent := parent)
    (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (remaining := remaining) (extra := extra) (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe) (profileBound := profileBound) (hprofileBound := hprofileBound)
    (hprofile := hprofile) (a := a) (step := step)
    (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit)
    (hnonunit := hnonunit) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent) (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport) (reference := reference)
    (time := time) (hone := hone) (hroot := hroot)
    (hemb := hemb) (hbackground := hbackground) (hslot := hslot)
    (hexceptional := hexceptional) (domain := domain) (direct := direct)
    (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh)
    (hfit := hfit) (lo := lo) (hi := hi)
    (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := original) (hreference := hreference) (htime := htime)
    (horders := horders) (leftComputed := leftComputed) (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders) (δ := δ) (analyticHeight := analyticHeight)
    (hδ := hδ) (hδhi := hδhi)

include hcountL hcountR hAtomBound hcostL hcostR hprimeL hprimeR hslotsL hslotsR
  hfirstL hfirstR hgaussL hgaussR herrorPos hannulusThreshold hscaleThreshold
  hsupportError hphysicalError hfirstNormalization
  hleftIndex hrightIndex hdivisorIndex hrawProfile hfirstCost hcombinedProfile hD hE hsupportFirst in
/-- An exact original parent-weight identity attaches the original
outer scalar to this same family. It does not change either child or
one of the passive allocation labels. -/
theorem literalPassiveNormalizedFamily_outer_index_from_combined_atoms
    (outerWeight factor : ℝ) (hfactor : 0 ≤ factor)
    (houter : outerWeight / Z ^ parentWidth = factor * firstFactor / firstNormalization) :
    ∀ analyticLeft analyticRight heightLeft heightRight
      (b : (production analyticLeft analyticRight heightLeft heightRight).active Finset.univ),
      outerWeight * originalFrozenPair *
          (production analyticLeft analyticRight heightLeft heightRight).weight Finset.univ parentWidth b ≤
        factor * (firstCost * rowCost * Z ^ (remainingExponent + tilt) * branch.indexWeight index) := by
  intro analyticLeft analyticRight heightLeft heightRight b
  let family := production analyticLeft analyticRight heightLeft heightRight
  have hindex := indexProof cap hcountL hcountR atomBound hAtomBound
    hcostL hcostR hprimeL hprimeR hslotsL hslotsR hfirstL hfirstR hgaussL hgaussR
    herrorPos hannulusThreshold hscaleThreshold hsupportError hphysicalError
    firstNormalization hfirstNormalization index hleftIndex hrightIndex hdivisorIndex
    parentWidth total rawProfile firstCost tilt hrawProfile hfirstCost hcombinedProfile hD hE hsupportFirst
    phase₁ χ₁ phase₂ χ₂ analyticLeft analyticRight heightLeft heightRight b
  have hpw : family.weight Finset.univ parentWidth b =
      family.weight Finset.univ 0 b / Z ^ parentWidth := by
    simp only [ActualNormalizedPairFamily.weight, normalizedCapacityPairWeight,
      Real.rpow_zero, div_one]
  calc
    _ = (outerWeight / Z ^ parentWidth) *
        (originalFrozenPair * family.weight Finset.univ 0 b) := by rw [hpw]; ring
    _ = factor * (firstFactor *
        (originalFrozenPair * family.weight Finset.univ 0 b / firstNormalization)) := by
      rw [houter]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hindex hfactor

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_index_from_combined_atoms
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_outer_index_from_combined_atoms
