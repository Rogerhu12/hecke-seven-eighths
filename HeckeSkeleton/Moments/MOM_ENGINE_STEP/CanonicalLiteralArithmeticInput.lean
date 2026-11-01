import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormalizedLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ArithmeticNormalizedLeaves

/-!
# Original arithmetic costs for the literal normalized family

The same original common occurrences and second allocation determine
all row and frozen-atom costs. The two stripped constants are paid once
in the original row profile, before the capacity child is chosen. This
module exposes those calculated data directly as the arithmetic input
of the actual `literalNormalizationData`; no total-mass or source-bound
premise is introduced.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

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

local instance canonicalLiteralArithmeticInputCircleCharacterFintype :
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
variable (hold : A.exteriorNorm ((F.moving P Rchar oldMoving).effectiveFullSupport
  (remaining * extra)) ≤
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

local notation "calibrations" =>
  v.computedLiteralCalibrations P Rchar δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ
    cutoff hcutoff hnorm dimension width character dyad LC RC exceptional firstKernel x j
    hlive firstSign leftAtoms rightAtoms leftScalar rightScalar leftBalance rightBalance
    hleftBalance hrightBalance firstSupport hfirst leftProfiles rightProfiles hbaseLeft hbaseRight
    F parent oldMoving correction hcorr remaining extra hextra leftRecipe rightRecipe
    profileBound hprofileBound hprofile a step geometry hretained henlargement
    hsecond hopposite hunit hnonunit columnLoss cutoffExponent hcutoffPower hactiveColumns hold
    reference time hone hroot hemb hbackground hslot hexceptional

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

/-- Both common dictionaries are built on the actual occurrence witnesses.
The two stripped column constants are paid in this same row profile,
and the original ordinary predicate only restricts that existing row set. -/
def literalOriginalArithmeticMass :
    ActualSecondRowMass ordinaryRows C
      (LC.branch v.2.2.1).slotCount (RC.branch v.2.2.2.1).slotCount := by
  have hp : v.chart.NonunitLabelStable :=
    ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_nonunitLabelStable
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad v.1 v.2.1
  have hmaskL : (v.literalLeftOriginal leftAtoms).characters.MaskIndicator := by
    change (v.literalLeftAtoms leftAtoms).characters.MaskIndicator
    rw [leftRecipe.characters]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator P Rchar F parent
      oldMoving correction remaining extra leftRecipe.slots.index
  have hmaskR : (v.literalRightOriginal rightAtoms).characters.MaskIndicator := by
    change (v.literalRightAtoms rightAtoms).characters.MaskIndicator
    rw [rightRecipe.characters]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator P Rchar F parent
      oldMoving correction remaining extra rightRecipe.slots.index
  exact ((v.literalSupportedRowMass leftAtoms rightAtoms hmaskL hmaskR hp
    profileBound hprofileBound hprofile).withColumnConstants leftScalar rightScalar).restrictRows
      (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)

/-- The frozen left cost is calculated on the actual second allocation.
The inverse norm of its own divisor remains in `scalarBound`. -/
def literalOriginalArithmeticLeftFrozen (r : Bool) :
    (rectangles.leftFrame C r).source.FrozenAtomBounds := by
  have hmask : leftTable.characters.MaskIndicator := by
    change (v.literalLeftAtoms leftAtoms).characters.MaskIndicator
    rw [leftRecipe.characters]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator P Rchar F parent
      oldMoving correction remaining extra leftRecipe.slots.index
  have hL := (Finset.mem_filter.mp allocation.property).2.1
  exact leftTable.frozenBounds ordinaryRows C .left j.2.1
    (fun i => v.block.leftResidual (v.leftReindex.index i)) v.leftReindex.ideal_product
    firstSign r j.1.val j.2.2.1.val (Finset.mem_filter.mp allocation.property).2.2.1
    hmask hL j.2.2.1.property

/-- The right frozen dictionary has its own actual occurrence witness,
but exactly the same stored divisor as the left dictionary. -/
def literalOriginalArithmeticRightFrozen (r : Bool) :
    (rectangles.rightFrame C r).source.FrozenAtomBounds := by
  have hmask : rightTable.characters.MaskIndicator := by
    change (v.literalRightAtoms rightAtoms).characters.MaskIndicator
    rw [rightRecipe.characters]
    exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator P Rchar F parent
      oldMoving correction remaining extra rightRecipe.slots.index
  have hL := (Finset.mem_filter.mp allocation.property).2.1
  exact rightTable.frozenBounds ordinaryRows C .right j.2.1
    (fun i => v.block.rightResidual (v.rightReindex.index i)) v.rightReindex.ideal_product
    (-firstSign) r j.1.val j.2.2.2.val (Finset.mem_filter.mp allocation.property).2.2.2
    hmask hL j.2.2.2.property

local notation "originalMass" =>
  v.literalOriginalArithmeticMass
    (P := P) (Rchar := Rchar) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (G := G) (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff) (hcutoff := hcutoff)
    (hnorm := hnorm) (dimension := dimension) (width := width)
    (character := character) (dyad := dyad) (LC := LC) (RC := RC)
    (exceptional := exceptional) (firstKernel := firstKernel) (x := x) (j := j)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (leftScalar := leftScalar) (rightScalar := rightScalar)
    (F := F) (parent := parent) (oldMoving := oldMoving) (correction := correction)
    (remaining := remaining) (extra := extra)
    (leftRecipe := leftRecipe) (rightRecipe := rightRecipe)
    (profileBound := profileBound) (hprofileBound := hprofileBound) (hprofile := hprofile)

@[simp] theorem literalOriginalArithmeticMass_fiber :
    originalMass.originalFiber = Γ.index := rfl

@[simp] theorem literalOriginalArithmeticMass_unit :
    originalMass.unitIdeal = secondPatternUnitIdeal v.block.primes
      v.block.leftMultiplicity v.block.rightMultiplicity pattern := rfl

@[simp] theorem literalOriginalArithmeticMass_nonunit :
    originalMass.nonunitIdeal = secondPatternNonunitIdeal v.block.primes pattern := rfl

@[simp] theorem literalOriginalArithmeticMass_profileBound :
    originalMass.profileBound = profileBound * ‖leftScalar‖ * ‖rightScalar‖ := rfl

/-- This supplies the actual arithmetic input of the already constructed
normalization. The caller supplies the same original single-character
analytic certificates as to `literalNormalizationData`; neither a row
mass dictionary, frozen bound nor finished normalization is an input. -/
def literalNormalizationArithmeticInput
    (X : (v.leaf exceptional firstKernel x j).ConstantAtomExtraction)
    (binding : X.leaf.OrdinaryBinding rectangles) :=
  let normalization :=
    v.literalNormalizationData
      (P := P)
      (Rchar := Rchar)
      (δ₂ := δ₂)
      (hδ₂ := hδ₂)
      (hδ₂half := hδ₂half)
      (G := G)
      (retainedScale := retainedScale)
      (Z := Z)
      (g := g)
      (hscale := hscale)
      (hZ := hZ)
      (cutoff := cutoff)
      (hcutoff := hcutoff)
      (hnorm := hnorm)
      (dimension := dimension)
      (width := width)
      (character := character)
      (dyad := dyad)
      (LC := LC)
      (RC := RC)
      (exceptional := exceptional)
      (firstKernel := firstKernel)
      (x := x)
      (j := j)
      (hlive := hlive)
      (firstSign := firstSign)
      (leftAtoms := leftAtoms)
      (rightAtoms := rightAtoms)
      (leftScalar := leftScalar)
      (rightScalar := rightScalar)
      (leftBalance := leftBalance)
      (rightBalance := rightBalance)
      (hleftBalance := hleftBalance)
      (hrightBalance := hrightBalance)
      (firstSupport := firstSupport)
      (hfirst := hfirst)
      (leftProfiles := leftProfiles)
      (rightProfiles := rightProfiles)
      (hbaseLeft := hbaseLeft)
      (hbaseRight := hbaseRight)
      (F := F)
      (parent := parent)
      (oldMoving := oldMoving)
      (correction := correction)
      (hcorr := hcorr)
      (remaining := remaining)
      (extra := extra)
      (hextra := hextra)
      (leftRecipe := leftRecipe)
      (rightRecipe := rightRecipe)
      (profileBound := profileBound)
      (hprofileBound := hprofileBound)
      (hprofile := hprofile)
      (a := a)
      (step := step)
      (geometry := geometry)
      (hretained := hretained)
      (henlargement := henlargement)
      (hsecond := hsecond)
      (hopposite := hopposite)
      (hunit := hunit)
      (hnonunit := hnonunit)
      (columnLoss := columnLoss)
      (cutoffExponent := cutoffExponent)
      (hcolumnLoss := hcolumnLoss)
      (hcutoffExponent := hcutoffExponent)
      (hcutoffPower := hcutoffPower)
      (hactiveColumns := hactiveColumns)
      (hold := hold)
      (reference := reference)
      (time := time)
      (hone := hone)
      (hroot := hroot)
      (hemb := hemb)
      (hbackground := hbackground)
      (hslot := hslot)
      (hexceptional := hexceptional)
      (domain := domain)
      (direct := direct)
      (hsmall := hsmall)
      (error := error)
      (herror := herror)
      (hstep := hstep)
      (mesh := mesh)
      (hmesh := hmesh)
      (hfit := hfit)
      (lo := lo)
      (hi := hi)
      (hlo := hlo)
      (hhi := hhi)
      (orders := orders)
      (original := original)
      (hreference := hreference)
      (htime := htime)
      (horders := horders)
      (leftComputed := leftComputed)
      (rightComputed := rightComputed)
      (hprimeOrders := hprimeOrders)
      (δ := δ)
      (analyticHeight := analyticHeight)
      (hδ := hδ)
      (hδhi := hδhi)
      (X := X)
      (binding := binding)
  fun analyticLeft analyticRight hanalyticLeft hanalyticRight =>
    show (normalization analyticLeft analyticRight hanalyticLeft hanalyticRight).ArithmeticInput from
      { commonLeftSlots := (LC.branch v.2.2.1).slotCount
        commonRightSlots := (RC.branch v.2.2.2.1).slotCount
        rowMass := originalMass
        leftAtoms := fun r => v.literalOriginalArithmeticLeftFrozen
          (P := P) (Rchar := Rchar) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
          (G := G) (retainedScale := retainedScale) (Z := Z) (g := g)
          (hscale := hscale) (hZ := hZ) (cutoff := cutoff) (hcutoff := hcutoff)
          (hnorm := hnorm) (dimension := dimension) (width := width)
          (character := character) (dyad := dyad) (LC := LC) (RC := RC)
          (exceptional := exceptional) (firstKernel := firstKernel) (x := x) (j := j)
          (hlive := hlive) (firstSign := firstSign)
          (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
          (leftScalar := leftScalar) (rightScalar := rightScalar)
          (leftBalance := leftBalance) (rightBalance := rightBalance)
          (hleftBalance := hleftBalance) (hrightBalance := hrightBalance)
          (F := F) (parent := parent) (oldMoving := oldMoving) (correction := correction)
          (remaining := remaining) (extra := extra) (leftRecipe := leftRecipe) r
        rightAtoms := fun r => v.literalOriginalArithmeticRightFrozen
          (P := P) (Rchar := Rchar) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
          (G := G) (retainedScale := retainedScale) (Z := Z) (g := g)
          (hscale := hscale) (hZ := hZ) (cutoff := cutoff) (hcutoff := hcutoff)
          (hnorm := hnorm) (dimension := dimension) (width := width)
          (character := character) (dyad := dyad) (LC := LC) (RC := RC)
          (exceptional := exceptional) (firstKernel := firstKernel) (x := x) (j := j)
          (hlive := hlive) (firstSign := firstSign)
          (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
          (leftScalar := leftScalar) (rightScalar := rightScalar)
          (leftBalance := leftBalance) (rightBalance := rightBalance)
          (hleftBalance := hleftBalance) (hrightBalance := hrightBalance)
          (F := F) (parent := parent) (oldMoving := oldMoving) (correction := correction)
          (remaining := remaining) (extra := extra) (rightRecipe := rightRecipe) r }


section SameOriginalNormalization

variable (X : (v.leaf exceptional firstKernel x j).ConstantAtomExtraction)
variable (binding : X.leaf.OrdinaryBinding rectangles)

local notation "originalNormalization" =>
  v.literalNormalizationData
    (P := P)
    (Rchar := Rchar)
    (δ₂ := δ₂)
    (hδ₂ := hδ₂)
    (hδ₂half := hδ₂half)
    (G := G)
    (retainedScale := retainedScale)
    (Z := Z)
    (g := g)
    (hscale := hscale)
    (hZ := hZ)
    (cutoff := cutoff)
    (hcutoff := hcutoff)
    (hnorm := hnorm)
    (dimension := dimension)
    (width := width)
    (character := character)
    (dyad := dyad)
    (LC := LC)
    (RC := RC)
    (exceptional := exceptional)
    (firstKernel := firstKernel)
    (x := x)
    (j := j)
    (hlive := hlive)
    (firstSign := firstSign)
    (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms)
    (leftScalar := leftScalar)
    (rightScalar := rightScalar)
    (leftBalance := leftBalance)
    (rightBalance := rightBalance)
    (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance)
    (firstSupport := firstSupport)
    (hfirst := hfirst)
    (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles)
    (hbaseLeft := hbaseLeft)
    (hbaseRight := hbaseRight)
    (F := F)
    (parent := parent)
    (oldMoving := oldMoving)
    (correction := correction)
    (hcorr := hcorr)
    (remaining := remaining)
    (extra := extra)
    (hextra := hextra)
    (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe)
    (profileBound := profileBound)
    (hprofileBound := hprofileBound)
    (hprofile := hprofile)
    (a := a)
    (step := step)
    (geometry := geometry)
    (hretained := hretained)
    (henlargement := henlargement)
    (hsecond := hsecond)
    (hopposite := hopposite)
    (hunit := hunit)
    (hnonunit := hnonunit)
    (columnLoss := columnLoss)
    (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss)
    (hcutoffExponent := hcutoffExponent)
    (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns)
    (hold := hold)
    (reference := reference)
    (time := time)
    (hone := hone)
    (hroot := hroot)
    (hemb := hemb)
    (hbackground := hbackground)
    (hslot := hslot)
    (hexceptional := hexceptional)
    (domain := domain)
    (direct := direct)
    (hsmall := hsmall)
    (error := error)
    (herror := herror)
    (hstep := hstep)
    (mesh := mesh)
    (hmesh := hmesh)
    (hfit := hfit)
    (lo := lo)
    (hi := hi)
    (hlo := hlo)
    (hhi := hhi)
    (orders := orders)
    (original := original)
    (hreference := hreference)
    (htime := htime)
    (horders := horders)
    (leftComputed := leftComputed)
    (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders)
    (δ := δ)
    (analyticHeight := analyticHeight)
    (hδ := hδ)
    (hδhi := hδhi)
    (X := X)
    (binding := binding)

local notation "originalArithmeticInput" =>
  v.literalNormalizationArithmeticInput
    (P := P)
    (Rchar := Rchar)
    (δ₂ := δ₂)
    (hδ₂ := hδ₂)
    (hδ₂half := hδ₂half)
    (G := G)
    (retainedScale := retainedScale)
    (Z := Z)
    (g := g)
    (hscale := hscale)
    (hZ := hZ)
    (cutoff := cutoff)
    (hcutoff := hcutoff)
    (hnorm := hnorm)
    (dimension := dimension)
    (width := width)
    (character := character)
    (dyad := dyad)
    (LC := LC)
    (RC := RC)
    (exceptional := exceptional)
    (firstKernel := firstKernel)
    (x := x)
    (j := j)
    (hlive := hlive)
    (firstSign := firstSign)
    (leftAtoms := leftAtoms)
    (rightAtoms := rightAtoms)
    (leftScalar := leftScalar)
    (rightScalar := rightScalar)
    (leftBalance := leftBalance)
    (rightBalance := rightBalance)
    (hleftBalance := hleftBalance)
    (hrightBalance := hrightBalance)
    (firstSupport := firstSupport)
    (hfirst := hfirst)
    (leftProfiles := leftProfiles)
    (rightProfiles := rightProfiles)
    (hbaseLeft := hbaseLeft)
    (hbaseRight := hbaseRight)
    (F := F)
    (parent := parent)
    (oldMoving := oldMoving)
    (correction := correction)
    (hcorr := hcorr)
    (remaining := remaining)
    (extra := extra)
    (hextra := hextra)
    (leftRecipe := leftRecipe)
    (rightRecipe := rightRecipe)
    (profileBound := profileBound)
    (hprofileBound := hprofileBound)
    (hprofile := hprofile)
    (a := a)
    (step := step)
    (geometry := geometry)
    (hretained := hretained)
    (henlargement := henlargement)
    (hsecond := hsecond)
    (hopposite := hopposite)
    (hunit := hunit)
    (hnonunit := hnonunit)
    (columnLoss := columnLoss)
    (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss)
    (hcutoffExponent := hcutoffExponent)
    (hcutoffPower := hcutoffPower)
    (hactiveColumns := hactiveColumns)
    (hold := hold)
    (reference := reference)
    (time := time)
    (hone := hone)
    (hroot := hroot)
    (hemb := hemb)
    (hbackground := hbackground)
    (hslot := hslot)
    (hexceptional := hexceptional)
    (domain := domain)
    (direct := direct)
    (hsmall := hsmall)
    (error := error)
    (herror := herror)
    (hstep := hstep)
    (mesh := mesh)
    (hmesh := hmesh)
    (hfit := hfit)
    (lo := lo)
    (hi := hi)
    (hlo := hlo)
    (hhi := hhi)
    (orders := orders)
    (original := original)
    (hreference := hreference)
    (htime := htime)
    (horders := horders)
    (leftComputed := leftComputed)
    (rightComputed := rightComputed)
    (hprimeOrders := hprimeOrders)
    (δ := δ)
    (analyticHeight := analyticHeight)
    (hδ := hδ)
    (hδhi := hδhi)
    (X := X)
    (binding := binding)

/-- The actual calibration already carries these original costs. The
arithmetic presentation is definitionally the same complete normalization,
so its chosen children, removed sets, radii and kernel are unchanged. -/
theorem literalNormalizationArithmeticInput_eq_self :
    ∀ analyticLeft analyticRight hanalyticLeft hanalyticRight,
      (originalNormalization analyticLeft analyticRight hanalyticLeft hanalyticRight).withArithmetic
        (originalArithmeticInput analyticLeft analyticRight hanalyticLeft hanalyticRight) =
      originalNormalization analyticLeft analyticRight hanalyticLeft hanalyticRight := by
  intro analyticLeft analyticRight hanalyticLeft hanalyticRight
  rfl

end SameOriginalNormalization

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalOriginalArithmeticMass
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalOriginalArithmeticLeftFrozen
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalOriginalArithmeticRightFrozen
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalNormalizationArithmeticInput

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalNormalizationArithmeticInput_eq_self
