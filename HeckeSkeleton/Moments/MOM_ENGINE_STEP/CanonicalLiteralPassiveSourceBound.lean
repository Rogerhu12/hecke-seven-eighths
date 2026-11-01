import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveCoveredBound

/-!
# The actual original integrand enters the same passive normalized family

The family is the output of `literalPassiveNormalizedFamily`, including
its original base and its already selected children. The complete
ordinary coefficient is bounded by the passive polynomial on the
same rows. Finite Minkowski and the family's finite capacity bound are
then applied without changing either Fourier variable or either kernel.

The old second-allocation cost remains a single external factor.
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

local instance canonicalLiteralPassiveSourceBoundCircleCharacterFintype :
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
local notation "ordinaryRows" => (normalizationRows).restrictRows
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

local notation "leftAllocation" => ((rectangles).leftFrame C false).allocation
local notation "rightAllocation" => ((rectangles).rightFrame C false).allocation
local notation "leftPaid" => CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining
  (fun i => leftRecipe.slots.index (SlotRestriction.index (leftAllocation).keep i))
local notation "rightPaid" => CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining
  (fun i => rightRecipe.slots.index (SlotRestriction.index (rightAllocation).keep i))

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

local notation "Labels" => CanonicalLiteralPassiveNormalizedFamily.PairLabel (A := A)
  leftTests rightTests leftAllocation rightAllocation (choice.mask extra) (choice.mask extra)
local notation "LeftLabel" => CanonicalLiteralPassiveNormalizedFamily.SideLabel
  leftTests leftAllocation A (choice.mask extra)
local notation "RightLabel" => CanonicalLiteralPassiveNormalizedFamily.SideLabel
  rightTests rightAllocation A (choice.mask extra)
local notation "leftFrame" => fun b : LeftLabel =>
  CanonicalLiteralPassiveFrames.frame leftTests leftAllocation A leftPaid C ordinaryRows
    .left (choice.mask extra) b.1.val firstSign b.2
local notation "rightFrame" => fun b : RightLabel =>
  CanonicalLiteralPassiveFrames.frame rightTests rightAllocation A rightPaid C ordinaryRows
    .right (choice.mask extra) b.1.val (-firstSign) b.2
local notation "frozenPair" =>
  Real.sqrt ((leftTable).originalFrozenCost leftAllocation) *
    Real.sqrt ((rightTable).originalFrozenCost rightAllocation)
local notation "passiveIntegrand" => CanonicalLiteralPassiveNormalizedFamily.integrand
  C ordinaryRows leftTests rightTests leftAllocation rightAllocation leftPaid rightPaid
  (choice.mask extra) (choice.mask extra) firstSign (-firstSign)

include hfirst hextra in
/-- This conclusion concerns the actual produced family. Its capacity
children are the same fixed choices used by its kernels and masses. -/
theorem literalPassiveNormalizedFamily_sourcePairs :
    ∀ analyticLeft analyticRight heightLeft heightRight (parentWidth : ℝ)
      (ξ : WithLp 2 (ℝ × ℝ)),
    let family := production analyticLeft analyticRight heightLeft heightRight
    (rectangles).originalIntegrand ξ / Z ^ parentWidth ≤ frozenPair *
      ∑ b : Labels, family.sourcePair parentWidth b ξ := by
  intro analyticLeft analyticRight heightLeft heightRight parentWidth ξ
  let family := production analyticLeft analyticRight heightLeft heightRight
  have hpre := v.literalPassiveOriginalIntegrand_le
    (P := P) (Rchar := Rchar) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (G := G) (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := hZ) (cutoff := cutoff) (hcutoff := hcutoff)
    (hnorm := hnorm) (dimension := dimension) (width := width)
    (character := character) (dyad := dyad) (LC := LC) (RC := RC)
    (exceptional := exceptional) (firstKernel := firstKernel) (x := x) (j := j)
    (hlive := hlive) (firstSign := firstSign) (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance)
    (hleftBalance := hleftBalance) (hrightBalance := hrightBalance)
    (firstSupport := firstSupport) (hfirst := hfirst)
    (leftProfiles := leftProfiles) (rightProfiles := rightProfiles)
    (F := F) (choice := choice) (parent := parent) (oldMoving := oldMoving)
    (correction := correction) (hcorr := hcorr) (remaining := remaining) (extra := extra)
    (hextra := hextra) (leftRecipe := leftRecipe) (rightRecipe := rightRecipe)
    (hone := hone) (hroot := hroot) (hemb := hemb) ξ
  have hsourcePair (b : Labels) : family.sourcePair parentWidth b ξ =
      Real.sqrt ((leftFrame b.1).energy ξ) * Real.sqrt ((rightFrame b.2).energy ξ) /
        Z ^ parentWidth := by
    change (Real.sqrt (‖(leftFrame b.1).normalizer‖ ^ 2 *
        (leftFrame b.1).source.energy (σ := σ) ξ) *
      Real.sqrt (‖(rightFrame b.2).normalizer‖ ^ 2 *
        (rightFrame b.2).source.energy (σ := σ) ξ)) / Z ^ parentWidth = _
    rw [← (leftFrame b.1).energy_eq_source, ← (rightFrame b.2).energy_eq_source]
  have hsum : (∑ b : Labels, family.sourcePair parentWidth b ξ) =
      ((∑ b : LeftLabel, Real.sqrt ((leftFrame b).energy ξ)) *
        (∑ b : RightLabel, Real.sqrt ((rightFrame b).energy ξ))) / Z ^ parentWidth := by
    simp only [hsourcePair, Fintype.sum_prod_type, ← Finset.sum_div, Finset.sum_mul_sum]
  have hL := CanonicalLiteralPassiveFrameEnergy.sqrt_passiveColumn_le_frames
    leftAllocation leftTests leftPaid C ordinaryRows (choice.mask extra) firstSign false ξ
  have hR := CanonicalLiteralPassiveFrameEnergy.sqrt_passiveColumn_le_frames
    rightAllocation rightTests rightPaid C ordinaryRows (choice.mask extra) (-firstSign) true ξ
  have hleftSum :
      (∑ b ∈ CanonicalLiteralPassiveNonzero.nonzeroLabels leftTests leftAllocation A
        (choice.mask extra),
        (Real.sqrt ((CanonicalLiteralPassiveFrames.frame leftTests leftAllocation A leftPaid
          C ordinaryRows .left (choice.mask extra) b firstSign false).energy ξ) +
          Real.sqrt ((CanonicalLiteralPassiveFrames.frame leftTests leftAllocation A leftPaid
            C ordinaryRows .left (choice.mask extra) b firstSign true).energy ξ))) =
        ∑ b : LeftLabel, Real.sqrt ((leftFrame b).energy ξ) := by
    rw [Fintype.sum_prod_type, Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b hb
    simp [add_comm]
  have hrightSum :
      (∑ b ∈ CanonicalLiteralPassiveNonzero.nonzeroLabels rightTests rightAllocation A
        (choice.mask extra),
        (Real.sqrt ((CanonicalLiteralPassiveFrames.frame rightTests rightAllocation A rightPaid
          C ordinaryRows .right (choice.mask extra) b (-firstSign) false).energy ξ) +
          Real.sqrt ((CanonicalLiteralPassiveFrames.frame rightTests rightAllocation A rightPaid
            C ordinaryRows .right (choice.mask extra) b (-firstSign) true).energy ξ))) =
        ∑ b : RightLabel, Real.sqrt ((rightFrame b).energy ξ) := by
    rw [Fintype.sum_prod_type, Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b hb
    simp [add_comm]
  change _ ≤ ∑ b ∈ CanonicalLiteralPassiveNonzero.nonzeroLabels
    leftTests leftAllocation A (choice.mask extra), _ at hL
  change _ ≤ ∑ b ∈ CanonicalLiteralPassiveNonzero.nonzeroLabels
    rightTests rightAllocation A (choice.mask extra), _ at hR
  rw [hleftSum] at hL
  rw [hrightSum] at hR
  have hp : passiveIntegrand ξ / Z ^ parentWidth ≤
      ∑ b : Labels, family.sourcePair parentWidth b ξ := by
    rw [hsum]
    apply div_le_div_of_nonneg_right _ (Real.rpow_pos_of_pos hZ parentWidth).le
    exact mul_le_mul hL hR (Real.sqrt_nonneg _)
      (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)
  have hcost : 0 ≤ frozenPair := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ ≤ frozenPair * (passiveIntegrand ξ / Z ^ parentWidth) := by
      convert div_le_div_of_nonneg_right hpre (Real.rpow_pos_of_pos hZ parentWidth).le using 1 <;> ring
    _ ≤ frozenPair * ∑ b : Labels, family.sourcePair parentWidth b ξ :=
      mul_le_mul_of_nonneg_left hp hcost

include hfirst hextra in
/-- Capacity is applied after the actual passive labels have been
constructed. This is the same finite family as in the mass theorem. -/
theorem literalPassiveNormalizedFamily_sourceBound :
    ∀ analyticLeft analyticRight heightLeft heightRight (parentWidth : ℝ)
      (ξ : WithLp 2 (ℝ × ℝ)),
    let family := production analyticLeft analyticRight heightLeft heightRight
    (rectangles).originalIntegrand ξ / Z ^ parentWidth ≤ frozenPair *
      ∑ b : family.active Finset.univ,
        family.weight Finset.univ parentWidth b * family.envelope Finset.univ b ξ *
          family.childPair Finset.univ b ξ := by
  intro analyticLeft analyticRight heightLeft heightRight parentWidth ξ
  let family := production analyticLeft analyticRight heightLeft heightRight
  have hp :=
    v.literalPassiveNormalizedFamily_sourcePairs
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
      (hrightBalance := hrightBalance) (firstSupport := firstSupport) (hfirst := hfirst) (leftProfiles := leftProfiles)
      (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
      (F := F) (choice := choice) (parent := parent)
      (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
      (remaining := remaining) (extra := extra) (hextra := hextra) (leftRecipe := leftRecipe)
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
      analyticLeft analyticRight heightLeft heightRight parentWidth ξ
  exact hp.trans (mul_le_mul_of_nonneg_left
    (family.finite_pointwise Finset.univ parentWidth hZ ξ)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

include hfirst hextra in
/-- The original stored leaf, before its two exact scalar extractions,
already has this same ordinary integrand. The binding contains only
single-coefficient, row and logarithmic-location identities. -/
theorem literalPassiveNormalizedFamily_originalSourcePairs
    (X : (v.leaf exceptional firstKernel x j).ConstantAtomExtraction)
    (binding : X.leaf.OrdinaryBinding rectangles) :
    ∀ analyticLeft analyticRight heightLeft heightRight (parentWidth : ℝ) (z : ℝ × ℝ),
    let family := production analyticLeft analyticRight heightLeft heightRight
    (v.leaf exceptional firstKernel x j).ordinaryIntegrand z / Z ^ parentWidth ≤ frozenPair *
      ∑ b : Labels, family.sourcePair parentWidth b (WithLp.toLp 2 z) := by
  intro analyticLeft analyticRight heightLeft heightRight parentWidth z
  rw [X.ordinaryIntegrand_eq, binding.ordinaryIntegrand_eq]
  exact
    v.literalPassiveNormalizedFamily_sourcePairs
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
      (hrightBalance := hrightBalance) (firstSupport := firstSupport) (hfirst := hfirst) (leftProfiles := leftProfiles)
      (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
      (F := F) (choice := choice) (parent := parent)
      (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
      (remaining := remaining) (extra := extra) (hextra := hextra) (leftRecipe := leftRecipe)
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
      analyticLeft analyticRight heightLeft heightRight parentWidth (WithLp.toLp 2 z)

include hfirst hextra in
/-- The original finite coefficient arrays give integrability under
the two original Fourier kernels. The old frozen factor is included
once in the outer measure used by the passive family. -/
theorem literalPassiveNormalizedFamily_ordinaryCost_le_sourcePairs
    (X : (v.leaf exceptional firstKernel x j).ConstantAtomExtraction)
    (binding : X.leaf.OrdinaryBinding rectangles) :
    ∀ analyticLeft analyticRight heightLeft heightRight (parentWidth : ℝ),
    let family := production analyticLeft analyticRight heightLeft heightRight
    (v.leaf exceptional firstKernel x j).ordinaryCost / Z ^ parentWidth ≤
      ∑ b : Labels, ((v.leaf exceptional firstKernel x j).weight * frozenPair) *
        ∫ z : ℝ × ℝ, family.sourcePair parentWidth b (WithLp.toLp 2 z)
          ∂(v.leaf exceptional firstKernel x j).measure := by
  intro analyticLeft analyticRight heightLeft heightRight parentWidth
  let family := production analyticLeft analyticRight heightLeft heightRight
  let leaf := v.leaf exceptional firstKernel x j
  have hp : ∀ z : ℝ × ℝ, leaf.ordinaryIntegrand z / Z ^ parentWidth ≤
      frozenPair * ∑ b : Labels, family.sourcePair parentWidth b (WithLp.toLp 2 z) :=
    v.literalPassiveNormalizedFamily_originalSourcePairs
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
      (hrightBalance := hrightBalance) (firstSupport := firstSupport) (hfirst := hfirst) (leftProfiles := leftProfiles)
      (rightProfiles := rightProfiles) (hbaseLeft := hbaseLeft) (hbaseRight := hbaseRight)
      (F := F) (choice := choice) (parent := parent)
      (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
      (remaining := remaining) (extra := extra) (hextra := hextra) (leftRecipe := leftRecipe)
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
      X binding analyticLeft analyticRight heightLeft heightRight parentWidth
  have hi (b : Labels) : Integrable
      (fun z : ℝ × ℝ => family.sourcePair parentWidth b (WithLp.toLp 2 z)) leaf.measure :=
    family.sourcePair_nested_integrable leaf.firstKernel leaf.secondKernel parentWidth b
  calc
    _ = leaf.weight * ∫ z, leaf.ordinaryIntegrand z / Z ^ parentWidth ∂leaf.measure := by
      rw [integral_div]
      unfold ActualHybridLeaf.ordinaryCost
      ring
    _ ≤ leaf.weight * ∫ z,
        frozenPair * ∑ b : Labels, family.sourcePair parentWidth b (WithLp.toLp 2 z)
          ∂leaf.measure := by
      apply mul_le_mul_of_nonneg_left _ leaf.weight_nonneg
      apply integral_mono (leaf.ordinaryIntegrand_integrable.div_const _)
        ((integrable_finsetSum Finset.univ (fun b _ => hi b)).const_mul frozenPair)
      exact hp
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun b _ => hi b)]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_sourcePairs
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_sourceBound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_originalSourcePairs
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_ordinaryCost_le_sourcePairs
