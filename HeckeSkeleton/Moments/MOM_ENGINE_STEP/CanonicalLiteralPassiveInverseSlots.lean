import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveCoveredProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveInheritance
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DependentNormalizedFamily

/-!
# Inverse slot characters of the actual passive family

The paid frame calibration retains the original slot characters through
its two literal allocations.  The normalized family then selects one
capacity child before any Fourier variable is evaluated.  These proofs
read that same child and compose its actual retained indices with the
original parent indices.

Only inverse membership for the original parent slots is used.  The raw
calibration identity is proved here from its definition, and no closure
of the finite character set under inversion is required.
-/

set_option autoImplicit false
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

local instance canonicalLiteralPassiveInverseSlotsCircleCharacterFintype :
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
local notation "passiveLeft" => fun b : Labels =>
  CanonicalLiteralPassiveSource.branch leftTests leftAllocation A (choice.mask extra) b.1.1.val
local notation "passiveRight" => fun b : Labels =>
  CanonicalLiteralPassiveSource.branch rightTests rightAllocation A (choice.mask extra) b.2.1.val
/-- Every slot of the already chosen left child inherits inverse
membership from its original parent slot. -/
theorem literalPassiveNormalizedFamily_left_slot_inverse_mem_theta
    (hinverse : ∀ i, (parent.slotCoefficient i)⁻¹ ∈ parent.theta) :
    ∀ analyticLeft analyticRight heightLeft heightRight,
      ∀ (b : (production analyticLeft analyticRight heightLeft heightRight).active Finset.univ)
        (ξ : WithLp 2 (ℝ × ℝ))
        (i : Fin ((production analyticLeft analyticRight heightLeft heightRight).leftData Finset.univ b ξ).geometry.slotCount),
        (((production analyticLeft analyticRight heightLeft heightRight).leftData Finset.univ b ξ).slotCoefficient i)⁻¹ ∈
            ((production analyticLeft analyticRight heightLeft heightRight).leftData Finset.univ b ξ).theta := by
  intro analyticLeft analyticRight heightLeft heightRight b ξ i
  let family := production analyticLeft analyticRight heightLeft heightRight
  have hdata (z : WithLp 2 (ℝ × ℝ)) :
      (family.leftCalibration b.val).data z =
        CanonicalLiteralAllocatedData.data P Rchar
          (CanonicalLiteralPassiveSource.profiles leftTests leftAllocation A leftPaid)
          (passiveLeft b.val) choice.phases parent oldMoving correction hcorr C
          (ordinaryRows).primes (ordinaryRows).leftMultiplicity (ordinaryRows).rightMultiplicity
          pattern sector remaining 1 m q
          (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
          (fun s => leftRecipe.slots.index (SlotRestriction.index (leftAllocation).keep s))
          b.val.1.2 firstSign false z := rfl
  exact CanonicalLiteralPassiveInheritance.frozen_slot_inverse_mem_theta P Rchar
    (CanonicalLiteralPassiveSource.profiles leftTests leftAllocation A leftPaid)
    (passiveLeft b.val) choice.phases parent oldMoving correction hcorr C
    (ordinaryRows).primes (ordinaryRows).leftMultiplicity (ordinaryRows).rightMultiplicity
    pattern sector remaining 1 m q
    (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
    (fun s => leftRecipe.slots.index (SlotRestriction.index (leftAllocation).keep s))
    b.val.1.2 firstSign false (family.leftChild Finset.univ b) hdata hinverse ξ i

/-- The negative Fourier side retains its original slot characters as
well; it does not replace them by inverse characters. -/
theorem literalPassiveNormalizedFamily_right_slot_inverse_mem_theta
    (hinverse : ∀ i, (parent.slotCoefficient i)⁻¹ ∈ parent.theta) :
    ∀ analyticLeft analyticRight heightLeft heightRight,
      ∀ (b : (production analyticLeft analyticRight heightLeft heightRight).active Finset.univ)
        (ξ : WithLp 2 (ℝ × ℝ))
        (i : Fin ((production analyticLeft analyticRight heightLeft heightRight).rightData Finset.univ b ξ).geometry.slotCount),
        (((production analyticLeft analyticRight heightLeft heightRight).rightData Finset.univ b ξ).slotCoefficient i)⁻¹ ∈
            ((production analyticLeft analyticRight heightLeft heightRight).rightData Finset.univ b ξ).theta := by
  intro analyticLeft analyticRight heightLeft heightRight b ξ i
  let family := production analyticLeft analyticRight heightLeft heightRight
  have hdata (z : WithLp 2 (ℝ × ℝ)) :
      (family.rightCalibration b.val).data z =
        CanonicalLiteralAllocatedData.data P Rchar
          (CanonicalLiteralPassiveSource.profiles rightTests rightAllocation A rightPaid)
          (passiveRight b.val) choice.phases parent oldMoving correction hcorr C
          (ordinaryRows).primes (ordinaryRows).leftMultiplicity (ordinaryRows).rightMultiplicity
          pattern sector remaining 1 m q
          (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
          (fun s => rightRecipe.slots.index (SlotRestriction.index (rightAllocation).keep s))
          b.val.2.2 (-firstSign) true z := rfl
  exact CanonicalLiteralPassiveInheritance.frozen_slot_inverse_mem_theta P Rchar
    (CanonicalLiteralPassiveSource.profiles rightTests rightAllocation A rightPaid)
    (passiveRight b.val) choice.phases parent oldMoving correction hcorr C
    (ordinaryRows).primes (ordinaryRows).leftMultiplicity (ordinaryRows).rightMultiplicity
    pattern sector remaining 1 m q
    (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
    (fun s => rightRecipe.slots.index (SlotRestriction.index (rightAllocation).keep s))
    b.val.2.2 (-firstSign) true (family.rightChild Finset.univ b) hdata hinverse ξ i

end ActualGaussStage.CoveredClassKey

namespace ActualNormalizedPairFamily

section BaseTransport

variable {ω ψ : HeckeCharacter K}
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z)
variable (labels : Finset Λ) (base : ℝ) (sameBase : Z = base)

/-- Changing only the base equality proof preserves the same left child. -/
theorem atBase_left_slot_inverse_mem_theta
    (hinverse : ∀ (b : family.active labels) (ξ : V)
      (i : Fin (family.leftData labels b ξ).geometry.slotCount),
      ((family.leftData labels b ξ).slotCoefficient i)⁻¹ ∈
        (family.leftData labels b ξ).theta)
    (b : family.active labels) (ξ : V)
    (i : Fin ((family.atBase base sameBase).leftData labels b ξ).geometry.slotCount) :
    (((family.atBase base sameBase).leftData labels b ξ).slotCoefficient i)⁻¹ ∈
      ((family.atBase base sameBase).leftData labels b ξ).theta :=
  hinverse b ξ i

/-- Changing only the base equality proof preserves the same right child. -/
theorem atBase_right_slot_inverse_mem_theta
    (hinverse : ∀ (b : family.active labels) (ξ : V)
      (i : Fin (family.rightData labels b ξ).geometry.slotCount),
      ((family.rightData labels b ξ).slotCoefficient i)⁻¹ ∈
        (family.rightData labels b ξ).theta)
    (b : family.active labels) (ξ : V)
    (i : Fin ((family.atBase base sameBase).rightData labels b ξ).geometry.slotCount) :
    (((family.atBase base sameBase).rightData labels b ξ).slotCoefficient i)⁻¹ ∈
      ((family.atBase base sameBase).rightData labels b ξ).theta :=
  hinverse b ξ i

end BaseTransport

section SigmaTransport

variable {ω ψ : HeckeCharacter K}
variable {V J : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Λ : J → Type*} {Z : ℝ}
variable (families : ∀ j, ActualNormalizedPairFamily A σ V (Λ j) ω ψ Z)
variable (outer : Finset J) (labels : ∀ j, Finset (Λ j))

/-- The sigma family uses the original inner label and its same left child. -/
theorem sigmaCombine_left_slot_inverse_mem_theta
    (hinverse : ∀ j ∈ outer, ∀ (b : (families j).active (labels j)) (ξ : V)
      (i : Fin ((families j).leftData (labels j) b ξ).geometry.slotCount),
      (((families j).leftData (labels j) b ξ).slotCoefficient i)⁻¹ ∈
        ((families j).leftData (labels j) b ξ).theta)
    (b : (sigmaCombine families).active (outer.sigma labels)) (ξ : V)
    (i : Fin ((sigmaCombine families).leftData (outer.sigma labels) b ξ).geometry.slotCount) :
    (((sigmaCombine families).leftData (outer.sigma labels) b ξ).slotCoefficient i)⁻¹ ∈
      ((sigmaCombine families).leftData (outer.sigma labels) b ξ).theta :=
  hinverse b.val.1 (sigmaActiveOuter families outer labels b).property
    (sigmaActiveInner families outer labels b) ξ i

/-- The sigma family uses the original inner label and its same right child. -/
theorem sigmaCombine_right_slot_inverse_mem_theta
    (hinverse : ∀ j ∈ outer, ∀ (b : (families j).active (labels j)) (ξ : V)
      (i : Fin ((families j).rightData (labels j) b ξ).geometry.slotCount),
      (((families j).rightData (labels j) b ξ).slotCoefficient i)⁻¹ ∈
        ((families j).rightData (labels j) b ξ).theta)
    (b : (sigmaCombine families).active (outer.sigma labels)) (ξ : V)
    (i : Fin ((sigmaCombine families).rightData (outer.sigma labels) b ξ).geometry.slotCount) :
    (((sigmaCombine families).rightData (outer.sigma labels) b ξ).slotCoefficient i)⁻¹ ∈
      ((sigmaCombine families).rightData (outer.sigma labels) b ξ).theta :=
  hinverse b.val.1 (sigmaActiveOuter families outer labels b).property
    (sigmaActiveInner families outer labels b) ξ i

end SigmaTransport
end ActualNormalizedPairFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_left_slot_inverse_mem_theta
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_right_slot_inverse_mem_theta
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.atBase_left_slot_inverse_mem_theta
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.atBase_right_slot_inverse_mem_theta
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_left_slot_inverse_mem_theta
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_right_slot_inverse_mem_theta
