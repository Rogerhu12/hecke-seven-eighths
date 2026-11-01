import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveParentGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedRecipe
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalMovingFactorAppend
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingOriginalArithmeticAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActiveNormalizedFamily

/-!
# Original output dictionaries of the same passive normalized family

The raw recipes, original background characters, frozen norm tests and
occurrence embeddings are constructed on the already stored calibrations.
The full joint budget is their literal allowed-row predicate. Its exact
mask recipe proves ordinary engine admissibility of the same children.

The displayed moving-support budget is required only on the original
active carrier. Such a label supplies an actual nonzero correlation row,
which identifies its previously fixed frequency pattern. The active
filter is idempotent and changes no capacity, selected child or kernel.
Inactive zero-correlation labels are not assigned a false support bound.
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

section RawOutput

namespace ActualNormalizedPairFamily

variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}

/-- A computed raw dictionary bundle. The literal constructor below
builds these fields; none is a new premise on a selected child. -/
structure RawMovingOutputData (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z)
    (labels : Finset Λ) (parent : MomentData K ω ψ) where
  left : ∀ b ∈ labels, CompleteMovingRowRecipe A P R (family.leftCalibration b).data
  right : ∀ b ∈ labels, CompleteMovingRowRecipe A P R (family.rightCalibration b).data
  left_full : ∀ b (hb : b ∈ labels), (left b hb).FullJointBudget Z
    ((family.leftCalibration b).parameters.m + (family.leftCalibration b).parameters.q)
  right_full : ∀ b (hb : b ∈ labels), (right b hb).FullJointBudget Z
    ((family.rightCalibration b).parameters.m + (family.rightCalibration b).parameters.q)
  characters : family.ParentCharacterInputs labels parent
  profiles : family.NormProfileInputs labels
  slots : family.ParentSlotDictionaries labels parent

namespace RawMovingOutputData

variable {family : ActualNormalizedPairFamily A σ V Λ ω ψ Z} {labels : Finset Λ}
variable {parent : MomentData K ω ψ}
variable (raw : family.RawMovingOutputData (P := P) (R := R) labels parent)

/-- Actual single-ideal and single-prime atoms follow from the same
complete moving recipe, without a separate arithmetic input. -/
def arithmeticInputs : family.ArithmeticAtomInputs labels
    (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) where
  left b hb ξ := (raw.left b hb).arithmeticAtoms ξ
  right b hb ξ := (raw.right b hb).arithmeticAtoms ξ

/-- Restrict only the input label proofs. All raw data remain identical. -/
def onActive : family.RawMovingOutputData (P := P) (R := R) (family.active labels) parent where
  left b hb := raw.left b (Finset.mem_filter.mp hb).1
  right b hb := raw.right b (Finset.mem_filter.mp hb).1
  left_full b hb := raw.left_full b (Finset.mem_filter.mp hb).1
  right_full b hb := raw.right_full b (Finset.mem_filter.mp hb).1
  characters := {
    left := fun b hb => raw.characters.left b (Finset.mem_filter.mp hb).1
    right := fun b hb => raw.characters.right b (Finset.mem_filter.mp hb).1 }
  profiles := {
    left := fun b hb => raw.profiles.left b (Finset.mem_filter.mp hb).1
    right := fun b hb => raw.profiles.right b (Finset.mem_filter.mp hb).1 }
  slots := {
    left := fun b hb => raw.slots.left b (Finset.mem_filter.mp hb).1
    right := fun b hb => raw.slots.right b (Finset.mem_filter.mp hb).1 }

/-- The two displayed-support estimates complete the existing input
record. They will be proved from an actual active row below. -/
def movingRowInputs
    (hleft : ∀ b (hb : b ∈ labels), (raw.left b hb).SupportBudget Z
      (family.leftCalibration b).parameters.q)
    (hright : ∀ b (hb : b ∈ labels), (raw.right b hb).SupportBudget Z
      (family.rightCalibration b).parameters.q) :
    family.MovingRowInputs (P := P) (R := R) labels where
  left := raw.left
  right := raw.right
  left_support := hleft
  right_support := hright
  left_full := raw.left_full
  right_full := raw.right_full

variable {a : RealParameters} {step : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {window : Set ℝ} {orders : Finset (ℕ × ℕ)}

/-- The full Boolean mask and all allowed rows survive exactly through
normalization and the same selected capacity deletion. -/
def outputGeometry (G : family.ParentGeometry labels parent a step)
    (windows : ∀ b : family.active labels, ∀ ξ : V,
      InFixedProfileWindow rowDomain Set.univ window orders (family.leftData labels b ξ) ∧
      InFixedProfileWindow rowDomain Set.univ window orders (family.rightData labels b ξ)) :
    family.OutputGeometry labels parent a step rowDomain window orders := by
  have leftMask (b : family.active labels) (ξ : V) :
      ActualRowMaskAdmissible A (family.leftData labels b ξ)
        (family.leftParameters labels b) Z := by
    let Q := raw.left b.val (Finset.mem_filter.mp b.property).1
    have h := (family.leftChild labels b).rowMaskAdmissible Q.effectiveMovingMaskRecipe
      (by
        intro z u hu
        rw [family.left_base b.val]
        exact Q.effectiveMovingMaskRecipe_jointBudget Z _
          (raw.left_full b.val (Finset.mem_filter.mp b.property).1) z u hu) ξ
    simpa only [family.left_base b.val] using h
  have rightMask (b : family.active labels) (ξ : V) :
      ActualRowMaskAdmissible A (family.rightData labels b ξ)
        (family.rightParameters labels b) Z := by
    let Q := raw.right b.val (Finset.mem_filter.mp b.property).1
    have h := (family.rightChild labels b).rowMaskAdmissible Q.effectiveMovingMaskRecipe
      (by
        intro z u hu
        rw [family.right_base b.val]
        exact Q.effectiveMovingMaskRecipe_jointBudget Z _
          (raw.right_full b.val (Finset.mem_filter.mp b.property).1) z u hu) ξ
    simpa only [family.right_base b.val] using h
  exact {
    left_width := G.left_width
    right_width := G.right_width
    left_width_nonneg := fun b => (family.left_parameters_nonneg labels b).1
    right_width_nonneg := fun b => (family.right_parameters_nonneg labels b).1
    left_plain_left_nonneg := fun b => (family.left_parameters_nonneg labels b).2.1
    left_plain_right_nonneg := fun b => (family.left_parameters_nonneg labels b).2.2
    right_plain_left_nonneg := fun b => (family.right_parameters_nonneg labels b).2.1
    right_plain_right_nonneg := fun b => (family.right_parameters_nonneg labels b).2.2
    left_length := fun b ξ => (family.actual_total_lengths labels b ξ).1
    right_length := fun b ξ => (family.actual_total_lengths labels b ξ).2
    left_kappa := G.left_kappa_eq
    right_kappa := G.right_kappa_eq
    left_slots := G.left_slot_count
    right_slots := G.right_slot_count
    left_theta := G.left_theta_eq
    right_theta := G.right_theta_eq
    left_slot_characters := G.left_character
    right_slot_characters := G.right_character
    left_admissible := fun b ξ => ⟨(windows b ξ).1, leftMask b ξ⟩
    right_admissible := fun b ξ => ⟨(windows b ξ).2, rightMask b ξ⟩
    left_capacity := fun b => (family.leftChild labels b).capacity
    right_capacity := fun b => (family.rightChild labels b).capacity }

end RawMovingOutputData

/-- The parent identities restrict to exactly the same active labels. -/
theorem ParentGeometry.onActive {family : ActualNormalizedPairFamily A σ V Λ ω ψ Z}
    {labels : Finset Λ} {parent : MomentData K ω ψ} {a : RealParameters} {step : ℝ}
    (G : family.ParentGeometry labels parent a step) :
    family.ParentGeometry (family.active labels) parent a step where
  left_parent b hb := G.left_parent b (Finset.mem_filter.mp hb).1
  right_parent b hb := G.right_parent b (Finset.mem_filter.mp hb).1
  left_gap b hb := G.left_gap b (Finset.mem_filter.mp hb).1
  right_gap b hb := G.right_gap b (Finset.mem_filter.mp hb).1
  left_kappa b hb := G.left_kappa b (Finset.mem_filter.mp hb).1
  right_kappa b hb := G.right_kappa b (Finset.mem_filter.mp hb).1
  left_slots b hb := G.left_slots b (Finset.mem_filter.mp hb).1
  right_slots b hb := G.right_slots b (Finset.mem_filter.mp hb).1
  left_theta b hb := G.left_theta b (Finset.mem_filter.mp hb).1
  right_theta b hb := G.right_theta b (Finset.mem_filter.mp hb).1

end ActualNormalizedPairFamily
end RawOutput

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

local instance canonicalLiteralPassiveOutputInputsCircleCharacterFintype :
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

local notation "Labels" => CanonicalLiteralPassiveNormalizedFamily.PairLabel (A := A)
  leftTests rightTests leftAllocation rightAllocation (choice.mask extra) (choice.mask extra)

local notation "leftPassiveTests" =>
  CanonicalLiteralPassiveSource.profiles leftTests leftAllocation A leftPaid
local notation "rightPassiveTests" =>
  CanonicalLiteralPassiveSource.profiles rightTests rightAllocation A rightPaid
local notation "leftPassiveAllocation" => fun b : Labels =>
  CanonicalLiteralPassiveSource.branch leftTests leftAllocation A (choice.mask extra) b.1.1.val
local notation "rightPassiveAllocation" => fun b : Labels =>
  CanonicalLiteralPassiveSource.branch rightTests rightAllocation A (choice.mask extra) b.2.1.val
local notation "inverse" => CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time
local notation "leftIndex" => fun i => leftRecipe.slots.index (SlotRestriction.index leftAllocation.keep i)
local notation "rightIndex" => fun i => rightRecipe.slots.index (SlotRestriction.index rightAllocation.keep i)

/-- Every raw field is computed from the original paid phase dictionary,
frozen norm tests and the two literal allocation keep maps. The full
budget is the actual allowed-row predicate, for every label. -/
def literalPassiveNormalizedFamily_rawOutputData :=
  fun analyticLeft analyticRight heightLeft heightRight =>
    show (production analyticLeft analyticRight heightLeft heightRight).RawMovingOutputData
      (P := P) (R := Rchar) Finset.univ parent from by
      let family := production analyticLeft analyticRight heightLeft heightRight
      let leftRaw (b : Labels) :
          CompleteMovingRowRecipe A P Rchar (family.leftCalibration b).data :=
        CanonicalLiteralAllocatedData.recipe P Rchar leftPassiveTests (leftPassiveAllocation b)
          choice.phases parent oldMoving correction hcorr C ordinaryRows.primes
          ordinaryRows.leftMultiplicity ordinaryRows.rightMultiplicity pattern sector remaining 1
          m q inverse leftIndex b.1.2 firstSign false
      let rightRaw (b : Labels) :
          CompleteMovingRowRecipe A P Rchar (family.rightCalibration b).data :=
        CanonicalLiteralAllocatedData.recipe P Rchar rightPassiveTests (rightPassiveAllocation b)
          choice.phases parent oldMoving correction hcorr C ordinaryRows.primes
          ordinaryRows.leftMultiplicity ordinaryRows.rightMultiplicity pattern sector remaining 1
          m q inverse rightIndex b.2.2 (-firstSign) true
      refine {
        left := fun b _ => leftRaw b
        right := fun b _ => rightRaw b
        left_full := ?_
        right_full := ?_
        characters := ?_
        profiles := ?_
        slots := ?_ }
      · intro b _ ξ u hu
        change idealNorm K u * idealNorm K
          ((leftRaw b).moving.fullMaskSupport (leftRaw b).remaining) ≤ Z ^ (m + q)
        have h : idealNorm K u * idealNorm K
            ((leftRaw b).moving.fullMaskSupport (leftRaw b).remaining) ≤
              leftTable.base ^ (m + q) := hu.2
        have hb : leftTable.base = Z := hbaseLeft
        simpa only [hb] using h
      · intro b _ ξ u hu
        change idealNorm K u * idealNorm K
          ((rightRaw b).moving.fullMaskSupport (rightRaw b).remaining) ≤ Z ^ (m + q)
        have h : idealNorm K u * idealNorm K
            ((rightRaw b).moving.fullMaskSupport (rightRaw b).remaining) ≤
              rightTable.base ^ (m + q) := hu.2
        have hb : rightTable.base = Z := hbaseRight
        simpa only [hb] using h
      · constructor
        · intro b _
          exact ⟨false, ((family.leftCalibration b).data 0).rowCharacter,
            ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩
        · intro b _
          exact ⟨false, ((family.rightCalibration b).data 0).rowCharacter,
            ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩
      · exact {
          left := fun b _ => CanonicalLiteralAllocatedData.normProfiles P Rchar
            leftPassiveTests (leftPassiveAllocation b) choice.phases parent oldMoving correction
            hcorr C ordinaryRows.primes ordinaryRows.leftMultiplicity ordinaryRows.rightMultiplicity
            pattern sector remaining 1 m q inverse leftIndex b.1.2 firstSign false
          right := fun b _ => CanonicalLiteralAllocatedData.normProfiles P Rchar
            rightPassiveTests (rightPassiveAllocation b) choice.phases parent oldMoving correction
            hcorr C ordinaryRows.primes ordinaryRows.leftMultiplicity ordinaryRows.rightMultiplicity
            pattern sector remaining 1 m q inverse rightIndex b.2.2 (-firstSign) true }
      · exact {
          left := fun b _ => CanonicalLiteralPassiveFrames.frameOriginalSlots
            leftTests leftAllocation A leftPaid C ordinaryRows .left (choice.mask extra)
            b.1.1.val firstSign b.1.2 parent leftRecipe.slots
          right := fun b _ => CanonicalLiteralPassiveFrames.frameOriginalSlots
            rightTests rightAllocation A rightPaid C ordinaryRows .right (choice.mask extra)
            b.2.1.val (-firstSign) b.2.2 parent rightRecipe.slots }

local notation "rawOutput" =>
  v.literalPassiveNormalizedFamily_rawOutputData
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

local notation "originalParentGeometry" =>
  v.literalPassiveNormalizedFamily_parentGeometry
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

local notation "originalWindow" =>
  v.literalPassiveNormalizedFamily_in_fixed_window
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

local notation "activeRows" =>
  v.literalPassiveNormalizedFamily_activeRows_nonempty
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

/-- An active passive source supplies a genuine nonzero original
correlation row. The previously fixed frequency pattern then pays the
displayed support, including the complete sixth-root charge. -/
theorem literalPassiveNormalizedFamily_active_support :
    ∀ analyticLeft analyticRight heightLeft heightRight
      (b : (production analyticLeft analyticRight heightLeft heightRight).active Finset.univ),
      A.exteriorNorm
        ((choice.phases.moving P Rchar oldMoving).appendSecondFactor C v.block.primes
          v.block.leftMultiplicity v.block.rightMultiplicity pattern).support ≤ Z ^ q := by
  intro analyticLeft analyticRight heightLeft heightRight b
  obtain ⟨anchor⟩ := activeRows analyticLeft analyticRight heightLeft heightRight b
  let S := v.chart.actualRows ∅ cutoff hcutoff v.rowLabel
  have hrow : anchor.val ∈ S.rows :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp anchor.property).1).1
  have hcorrelation : S.correlation anchor.val ≠ 0 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp anchor.property).1).2
  let live : S.live := ⟨anchor.val, Finset.mem_filter.mpr ⟨hrow, hcorrelation⟩⟩
  have hclass : v.chart.NonunitLabelStable :=
    ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_nonunitLabelStable
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad v.1 v.2.1
  let hp := v.chart.originalNonunitClass hclass ∅ cutoff hcutoff v.rowLabel live
  let paid := choice.phases.moving P Rchar oldMoving
  let W := S.appendedNonunitClassSupportAtoms paid remaining C
    v.block.left_positive v.block.right_positive pattern hp
  have hunitNorm :
      A.exteriorNorm (unitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity
        (S.frequency hp.val.val)) ≤ Z ^ geometry.skeleton.t₂ := by
    rw [← S.secondPatternUnitIdeal_eq_live C pattern hp.val hp.property]
    change (Ideal.absNorm (secondPatternUnitIdeal v.block.primes v.block.leftMultiplicity
      v.block.rightMultiplicity pattern).val : ℝ) ≤ Z ^ idealLogLength Z geometry.ideals.unitPart.val
    rw [← hunit]
    exact (rpow_idealLogLength Z domain.scale _
      (nonZeroDivisors.coe_ne_zero geometry.ideals.unitPart)).symm.le
  have hnonunitNorm :
      A.exteriorNorm (nonunitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity
        (S.frequency hp.val.val)) ≤ Z ^ geometry.skeleton.V := by
    rw [← S.secondPatternNonunitIdeal_eq C pattern hp.val.val hp.property]
    change (Ideal.absNorm (secondPatternNonunitIdeal v.block.primes pattern).val : ℝ) ≤
      Z ^ idealLogLength Z geometry.ideals.nonunitPart.val
    rw [← hnonunit]
    exact (rpow_idealLogLength Z domain.scale _
      (nonZeroDivisors.coe_ne_zero geometry.ideals.nonunitPart)).symm.le
  have hold : A.exteriorNorm (ExteriorIdealEuler.mul (paid.effectiveFullSupport remaining)
      (secondSixthRootIdeal S.primes S.leftMultiplicity S.rightMultiplicity)) ≤
      Z ^ (geometry.supportCenter + rootLength) :=
    secondOldWithSixthRoot_norm_window S.primes S.leftMultiplicity S.rightMultiplicity
      (paid.effectiveFullSupport remaining) Z geometry.supportCenter domain.scale hpaidSupport
  have h := W.support_norm_window Z (geometry.supportCenter + rootLength)
    geometry.skeleton.t₂ geometry.skeleton.V (zero_lt_one.trans domain.scale)
    hold hunitNorm hnonunitNorm
  exact h.trans_eq (congrArg (fun t : ℝ => Z ^ t) (by
    dsimp only [OriginalNominalGeometry.literalSupportParameter]
    ring))

local notation "activeSupport" =>
  v.literalPassiveNormalizedFamily_active_support
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

/-- The existing moving-input record is constructed on the exact active
labels. No support estimate is asserted for an inactive correlation. -/
def literalPassiveNormalizedFamily_movingInputs :=
  fun analyticLeft analyticRight heightLeft heightRight =>
    show (production analyticLeft analyticRight heightLeft heightRight).MovingRowInputs
      (P := P) (R := Rchar)
      ((production analyticLeft analyticRight heightLeft heightRight).active Finset.univ) from by
      let raw := (rawOutput analyticLeft analyticRight heightLeft heightRight).onActive
      apply raw.movingRowInputs
      · intro b hb
        change A.exteriorNorm
          ((choice.phases.moving P Rchar oldMoving).appendSecondFactor C v.block.primes
            v.block.leftMultiplicity v.block.rightMultiplicity pattern).support ≤ Z ^ q
        exact activeSupport analyticLeft analyticRight heightLeft heightRight ⟨b, hb⟩
      · intro b hb
        change A.exteriorNorm
          ((choice.phases.moving P Rchar oldMoving).appendSecondFactor C v.block.primes
            v.block.leftMultiplicity v.block.rightMultiplicity pattern).support ≤ Z ^ q
        exact activeSupport analyticLeft analyticRight heightLeft heightRight ⟨b, hb⟩

/-- The four remaining input dictionaries hold even before activity
is tested. Their active restrictions are the ones used with movingInputs. -/
def literalPassiveNormalizedFamily_parentCharacterInputs :=
  fun analyticLeft analyticRight heightLeft heightRight =>
    (rawOutput analyticLeft analyticRight heightLeft heightRight).characters

def literalPassiveNormalizedFamily_normProfileInputs :=
  fun analyticLeft analyticRight heightLeft heightRight =>
    (rawOutput analyticLeft analyticRight heightLeft heightRight).profiles

def literalPassiveNormalizedFamily_arithmeticAtomInputs :=
  fun analyticLeft analyticRight heightLeft heightRight =>
    (rawOutput analyticLeft analyticRight heightLeft heightRight).arithmeticInputs

def literalPassiveNormalizedFamily_parentSlotDictionaries :=
  fun analyticLeft analyticRight heightLeft heightRight =>
    (rawOutput analyticLeft analyticRight heightLeft heightRight).slots

/-- Ordinary engine geometry holds on the original active children.
The mask field is constructed from the complete paid recipe itself. -/
def literalPassiveNormalizedFamily_outputGeometry :=
  fun analyticLeft analyticRight heightLeft heightRight =>
    (rawOutput analyticLeft analyticRight heightLeft heightRight).outputGeometry
      (originalParentGeometry analyticLeft analyticRight heightLeft heightRight)
      (originalWindow analyticLeft analyticRight heightLeft heightRight)

/-- The active-only input record uses precisely the same selected
children, so its ordinary geometry is the exact restriction above. -/
def literalPassiveNormalizedFamily_activeOutputGeometry :=
  fun analyticLeft analyticRight heightLeft heightRight =>
    (rawOutput analyticLeft analyticRight heightLeft heightRight).onActive.outputGeometry
      (originalParentGeometry analyticLeft analyticRight heightLeft heightRight).onActive
      (fun b ξ => originalWindow analyticLeft analyticRight heightLeft heightRight
        ((production analyticLeft analyticRight heightLeft heightRight).activeActiveEquiv
          Finset.univ b) ξ)

local notation "activeMoving" =>
  v.literalPassiveNormalizedFamily_movingInputs
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

local notation "activeGeometry" =>
  v.literalPassiveNormalizedFamily_activeOutputGeometry
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

/-- All five original input records are available on the same exact
active labels used by movingInputs. -/
def literalPassiveNormalizedFamily_activeParentCharacterInputs :=
  fun analyticLeft analyticRight heightLeft heightRight =>
    (rawOutput analyticLeft analyticRight heightLeft heightRight).onActive.characters

def literalPassiveNormalizedFamily_activeNormProfileInputs :=
  fun analyticLeft analyticRight heightLeft heightRight =>
    (rawOutput analyticLeft analyticRight heightLeft heightRight).onActive.profiles

def literalPassiveNormalizedFamily_activeArithmeticAtomInputs :=
  fun analyticLeft analyticRight heightLeft heightRight =>
    (rawOutput analyticLeft analyticRight heightLeft heightRight).onActive.arithmeticInputs

def literalPassiveNormalizedFamily_activeParentSlotDictionaries :=
  fun analyticLeft analyticRight heightLeft heightRight =>
    (rawOutput analyticLeft analyticRight heightLeft heightRight).onActive.slots

/-- These are the original active children, rather than children of a
newly selected family. The exact active equivalence changes only proofs. -/
theorem literalPassiveNormalizedFamily_moving_admissible :
    ∀ analyticLeft analyticRight heightLeft heightRight
      (b : (production analyticLeft analyticRight heightLeft heightRight).active Finset.univ)
      (ξ : WithLp 2 (ℝ × ℝ)),
      MovingEngineChildAdmissible A P Rchar
          (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) parent
          Set.univ (Set.Icc (0 : ℝ) hi) orders Z
          ((production analyticLeft analyticRight heightLeft heightRight).leftData Finset.univ b ξ)
          ((production analyticLeft analyticRight heightLeft heightRight).leftParameters Finset.univ b) ∧
        MovingEngineChildAdmissible A P Rchar
          (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) parent
          Set.univ (Set.Icc (0 : ℝ) hi) orders Z
          ((production analyticLeft analyticRight heightLeft heightRight).rightData Finset.univ b ξ)
          ((production analyticLeft analyticRight heightLeft heightRight).rightParameters Finset.univ b) := by
  intro analyticLeft analyticRight heightLeft heightRight b ξ
  let family := production analyticLeft analyticRight heightLeft heightRight
  let raw := (rawOutput analyticLeft analyticRight heightLeft heightRight).onActive
  let b' := (family.activeActiveEquiv Finset.univ).symm b
  let geometry' := activeGeometry analyticLeft analyticRight heightLeft heightRight
  let moving := activeMoving analyticLeft analyticRight heightLeft heightRight
  exact ⟨ActualNormalizedPairFamily.moving_left_admissible geometry' moving
      raw.characters raw.profiles raw.arithmeticInputs raw.slots b' ξ,
    ActualNormalizedPairFamily.moving_right_admissible geometry' moving
      raw.characters raw.profiles raw.arithmeticInputs raw.slots b' ξ⟩

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.RawMovingOutputData.arithmeticInputs
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.RawMovingOutputData.outputGeometry
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_rawOutputData
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_active_support
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_movingInputs
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_parentCharacterInputs
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_normProfileInputs
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_arithmeticAtomInputs
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_parentSlotDictionaries
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_outputGeometry
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_activeOutputGeometry
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamily_moving_admissible
