import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedLiteralProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralRowProfileBound
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AnalyticChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedFamilyAdapter

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false

/-!
# One actual family constructor for all physical source branches

The physical validity record contains only original column dictionaries,
support and numerical windows. The normalized profiles, passive labels,
capacity choices and common Fourier measure are computed below. No
output moment estimate or completed normalized family is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep EngineInduction
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

attribute [local instance]
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  selectedPrincipal selectedComplex selectedNormOneSpace selectedNormOneBorel
  selectedInfinityUnitSpace selectedInfinityUnitBorel selectedLocalUnitSpace selectedLocalUnitBorel

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

local instance familyCircleFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace SelectedLeafPacket

variable {request : Request c frame Cp Hp hCp hminimum hHp} {frequency : ℝ × ℝ}
variable {leaf : ActualHybridLeaf K (ActualSIntegerOrbit K (places K c)) ℝ ℝ}
variable (p : SelectedLeafPacket request frequency leaf)

local notation "parent" => (SelectedSource.model request frequency).data
local notation "parameters" => SelectedSource.parameters request frequency
local notation "recipe" => SelectedSource.recipe request frequency
local notation "box" => selectedBox c frame
local notation "chart" => ActualGaussStage.CoveredClassKey.chart p.key
local notation "block" => ActualGaussStage.CoveredClassKey.block p.key
local notation "label" => ActualGaussStage.CoveredClassKey.rowLabel p.key
local notation "cutoff" => box.secondCutoff request.base
local notation "hcutoff" => box.secondCutoff_ge_one (SelectedSource.base_gt_one request).le
local notation "pattern" => SecondBlockProfileChart.originalNonunitPattern chart ∅ cutoff hcutoff label
local notation "sector" => SecondBlockProfileChart.originalSector chart (probeData K c) ∅ cutoff hcutoff label
local notation "bare" => ActualGaussStage.CoveredClassKey.leaf p.key p.exceptional p.firstKernel p.location p.allocation

/-- This record is checked on original finite sources. None of its
fields mentions normalized children, kernels or a moment inequality. -/
structure Valid : Prop where
  physicalRows : p.physical.source.rows.Nonempty
  firstSign : p.firstSign = 1 ∨ p.firstSign = -1
  leftCoefficient : ∀ i ∈ (p.cover.branch p.key.2.2.1).reindex.cartesian,
    (p.cover.branch p.key.2.2.1).reindex.index i ∈ block.leftColumns p.physical.source.columns →
      chart.sourceLeftCoefficient ((p.cover.branch p.key.2.2.1).reindex.index i) =
        (p.firstAtoms false).whole i
  rightCoefficient : ∀ i ∈ (p.cover.branch p.key.2.2.2.1).reindex.cartesian,
    (p.cover.branch p.key.2.2.2.1).reindex.index i ∈ block.rightColumns p.physical.source.columns →
      chart.sourceRightCoefficient ((p.cover.branch p.key.2.2.2.1).reindex.index i) =
        (p.firstAtoms true).whole i
  leftCharacters : (ActualGaussStage.CoveredClassKey.literalLeftAtoms p.key (p.firstAtoms false)).characters =
    CanonicalLiteralPhaseCalibration.sourceCharacters (probeData K c) (momentRowCharacters K c)
      p.leftInput.phases parent recipe.moving recipe.correction recipe.remaining
      p.leftInput.deletion p.leftSlots.index
  rightCharacters : (ActualGaussStage.CoveredClassKey.literalRightAtoms p.key (p.firstAtoms true)).characters =
    CanonicalLiteralPhaseCalibration.sourceCharacters (probeData K c) (momentRowCharacters K c)
      p.leftInput.phases parent recipe.moving recipe.correction recipe.remaining
      p.leftInput.deletion p.rightSlots.index
  columns : ∀ i ∈ p.physical.source.columns, p.physical.source.coefficient i ≠ 0 →
    (TargetArithmetic.arithmetic c).exteriorNorm (p.physical.source.ideal i) ≤
      request.base ^ (p.geometry.skeleton.A - p.geometry.skeleton.c - p.geometry.skeleton.w + box.loss)
  paidSupport : (TargetArithmetic.arithmetic c).exteriorNorm
    ((p.choice.phases.moving (probeData K c) (momentRowCharacters K c) recipe.moving)
      .effectiveFullSupport recipe.remaining) ≤
        request.base ^ (p.geometry.skeleton.q + p.geometry.skeleton.R +
          p.geometry.skeleton.E + p.geometry.skeleton.wo)
  directSlots : p.geometry.tag = .direct → parent.geometry.slotCount = 0
  exceptional : bare.exceptional = fun h =>
    ActualSecondCorrelationRows.literalCharacter (chart.actualRows ∅ cutoff hcutoff label)
      (TargetArithmetic.context c) (probeData K c) (momentRowCharacters K c)
      p.leftInput.phases recipe.moving recipe.correction pattern sector h ∈ parent.theta
  widthBox : OriginalNominalGeometry.literalRowParameter p.geometry (3 * box.loss) +
    OriginalNominalGeometry.literalSupportParameter p.geometry
      (idealLogLength request.base
        (secondSixthRootIdeal block.primes block.leftMultiplicity block.rightMultiplicity).val) ≤
          box.rawNormBound
  leftPoint : ∀ h ∈ bare.rows, ∃ z : WithLp 2 (ℝ × ℝ), ∀ i ∈ bare.left,
    WithLp.toLp 2 (bare.leftFirst h i, bare.leftSecond h i) =
      z + rawSourceLocation (CanonicalLiteralLocations.plain p.firstSign)
        (CanonicalLiteralLocations.plain p.firstSign) (CanonicalLiteralLocations.prime p.firstSign) i
  rightPoint : ∀ h ∈ bare.rows, ∃ z : WithLp 2 (ℝ × ℝ), ∀ i ∈ bare.right,
    WithLp.toLp 2 (-bare.rightFirst h i, bare.rightSecond h i) =
      z + rawSourceLocation (CanonicalLiteralLocations.plain (-p.firstSign))
        (CanonicalLiteralLocations.plain (-p.firstSign))
        (CanonicalLiteralLocations.prime (-p.firstSign)) i

variable (hrows : (SelectedProfileData.rows request frequency).Nonempty) (valid : p.Valid)

/-- The radius comes from the original fixed analytic height and the
same computed profiles. All source tags use this single constructor. -/
def family :=
  ActualGaussStage.CoveredClassKey.literalPassiveNormalizedFamilyOfWindow
    (hΓ := actualSixthUnits_are_sixth (places K c))
    (μv := TargetArithmetic.localMeasures (K := K))
    (hDiff := TargetArithmetic.different c) (ν := TargetArithmetic.finiteMeasure (K := K))
    (P := probeData K c) (Rchar := momentRowCharacters K c)
    (δ₂ := box.delta) (hδ₂ := box.tilt_pos) (hδ₂half := box.tilt_le_half)
    (G := p.physical.source) (retainedScale := p.physical.firstGeometry.retainedScale)
    (Z := request.base) (g := p.physical.firstGeometry.enlargement)
    (hscale := p.physical.firstGeometry.retainedScale_pos)
    (hZ := zero_lt_one.trans (SelectedSource.base_gt_one request))
    (cutoff := cutoff) (hcutoff := hcutoff) (hnorm := p.physical.row_bound)
    (dimension := 0) (width := 0)
    (character := fun _ _ => (PUnit.unit : PUnit)) (dyad := fun _ _ i => Fin.elim0 i)
    (LC := p.cover) (RC := p.cover) (v := p.key) (exceptional := p.exceptional)
    (firstKernel := p.firstKernel) (x := p.location) (j := p.allocation) (hlive := p.live)
    (firstSign := p.firstSign) (leftAtoms := p.firstAtoms false) (rightAtoms := p.firstAtoms true)
    (leftScalar := p.scalar false) (rightScalar := p.scalar true)
    (leftBalance := p.balance false) (rightBalance := p.balance true)
    (hleftBalance := by sorry) (hrightBalance := by sorry)
    (leftProfiles := p.leftProfiles hrows) (rightProfiles := p.rightProfiles hrows)
    (hbaseLeft := rfl) (hbaseRight := rfl)
    (F := p.leftInput.phases) (choice := p.choice)
    (parent := parent) (oldMoving := recipe.moving) (correction := recipe.correction)
    (hcorr := by sorry) (remaining := recipe.remaining) (extra := p.leftInput.deletion)
    (leftSlots := p.leftSlots) (rightSlots := p.rightSlots)
    (hleftCharacters := valid.leftCharacters) (hrightCharacters := valid.rightCharacters)
    (profileBound := 1) (hprofileBound := zero_le_one) (hprofile := by
      intro q _
      exact ActualGaussStage.canonicalSector_prepared_weight_norm_le_one
        (hΓ := actualSixthUnits_are_sixth (places K c))
        (μv := TargetArithmetic.localMeasures (K := K))
        (hDiff := TargetArithmetic.different c) (ν := TargetArithmetic.finiteMeasure (K := K))
        (probeData K c) box.delta box.tilt_pos box.tilt_le_half p.physical.source
        p.physical.firstGeometry.retainedScale request.base p.physical.firstGeometry.enlargement
        p.physical.firstGeometry.retainedScale_pos
        (zero_lt_one.trans (SelectedSource.base_gt_one request)) cutoff hcutoff p.physical.row_bound
        0 0 (fun _ _ => (PUnit.unit : PUnit)) (fun _ _ i => Fin.elim0 i)
        valid.physicalRows p.key.1 p.key.2.1 q)
    (a := parameters) (step := recipeInductionSigma c) (geometry := p.geometry)
    (hretained := rfl) (henlargement := rfl)
    (hsecond := by sorry) (hopposite := by sorry) (hunit := by sorry) (hnonunit := by sorry)
    (columnLoss := box.loss) (cutoffExponent := box.loss)
    (hcolumnLoss := box.loss_pos.le) (hcutoffExponent := box.loss_pos.le)
    (hcutoffPower := box.secondCutoff_le (SelectedSource.base_gt_one request).le)
    (hactiveColumns := valid.columns) (hpaidSupport := valid.paidSupport)
    (reference := SelectedProfileData.reference request frequency hrows) (time := 0)
    (hone := by sorry) (hroot := SelectedSource.probe_root (c := c))
    (hemb := SelectedSource.probe_embedding (c := c))
    (hbackground := by sorry) (hslot := by sorry) (hexceptional := valid.exceptional)
    (centered := (SelectedSource.model request frequency).centered)
    (Y₁ := request.base ^ (SelectedSource.model request frequency).comparison₁)
    (Y₂ := request.base ^ (SelectedSource.model request frequency).comparison₂)
    (floor := 16 * recipeInductionSigma c) (padding := recipeInductionSigma c / 16)
    (domain := by sorry) (direct := valid.directSlots)
    (hsmall := by sorry) (error := box.loss) (herror := box.loss_pos.le)
    (hstep := box.step_pos) (mesh := (momentMesh K c.family).val)
    (hmesh := by sorry) (hfit := by sorry)
    (lo := SelectedProfileData.lower request) (hi := SelectedProfileData.upper request)
    (hlo := SelectedProfileData.lower_pos request) (hhi := by sorry)
    (orders := childOrdersAtRank c frame (selectedRank request))
    (original := SelectedProfileData.parentRawWindow request frequency)
    (hreference := Set.mem_univ _) (htime := Set.mem_univ _) (horders := by sorry)
    (leftComputed := p.leftComputed hrows) (rightComputed := p.rightComputed hrows)
    (hprimeOrders := by sorry)
    (δ := analyticContour c frame (selectedRank request))
    (analyticHeight := analyticHeightConstant c frame * (1 + Real.log request.base))
    (hδ := analyticContour_pos c frame (selectedRank request))
    (hδhi := analyticContour_le_quarter c frame (selectedRank request))
    (normBox := box.rawNormBound) (heightC := analyticHeightConstant c frame)
    (analyticWindow := by sorry)
    (boundary := by sorry) (hslotInverse := by sorry)
    (hwidthBox := by simpa only [show 2 * box.loss + box.loss = 3 * box.loss by ring] using valid.widthBox)
    (hheight := le_rfl)

end SelectedLeafPacket
end HeckeSkeleton.Moments.EngineStepV2
