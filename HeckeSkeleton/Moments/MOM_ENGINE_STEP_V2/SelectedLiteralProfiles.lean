import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedLeafPacket
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedProfileData

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false

/-!
# Original representatives through the two literal extractions

One actual original row freezes the source's norm profiles at time zero.
Both sides use those representatives and the same rank-local annulus.
The two Cartesian occurrence maps and both scalar removals are computed
before any passive allocation or capacity truncation is considered.
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

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

namespace SelectedSource

variable (request : Request c frame Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ)
variable (hrows : (SelectedProfileData.rows request frequency).Nonempty)

def seedProfiles : (seed request frequency).ProfileData :=
  CompleteMovingRowRecipe.literalOriginalProfileDataOfWindow (recipe request frequency)
    PUnit.unit ((normProfiles request frequency).at PUnit.unit)
    (parameters request frequency) request.base 0
    (request.base ^ (model request frequency).comparison₁)
    (request.base ^ (model request frequency).comparison₂) (model request frequency).centered
    (base_gt_one request)
    (Real.rpow_pos_of_pos (zero_lt_one.trans (base_gt_one request)) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans (base_gt_one request)) _)
    (SelectedProfileData.reference request frequency hrows)
    (SelectedProfileData.reference_allowed request frequency hrows)
    (SelectedProfileData.localizedRawWindow request frequency)
    (Set.mem_univ _) (Set.mem_univ _) (SelectedProfileData.window_positive request)

def seedSchwartzModel : (seedProfiles request frequency hrows).SchwartzModel
    (SelectedProfileData.window request) :=
  CompleteMovingRowRecipe.literalOriginalSchwartzModel (recipe request frequency)
    PUnit.unit ((normProfiles request frequency).at PUnit.unit)
    (parameters request frequency) request.base 0
    (request.base ^ (model request frequency).comparison₁)
    (request.base ^ (model request frequency).comparison₂) (model request frequency).centered
    (base_gt_one request)
    (Real.rpow_pos_of_pos (zero_lt_one.trans (base_gt_one request)) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans (base_gt_one request)) _)
    (SelectedProfileData.reference request frequency hrows)
    (SelectedProfileData.reference_allowed request frequency hrows)
    (SelectedProfileData.localizedRawWindow request frequency)
    (Set.mem_univ _) (Set.mem_univ _) (SelectedProfileData.window_positive request)
    isClosed_Icc

def seedSlots : OriginalSlotDictionary (model request frequency).data
    (seed request frequency).length where
  index := Function.Embedding.refl _
  length_eq := by sorry

end SelectedSource

namespace SelectedLeafPacket

variable {request : Request c frame Cp Hp hCp hminimum hHp} {frequency : ℝ × ℝ}
variable {leaf : ActualHybridLeaf K (ActualSIntegerOrbit K (places K c)) ℝ ℝ}
variable (p : SelectedLeafPacket request frequency leaf)
variable (hrows : (SelectedProfileData.rows request frequency).Nonempty)

def firstAtlas (side : Bool) :
    SourceCartesianAtlas p.physical.source.columns p.physical.source.ideal :=
  match side with
  | false => p.cover.branch p.key.2.2.1
  | true => p.cover.branch p.key.2.2.2.1

def firstAtoms (side : Bool) : CanonicalLiteralRectangles.Atoms (K := K)
    (p.firstAtlas side).slotCount :=
  match side with
  | false => p.leftInput.atoms (σ := TargetArithmetic.embedding c)
      (probeData K c) (momentRowCharacters K c) (selectedBox c frame).delta (selectedBox c frame).delta
  | true => p.rightInput.atoms (σ := TargetArithmetic.embedding c)
      (probeData K c) (momentRowCharacters K c) (selectedBox c frame).delta (selectedBox c frame).delta

def scalar (side : Bool) : ℂ :=
  match side with
  | false => p.leftInput.scalar (σ := TargetArithmetic.embedding c) (selectedBox c frame).delta
  | true => p.rightInput.scalar (σ := TargetArithmetic.embedding c) (selectedBox c frame).delta

def balance (side : Bool) : Bool → ℝ :=
  match side with
  | false => p.leftInput.balance (selectedBox c frame).delta (selectedBox c frame).delta
  | true => p.rightInput.balance (selectedBox c frame).delta (selectedBox c frame).delta

def firstProfiles (side : Bool) : (p.firstAtoms side).ProfileData :=
  match side with
  | false => p.leftInput.profiles (σ := TargetArithmetic.embedding c)
      (probeData K c) (momentRowCharacters K c) (selectedBox c frame).delta (selectedBox c frame).delta
      (SelectedSource.seedProfiles request frequency hrows)
  | true => p.rightInput.profiles (σ := TargetArithmetic.embedding c)
      (probeData K c) (momentRowCharacters K c) (selectedBox c frame).delta (selectedBox c frame).delta
      (SelectedSource.seedProfiles request frequency hrows)

def leftProfiles :=
  (((p.firstProfiles hrows false).onAtlas
    (ActualGaussStage.CoveredClassKey.literalLeftParent p.key) rfl).extract
    (ActualGaussStage.CoveredClassKey.literalLeftBranch p.key)).onAtlas
    (ActualGaussStage.CoveredClassKey.literalLeftResidualAtlas p.key) rfl

def rightProfiles :=
  (((p.firstProfiles hrows true).onAtlas
    (ActualGaussStage.CoveredClassKey.literalRightParent p.key) rfl).extract
    (ActualGaussStage.CoveredClassKey.literalRightBranch p.key)).onAtlas
    (ActualGaussStage.CoveredClassKey.literalRightResidualAtlas p.key) rfl

def firstComputed (side : Bool) :
    CanonicalLiteralFullKappaInput.ComputedProfiles
      (((p.firstProfiles hrows side).scale (p.scalar side)⁻¹).balancePlain (p.balance side))
      (SelectedProfileData.window request) (childOrdersAtRank c frame (selectedRank request))
      (rawAmplitudeAtRank c frame (selectedRank request)) := by
  cases side
  · exact p.leftInput.computedProfiles (σ := TargetArithmetic.embedding c)
      (probeData K c) (momentRowCharacters K c) (selectedBox c frame).delta (selectedBox c frame).delta
      (SelectedSource.seedProfiles request frequency hrows)
      (SelectedSource.seedSchwartzModel request frequency hrows)
      isCompact_Icc (SelectedProfileData.window_positive request)
      (childOrdersAtRank c frame (selectedRank request))
      (rawAmplitudeAtRank c frame (selectedRank request))
      (zero_le_one.trans (rawAmplitudeAtRank_one_le c frame (selectedRank request)))
      (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  · exact p.rightInput.computedProfiles (σ := TargetArithmetic.embedding c)
      (probeData K c) (momentRowCharacters K c) (selectedBox c frame).delta (selectedBox c frame).delta
      (SelectedSource.seedProfiles request frequency hrows)
      (SelectedSource.seedSchwartzModel request frequency hrows)
      isCompact_Icc (SelectedProfileData.window_positive request)
      (childOrdersAtRank c frame (selectedRank request))
      (rawAmplitudeAtRank c frame (selectedRank request))
      (zero_le_one.trans (rawAmplitudeAtRank_one_le c frame (selectedRank request)))
      (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)

def leftComputed :=
  let first := CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance
    (p.scalar false)⁻¹ (p.balance false) (p.firstComputed hrows false)
    (ActualGaussStage.CoveredClassKey.literalLeftParent p.key) rfl
  let second := CanonicalLiteralFullKappaInput.ComputedProfiles.extractThenScaleBalance
    (p.scalar false)⁻¹ (p.balance false) first
    (ActualGaussStage.CoveredClassKey.literalLeftBranch p.key)
  CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance
    (p.scalar false)⁻¹ (p.balance false) second
    (ActualGaussStage.CoveredClassKey.literalLeftResidualAtlas p.key) rfl

def rightComputed :=
  let first := CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance
    (p.scalar true)⁻¹ (p.balance true) (p.firstComputed hrows true)
    (ActualGaussStage.CoveredClassKey.literalRightParent p.key) rfl
  let second := CanonicalLiteralFullKappaInput.ComputedProfiles.extractThenScaleBalance
    (p.scalar true)⁻¹ (p.balance true) first
    (ActualGaussStage.CoveredClassKey.literalRightBranch p.key)
  CanonicalLiteralFullKappaInput.ComputedProfiles.onAtlasThenScaleBalance
    (p.scalar true)⁻¹ (p.balance true) second
    (ActualGaussStage.CoveredClassKey.literalRightResidualAtlas p.key) rfl

def leftSlots : OriginalSlotDictionary (SelectedSource.model request frequency).data
    (ActualGaussStage.CoveredClassKey.literalLeftAtoms p.key (p.firstAtoms false)).length where
  index := ⟨fun j =>
    (p.leftInput.slots (σ := TargetArithmetic.embedding c) (probeData K c)
      (momentRowCharacters K c) (selectedBox c frame).delta (selectedBox c frame).delta
      (SelectedSource.model request frequency).data (SelectedSource.seedSlots request frequency)).index
        (SlotRestriction.index (ActualGaussStage.CoveredClassKey.literalLeftBranch p.key).keep j),
    by sorry⟩
  length_eq := by sorry

def rightSlots : OriginalSlotDictionary (SelectedSource.model request frequency).data
    (ActualGaussStage.CoveredClassKey.literalRightAtoms p.key (p.firstAtoms true)).length where
  index := ⟨fun j =>
    (p.rightInput.slots (σ := TargetArithmetic.embedding c) (probeData K c)
      (momentRowCharacters K c) (selectedBox c frame).delta (selectedBox c frame).delta
      (SelectedSource.model request frequency).data (SelectedSource.seedSlots request frequency)).index
        (SlotRestriction.index (ActualGaussStage.CoveredClassKey.literalRightBranch p.key).keep j),
    by sorry⟩
  length_eq := by sorry

end SelectedLeafPacket
end HeckeSkeleton.Moments.EngineStepV2
