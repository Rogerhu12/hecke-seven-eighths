import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedSupportPoolAtlas


set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false

/-!
# The actual first occurrence descriptors on every source cover

These six small adapters dispatch the two first Cauchy sides and the
three source kinds to one common literal-input construction. Every
occurrence branch comes from the original atlas or the existing proved
combined-support reconstruction. Only dictionary equalities remain
proof obligations; no atom table or allocation is selected by a hole.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep EngineInduction
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis HeckeGeneral.Arithmetic
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  selectedPrincipal selectedComplex selectedNormOneSpace selectedNormOneBorel
  selectedInfinityUnitSpace selectedInfinityUnitBorel selectedLocalUnitSpace selectedLocalUnitBorel
  ActualPoolStages.coveredLeafKeyFintype
  FirstBlockPoolData.SecondStages.coveredClassKeyFintype
  FirstBlockPoolData.SecondStages.coveredLeafKeyFintype

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

local instance selectedInputCircleFintype : Fintype ((PUnit × PUnit) →* Circle) :=
  Fintype.ofFinite _

open DedekindZetaZeroFree.LocalFiniteSums
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum

namespace SelectedSource

variable (request : Request c frame Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ)

def seed :=
  CompleteMovingRowRecipe.literalOriginalAtoms (recipe request frequency) PUnit.unit
    ((normProfiles request frequency).at PUnit.unit :
      NormProfileRecipe (fun _ : PUnit.{1} => _)) (parameters request frequency)
    request.base 0 (request.base ^ (model request frequency).comparison₁)
    (request.base ^ (model request frequency).comparison₂) (model request frequency).centered
    (base_gt_one request)
    (Real.rpow_pos_of_pos (zero_lt_one.trans (base_gt_one request)) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans (base_gt_one request)) _)

section Direct

variable (DE : (firstSource request frequency).CommonLabel)
variable (D : (((firstSource request frequency).block DE).mask
  (firstSource request frequency).mask).powerset)
variable (S : divisorPool ((firstSource request frequency).pieces DE D).rightData.columns
  (fun j => (((firstSource request frequency).pieces DE D).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

def directLeftInput
    (label : (FirstBlockDirectData.leftSourceCover
      ((firstSource request frequency).pieces DE D) (atlas request frequency) S χ).labels) :
    LiteralInput (seed request frequency)
      ((FirstBlockDirectData.leftSourceCover
        ((firstSource request frequency).pieces DE D) (atlas request frequency) S χ).branch label) where
  firstSupport := primeSupport DE.val.1
  firstSupport_prime := fun _ hp => support_prime hp
  firstBranch := (atlas request frequency).branch (primeSupport DE.val.1) DE.val.1 label
  count := by sorry
  power := unitExterior (TargetArithmetic.arithmetic c)
  phases := CanonicalLiteralActualCharacters.unamplifiedPhases
    (FirstCommonCharacterBlock.literalLeftFixed ((firstSource request frequency).block DE) D.val)
    (CanonicalLiteralFirstPhase.leftElement (TargetArithmetic.context c)
      ((firstSource request frequency).block DE).primes
      ((firstSource request frequency).block DE).leftMultiplicity
      ((firstSource request frequency).block DE).rightMultiplicity
      (sIntegerMaskGenerator K (places K c) D.val).val)
    (FirstCommonCharacterBlock.literalLeftFixed_generates
      ((firstSource request frequency).block DE) (TargetArithmetic.context c) D.val)

def directRightInput
    (label : (FirstBlockDirectData.rightSourceCover
      ((firstSource request frequency).pieces DE D) (atlas request frequency) S χ).labels) :
    LiteralInput (seed request frequency)
      ((FirstBlockDirectData.rightSourceCover
        ((firstSource request frequency).pieces DE D) (atlas request frequency) S χ).branch label) where
  firstSupport := primeSupport DE.val.1
  firstSupport_prime := fun _ hp => support_prime hp
  firstBranch := (atlas request frequency).branch (primeSupport DE.val.1) DE.val.2 label
  count := by sorry
  power := unitExterior (TargetArithmetic.arithmetic c)
  phases := CanonicalLiteralActualCharacters.unamplifiedPhases
    (FirstCommonCharacterBlock.literalRightFixed ((firstSource request frequency).block DE) D.val)
    (CanonicalLiteralFirstPhase.rightElement (TargetArithmetic.context c)
      ((firstSource request frequency).block DE).primes
      ((firstSource request frequency).block DE).leftMultiplicity
      ((firstSource request frequency).block DE).rightMultiplicity
      (sIntegerMaskGenerator K (places K c) D.val).val)
    (FirstCommonCharacterBlock.literalRightFixed_generates
      ((firstSource request frequency).block DE) (TargetArithmetic.context c) D.val)

end Direct

section Pooled

variable (DE : (pooledSource request frequency).CommonLabel)
variable (D : (((pooledSource request frequency).block DE).mask
  (pooledSource request frequency).mask).powerset)
variable (S : divisorPool ((pooledSource request frequency).pools DE D).rightData.columns
  (fun j => (((pooledSource request frequency).pools DE D).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

def mainLeftInput
    (label : (((pooledSource request frequency).pools DE D).leftSourceCovers
      (pooledAtlas request frequency) S χ).main.labels) :
    LiteralInput (seed request frequency)
      ((((pooledSource request frequency).pools DE D).leftSourceCovers
        (pooledAtlas request frequency) S χ).main.branch label) where
  firstSupport := primeSupport DE.val.1
  firstSupport_prime := fun _ hp => support_prime hp
  firstBranch := (pooledAtlas request frequency).branch (primeSupport DE.val.1) DE.val.1 label
  count := by sorry
  power := unitExterior (TargetArithmetic.arithmetic c)
  phases := CanonicalLiteralActualCharacters.unamplifiedPhases
    (FirstCommonCharacterBlock.literalLeftFixed ((pooledSource request frequency).block DE) D.val)
    (CanonicalLiteralFirstPhase.leftElement (TargetArithmetic.context c)
      ((pooledSource request frequency).block DE).primes
      ((pooledSource request frequency).block DE).leftMultiplicity
      ((pooledSource request frequency).block DE).rightMultiplicity
      (sIntegerMaskGenerator K (places K c) D.val).val)
    (FirstCommonCharacterBlock.literalLeftFixed_generates
      ((pooledSource request frequency).block DE) (TargetArithmetic.context c) D.val)

def poolLeftInput (q : (pool request).primes) (n : ℕ)
    (label : ((((pooledSource request frequency).pools DE D).leftSourceCovers
      (pooledAtlas request frequency) S χ).residual q n).labels) :
    LiteralInput (seed request frequency)
      (((((pooledSource request frequency).pools DE D).leftSourceCovers
        (pooledAtlas request frequency) S χ).residual q n).branch label) where
  firstSupport := primeSupport DE.val.1 ∪ {q.val.val.asIdeal}
  firstSupport_prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact support_prime hp
    · rcases Finset.mem_singleton.mp hp with rfl
      exact q.val.val.prime
  firstBranch := (((pooledSource request frequency).pools DE D).divisorPools.leftData S)
    .combinedBranchForLabel (pooledAtlas request frequency) (primeSupport DE.val.1) DE.val.1
      ((((pooledSource request frequency).pools DE D).divisorPools.left_columns S).trans
        ((pooledSource request frequency).pools DE D).left_columns) q.val n label
  count := by sorry
  power := powerIdeal q.val n
  phases := CanonicalLiteralActualCharacters.amplifiedPhases (TargetArithmetic.context c)
    (FirstCommonCharacterBlock.literalLeftFixed ((pooledSource request frequency).block DE) D.val)
    (CanonicalLiteralFirstPhase.leftElement (TargetArithmetic.context c)
      ((pooledSource request frequency).block DE).primes
      ((pooledSource request frequency).block DE).leftMultiplicity
      ((pooledSource request frequency).block DE).rightMultiplicity
      (sIntegerMaskGenerator K (places K c) D.val).val)
    (FirstCommonCharacterBlock.literalLeftFixed_generates
      ((pooledSource request frequency).block DE) (TargetArithmetic.context c) D.val) q.val n

def mainRightInput
    (label : (((pooledSource request frequency).pools DE D).rightSourceCovers
      (pooledAtlas request frequency) S χ).main.labels) :
    LiteralInput (seed request frequency)
      ((((pooledSource request frequency).pools DE D).rightSourceCovers
        (pooledAtlas request frequency) S χ).main.branch label) where
  firstSupport := primeSupport DE.val.1
  firstSupport_prime := fun _ hp => support_prime hp
  firstBranch := (pooledAtlas request frequency).branch (primeSupport DE.val.1) DE.val.2 label
  count := by sorry
  power := unitExterior (TargetArithmetic.arithmetic c)
  phases := CanonicalLiteralActualCharacters.unamplifiedPhases
    (FirstCommonCharacterBlock.literalRightFixed ((pooledSource request frequency).block DE) D.val)
    (CanonicalLiteralFirstPhase.rightElement (TargetArithmetic.context c)
      ((pooledSource request frequency).block DE).primes
      ((pooledSource request frequency).block DE).leftMultiplicity
      ((pooledSource request frequency).block DE).rightMultiplicity
      (sIntegerMaskGenerator K (places K c) D.val).val)
    (FirstCommonCharacterBlock.literalRightFixed_generates
      ((pooledSource request frequency).block DE) (TargetArithmetic.context c) D.val)

def poolRightInput (q : (pool request).primes) (n : ℕ)
    (label : ((((pooledSource request frequency).pools DE D).rightSourceCovers
      (pooledAtlas request frequency) S χ).residual q n).labels) :
    LiteralInput (seed request frequency)
      (((((pooledSource request frequency).pools DE D).rightSourceCovers
        (pooledAtlas request frequency) S χ).residual q n).branch label) where
  firstSupport := primeSupport DE.val.1 ∪ {q.val.val.asIdeal}
  firstSupport_prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact support_prime hp
    · rcases Finset.mem_singleton.mp hp with rfl
      exact q.val.val.prime
  firstBranch := (((pooledSource request frequency).pools DE D).divisorPools.rightData S)
    .combinedBranchForLabel (pooledAtlas request frequency) (primeSupport DE.val.1) DE.val.2
      ((((pooledSource request frequency).pools DE D).divisorPools.right_columns S).trans
        ((pooledSource request frequency).pools DE D).right_columns) q.val n label
  count := by sorry
  power := powerIdeal q.val n
  phases := CanonicalLiteralActualCharacters.amplifiedPhases (TargetArithmetic.context c)
    (FirstCommonCharacterBlock.literalRightFixed ((pooledSource request frequency).block DE) D.val)
    (CanonicalLiteralFirstPhase.rightElement (TargetArithmetic.context c)
      ((pooledSource request frequency).block DE).primes
      ((pooledSource request frequency).block DE).leftMultiplicity
      ((pooledSource request frequency).block DE).rightMultiplicity
      (sIntegerMaskGenerator K (places K c) D.val).val)
    (FirstCommonCharacterBlock.literalRightFixed_generates
      ((pooledSource request frequency).block DE) (TargetArithmetic.context c) D.val) q.val n

end Pooled
end SelectedSource
end HeckeSkeleton.Moments.EngineStepV2

