module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S5: original second correlation geometry before capacity

The common ideals and the actual divided-frequency pattern determine
both nominal sides. The first retained scale and branch tag stay fixed.
The conclusions are the paper's nominal width drop, positive slack,
complete-correlation norm and physical row/support windows. No child
profile, clipping, slot removal or final kernel mass is supplied here.

Paper: Section 4.8, lines 2883--2906.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family}

structure SecondClassKey (second : SecondFamily expansion) where
  sourceIndex : Fin expansion.count
  common : (second.source sourceIndex).CommonLabel
  divisor : (second.source sourceIndex).stage.mask.powerset
  rowLabel : Fin (((second.source sourceIndex).stage.charts common divisor).rowLabelCount + 1)

namespace SecondClassKey

variable {second : SecondFamily expansion} (key : SecondClassKey second)

abbrev source := second.source key.sourceIndex
abbrev block := key.source.block key.common
abbrev R := key.source.rows key.common key.divisor key.rowLabel

def Active : Prop :=
  0 < key.source.physical.outerWeight ∧ key.source.physical.source.rows.Nonempty ∧
    key.common.val ∈ key.source.physical.activeCommon ∧ key.R.live.Nonempty

end SecondClassKey

structure ClassGeometry {second : SecondFamily expansion} (key : SecondClassKey second) where
  nominal : Bool → OriginalNominalGeometry (K := K) call.workingParameters call.base
    (recipeInductionSigma c)

namespace ClassGeometry

variable {second : SecondFamily expansion} {key : SecondClassKey second}
variable (geometry : ClassGeometry key)

def slack (side : Bool) : ℝ :=
  (geometry.nominal side).halfSecond - (geometry.nominal side).secondRadical +
    (geometry.nominal side).tag.removedLength call.base +
    (geometry.nominal side).boundary +
    (geometry.nominal side).tag.poolLength (recipeInductionSigma c)

structure Realizes : Prop where
  first : ∀ side, (geometry.nominal side).ideals.first.val = key.source.physical.first.selected.val
  opposite : ∀ side, (geometry.nominal side).ideals.opposite.val = key.source.physical.first.opposite.val
  complementary : ∀ side, (geometry.nominal side).ideals.complementary.val =
    key.source.physical.first.complementary.val
  second : ∀ side, (geometry.nominal side).ideals.second.val =
    if side then key.common.val.2 else key.common.val.1
  secondOpposite : ∀ side, (geometry.nominal side).ideals.secondOpposite.val =
    if side then key.common.val.1 else key.common.val.2
  unitPart : ∀ side (h : key.R.live), (geometry.nominal side).ideals.unitPart.val =
    (unitFrequencyRadical (Arithmetic.context c) key.R.primes
      key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency h.val)).val
  nonunitPart : ∀ side (h : key.R.live), (geometry.nominal side).ideals.nonunitPart.val =
    (nonunitFrequencyRadical (Arithmetic.context c) key.R.primes
      key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency h.val)).val
  tag : ∀ side, (geometry.nominal side).tag = key.source.physical.first.tag
  retainedScale : ∀ side, (geometry.nominal side).retainedScale = key.source.physical.first.retainedScale
  supportError : ∀ side, (geometry.nominal side).supportError = 4 * p.loss
  width : ∀ side, (geometry.nominal side).skeleton.nominalWidth ≤
    call.workingParameters.m + call.workingParameters.q - recipeInductionSigma c
  slack : ∀ side, (geometry.nominal side).tag.removedLength call.base +
    (geometry.nominal side).tag.poolLength (recipeInductionSigma c) ≤ geometry.slack side
  correlation : ∀ side (h : key.R.live), ‖key.R.correlation h.val‖ ≤
    call.base ^ ((geometry.nominal side).skeleton.g₂ - (geometry.nominal side).skeleton.t₂)
  rowWindow : ∀ side (h : key.R.live),
    idealNorm K (key.R.extractedRow (Arithmetic.context c) h).momentIdeal ≤
      call.base ^ ((geometry.nominal side).skeleton.nominalRow + 12 * p.loss)
  supportWindow : ∀ side,
    ((Arithmetic.data c).exteriorNorm key.source.physical.first.paidSupport) *
      (Ideal.absNorm (geometry.nominal side).ideals.unitPart.val : ℝ) *
      (Ideal.absNorm (geometry.nominal side).ideals.nonunitPart.val : ℝ) ≤
        call.base ^ ((geometry.nominal side).skeleton.nominalSupport + 4 * p.loss)

end ClassGeometry

structure GeometryFamily (second : SecondFamily expansion) where
  geometry : ∀ key : SecondClassKey second, key.Active → ClassGeometry key

namespace GeometryFamily

def Realizes {second : SecondFamily expansion} (geometry : GeometryFamily second) : Prop :=
  ∀ key active, (geometry.geometry key active).Realizes

end GeometryFamily

def NominalGeometryTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (call : Call c) (trace : SourceTrace call p), trace.Realizes →
    ∃ geometry : GeometryFamily trace.second, geometry.Realizes

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
