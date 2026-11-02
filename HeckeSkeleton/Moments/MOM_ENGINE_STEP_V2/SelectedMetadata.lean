import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedLeafPacket

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false

/-!
# Original first coordinates of every physical source branch

The Boolean records the actual first Cauchy side. The optional pool
valuation records the genuine main source or the same selected prime
with valuation one, six or seven. Sources and geometry are constructed
directly from the original first block, before any child normalization.
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
open HeckePort.Moments HeckePort.Moments.Support

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

local instance selectedMetadataCircleFintype : Fintype ((PUnit × PUnit) →* Circle) :=
  Fintype.ofFinite _

namespace SelectedSource

variable (request : Request c frame Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ)

section Direct

variable (DE : (firstSource request frequency).CommonLabel)
variable (D : (((firstSource request frequency).block DE).mask
  (firstSource request frequency).mask).powerset)
variable (S : divisorPool ((firstSource request frequency).pieces DE D).rightData.columns
  (fun j => (((firstSource request frequency).pieces DE D).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

/-- True is the first left side; false is its signed right side. -/
def directMetadata (firstLeft : Bool) : SelectedStageMetadata request frequency :=
  match firstLeft with
  | true => {
      Column := _
      source := (((firstSource request frequency).pieces DE D).leftData.directSource
        (FirstBlockDirectData.leftDivisorCoefficient
          ((firstSource request frequency).pieces DE D) S χ))
      firstGeometry := leftDirectGeometry request frequency DE D
      row_bound := (directRows request frequency DE D).1 }
  | false => {
      Column := _
      source := (((firstSource request frequency).pieces DE D).rightData.directSource
        (FirstBlockDirectData.rightDivisorCoefficient
          ((firstSource request frequency).pieces DE D) S χ))
      firstGeometry := rightDirectGeometry request frequency DE D
      row_bound := (directRows request frequency DE D).2 }

end Direct

section Pooled

variable (DE : (pooledSource request frequency).CommonLabel)
variable (D : (((pooledSource request frequency).block DE).mask
  (pooledSource request frequency).mask).powerset)
variable (S : divisorPool ((pooledSource request frequency).pools DE D).rightData.columns
  (fun j => (((pooledSource request frequency).pools DE D).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

/-- A missing valuation is the actual main source, with its sixth-power
row enlargement. A valuation retains the original residual source and
the exact prime used by its first occurrence descriptor. -/
def pooledMetadata (firstLeft : Bool)
    (valuation : Option (AmplifierValuation × (pool request).primes)) :
    SelectedStageMetadata request frequency :=
  match firstLeft, valuation with
  | true, none => {
      Column := _
      source := (((pooledSource request frequency).pools DE D).divisorPools.leftData S).mainSource
        (((pooledSource request frequency).pools DE D).leftDivisorCoefficient S χ)
      firstGeometry := OriginalNominalGeometry.canonicalMain
        (a := parameters request frequency) (step := recipeInductionSigma c)
        (FirstCommonCharacterBlock.literalLeftCoordinates
          ((pooledSource request frequency).block DE) D.val)
        (selectedBox c frame).error (zero_lt_one.trans (base_gt_one request))
        (selectedBox c frame).error_pos.le
      row_bound := by sorry }
  | true, some (e, q) => {
      Column := _
      source := (((pooledSource request frequency).pools DE D).divisorPools.leftData S).residualSource
        q.val e.multiplicity (((pooledSource request frequency).pools DE D).leftDivisorCoefficient S χ)
      firstGeometry := OriginalNominalGeometry.canonicalPoolError
        (a := parameters request frequency) (pool request) e q
        (FirstCommonCharacterBlock.literalLeftCoordinates
          ((pooledSource request frequency).block DE) D.val)
        (selectedBox c frame).error (selectedBox c frame).error_pos.le
      row_bound := by sorry }
  | false, none => {
      Column := _
      source := (((pooledSource request frequency).pools DE D).divisorPools.rightData S).mainSource
        (((pooledSource request frequency).pools DE D).rightDivisorCoefficient S χ)
      firstGeometry := OriginalNominalGeometry.canonicalMain
        (a := parameters request frequency) (step := recipeInductionSigma c)
        (FirstCommonCharacterBlock.literalRightCoordinates
          ((pooledSource request frequency).block DE) D.val)
        (selectedBox c frame).error (zero_lt_one.trans (base_gt_one request))
        (selectedBox c frame).error_pos.le
      row_bound := by sorry }
  | false, some (e, q) => {
      Column := _
      source := (((pooledSource request frequency).pools DE D).divisorPools.rightData S).residualSource
        q.val e.multiplicity (((pooledSource request frequency).pools DE D).rightDivisorCoefficient S χ)
      firstGeometry := OriginalNominalGeometry.canonicalPoolError
        (a := parameters request frequency) (pool request) e q
        (FirstCommonCharacterBlock.literalRightCoordinates
          ((pooledSource request frequency).block DE) D.val)
        (selectedBox c frame).error (selectedBox c frame).error_pos.le
      row_bound := by sorry }

end Pooled
end SelectedSource
end HeckeSkeleton.Moments.EngineStepV2

