module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceScalarData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Each original rectangle is the original literal atom product

This is the starting point before either support extraction. The
original index changes only the nonzero-ideal representation. Both
plain profiles, every original prime profile, the working comparison
scales and the original complete character mask are kept explicitly.
The absent ordinary comparison is zero before any subtraction.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace Call

variable (call : Call c)

def originalPlainWeight (rectangle plain : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) : ℂ :=
  (if plain then call.localizedNormProfiles.right PUnit.unit 0
   else call.localizedNormProfiles.left PUnit.unit 0)
    (idealNorm K I / call.originalPlainScale rectangle plain)

def originalBareRectangle (rectangle : Bool)
    (i : AllocationColumn K call.localizedData.geometry.slotCount) : ℂ :=
  rawBareSourceCoefficient call.originalCharacters
    (call.originalPlainScale rectangle false) (call.originalPlainScale rectangle true)
    call.base call.originalLength
    (call.originalPlainWeight rectangle false) (call.originalPlainWeight rectangle true)
    call.originalSlotWeight i

/-- The exact original individual term dictionary, on every column. -/
theorem workingRectangle_originalIndex (rectangle : Bool)
    (i : AllocationColumn K call.localizedData.geometry.slotCount) :
    call.workingValues.rectangle rectangle (call.workingRaw.originalIndex i) =
      call.originalBareRectangle rectangle i :=
  call.localizedSource.source.recipe.literalOriginalDictionary_rectangle PUnit.unit
    call.localizedNormProfiles call.workingParameters call.base 0
    (call.base ^ call.workingComparison₁) (call.base ^ call.workingComparison₂)
    rectangle (1 : PUnit.{1} →* Circle) i

def originalRectangleTerm (rectangle : Bool)
    (i : AllocationColumn K call.localizedData.geometry.slotCount) : ℂ :=
  if rectangle && !call.node.centered then 0 else call.originalBareRectangle rectangle i

theorem originalRectangleTerm_false
    (i : AllocationColumn K call.localizedData.geometry.slotCount) :
    call.originalRectangleTerm false i = call.originalBareRectangle false i := by
  simp only [originalRectangleTerm, Bool.false_and, Bool.false_eq_true, if_false]

theorem originalRectangleTerm_true
    (i : AllocationColumn K call.localizedData.geometry.slotCount) :
    call.originalRectangleTerm true i =
      if call.node.centered then call.originalBareRectangle true i else 0 := by
  cases h : call.node.centered <;> simp [originalRectangleTerm, h]

theorem workingCoefficient_originalIndex
    (i : AllocationColumn K call.localizedData.geometry.slotCount) :
    call.workingValues.coefficient call.node.centered (call.workingRaw.originalIndex i) =
      call.originalRectangleTerm false i - call.originalRectangleTerm true i := by
  rw [ParentRawAtoms.ConstantValues.coefficient,
    call.workingRectangle_originalIndex false i,
    call.workingRectangle_originalIndex true i,
    call.originalRectangleTerm_false, call.originalRectangleTerm_true]

end Call

namespace PhysicalSource

variable (source : PhysicalSource call p)

/-- The source's actual linear multiplier transports both original
rectangles at the same exact ancestor column. -/
theorem rectangle_of_originalIndex (rectangle : Bool) (i : source.Column)
    (original : AllocationColumn K call.localizedData.geometry.slotCount)
    (hancestor : source.ancestor i = call.workingRaw.originalIndex original) :
    source.rectangle rectangle i =
      source.multiplier i * call.originalRectangleTerm rectangle original := by
  cases rectangle <;> cases h : call.node.centered <;>
    simp [PhysicalSource.rectangle, Call.originalRectangleTerm, h, hancestor,
      call.workingRectangle_originalIndex]

end PhysicalSource
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Call.workingRectangle_originalIndex
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Call.workingCoefficient_originalIndex
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PhysicalSource.rectangle_of_originalIndex
