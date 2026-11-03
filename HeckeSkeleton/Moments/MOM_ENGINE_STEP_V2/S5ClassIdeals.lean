import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S5NominalLedger
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualMovingFrequencyFactors

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual ideal coordinates of an S5 frequency class

One live frequency fixes the unit and nonunit radicals. The second
source's original nonunit classifier proves that every other live
frequency has these same radicals. Interchanging the second common
ideals handles both sides without choosing a new frequency class.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable (key : SecondClassKey second)

theorem live_label (h : key.R.live) :
    (key.source.stage.charts key.common key.divisor).rowLabel h.val = key.rowLabel := by
  have hr := (Finset.mem_filter.mp h.property).1
  exact (Finset.mem_filter.mp hr).2

theorem live_nonunit_same (realized : key.source.Realizes) (h k : key.R.live) :
    ∀ i, nonunitFrequencySaving (Arithmetic.context c) (key.R.primes i)
        (key.R.leftMultiplicity i) (key.R.rightMultiplicity i) (key.R.frequency h.val) ↔
      nonunitFrequencySaving (Arithmetic.context c) (key.R.primes i)
        (key.R.leftMultiplicity i) (key.R.rightMultiplicity i) (key.R.frequency k.val) := by
  have hs := realized.patternStable key.common key.divisor h.val k.val
    ((live_label key h).trans (live_label key k).symm)
  intro i
  have hi := congrFun hs i
  change decide (nonunitFrequencySaving (Arithmetic.context c) (key.R.primes i)
      (key.R.leftMultiplicity i) (key.R.rightMultiplicity i) (key.R.frequency h.val)) =
    decide (nonunitFrequencySaving (Arithmetic.context c) (key.R.primes i)
      (key.R.leftMultiplicity i) (key.R.rightMultiplicity i) (key.R.frequency k.val)) at hi
  have he : (decide (nonunitFrequencySaving (Arithmetic.context c) (key.R.primes i)
        (key.R.leftMultiplicity i) (key.R.rightMultiplicity i) (key.R.frequency h.val)) = true) ↔
      (decide (nonunitFrequencySaving (Arithmetic.context c) (key.R.primes i)
        (key.R.leftMultiplicity i) (key.R.rightMultiplicity i) (key.R.frequency k.val)) = true) := by
    rw [hi]
  simpa only [decide_eq_true_eq] using he

theorem live_radicals_same (realized : key.source.Realizes) (h k : key.R.live) :
    unitFrequencyRadical (Arithmetic.context c) key.R.primes
        key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency h.val) =
      unitFrequencyRadical (Arithmetic.context c) key.R.primes
        key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency k.val) ∧
    nonunitFrequencyRadical (Arithmetic.context c) key.R.primes
        key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency h.val) =
      nonunitFrequencyRadical (Arithmetic.context c) key.R.primes
        key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency k.val) :=
  key.R.frequencyRadicals_eq_of_nonunitClassification (Arithmetic.context c)
    h k (live_nonunit_same key realized h k)

def leftIdeals (h : key.R.live) : OriginalNominalIdeals K where
  first := key.source.physical.first.selected
  opposite := key.source.physical.first.opposite
  complementary := key.source.physical.first.complementary
  second := exteriorMomentIdeal (primePowerProduct key.R.primes key.R.leftMultiplicity)
  secondOpposite := exteriorMomentIdeal (primePowerProduct key.R.primes key.R.rightMultiplicity)
  unitPart := exteriorMomentIdeal (unitFrequencyRadical (Arithmetic.context c)
    key.R.primes key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency h.val))
  nonunitPart := exteriorMomentIdeal (nonunitFrequencyRadical (Arithmetic.context c)
    key.R.primes key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency h.val))
  unit_dvd_gcd :=
    unitFrequencyRadical_dvd_gcd (Arithmetic.context c) key.R.primes
      key.R.leftMultiplicity key.R.rightMultiplicity key.block.left_positive
      (key.R.frequency h.val)

def sideIdeals (h : key.R.live) (side : Bool) : OriginalNominalIdeals K :=
  if side then (leftIdeals key h).swapSecond else leftIdeals key h

theorem sideIdeals_first (h : key.R.live) (side : Bool) :
    (sideIdeals key h side).first.val = key.source.physical.first.selected.val := by
  cases side <;> rfl

theorem sideIdeals_opposite (h : key.R.live) (side : Bool) :
    (sideIdeals key h side).opposite.val = key.source.physical.first.opposite.val := by
  cases side <;> rfl

theorem sideIdeals_complementary (h : key.R.live) (side : Bool) :
    (sideIdeals key h side).complementary.val = key.source.physical.first.complementary.val := by
  cases side <;> rfl

theorem sideIdeals_second (h : key.R.live) (side : Bool) :
    (sideIdeals key h side).second.val =
      if side then key.common.val.2 else key.common.val.1 := by
  cases side
  · exact key.block.common_left
  · exact key.block.common_right

theorem sideIdeals_secondOpposite (h : key.R.live) (side : Bool) :
    (sideIdeals key h side).secondOpposite.val =
      if side then key.common.val.1 else key.common.val.2 := by
  cases side
  · exact key.block.common_right
  · exact key.block.common_left

theorem sideIdeals_unitPart (realized : key.source.Realizes)
    (h k : key.R.live) (side : Bool) :
    (sideIdeals key h side).unitPart.val =
      (unitFrequencyRadical (Arithmetic.context c) key.R.primes
        key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency k.val)).val := by
  have he := congrArg Subtype.val (live_radicals_same key realized h k).1
  cases side <;> exact he

theorem sideIdeals_nonunitPart (realized : key.source.Realizes)
    (h k : key.R.live) (side : Bool) :
    (sideIdeals key h side).nonunitPart.val =
      (nonunitFrequencyRadical (Arithmetic.context c) key.R.primes
        key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency k.val)).val := by
  have he := congrArg Subtype.val (live_radicals_same key realized h k).2
  cases side <;> exact he

theorem sideIdeals_firstFrequency (h : key.R.live) (side : Bool) :
    (sideIdeals key h side).firstFrequency call.workingParameters call.base =
      key.source.physical.firstFrequency := by
  cases side <;> rfl

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof.live_radicals_same
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof.sideIdeals
