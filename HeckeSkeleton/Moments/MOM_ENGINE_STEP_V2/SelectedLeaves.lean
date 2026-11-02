import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedPredicates
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ParentTerminals
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.HybridExpansion

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false

/-!
# Live literal leaves and the two exact raw terminal pairs

The finite carrier stores the actual two common labels, the independent
divisors and phases, both Cartesian branches and both allocations. Only
zero original weights or identically zero whole coefficients are removed.
Raw terminals are sums of actual zero values and the exact original
physical-cutoff discrepancy norms, before either child is normalized.
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

local instance selectedLeavesCircleFintype : Fintype ((PUnit × PUnit) →* Circle) :=
  Fintype.ofFinite _

namespace SelectedSource

variable (request : Request c frame Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ)

def directKeys := ActualDirectFirstSource.SecondStages.liveLeaves (directPrepared request frequency)
  (atlas request frequency) (directPredicates request frequency) (normalization request frequency)

def directLeaf (j : directKeys request frequency) :
    ActualHybridLeaf K (ActualSIntegerOrbit K (places K c)) ℝ ℝ :=
  ActualDirectFirstSource.SecondStages.parentLeaf (directPrepared request frequency) (atlas request frequency)
    (directPredicates request frequency) (normalization request frequency) j.val

theorem directLeaf_live (j : directKeys request frequency) :
    (directLeaf request frequency j).Live :=
  ActualDirectFirstSource.SecondStages.liveLeaves_spec (directPrepared request frequency) (atlas request frequency)
    (directPredicates request frequency) (normalization request frequency) j

def pooledKeys := ActualFirstSource.SecondStages.liveLeaves (pooledPrepared request frequency)
  (pooledAtlas request frequency) (pooledPredicates request frequency)
  (pooledNormalization request frequency)

def pooledLeaf (j : pooledKeys request frequency) :
    ActualHybridLeaf K (ActualSIntegerOrbit K (places K c)) ℝ ℝ :=
  ActualFirstSource.SecondStages.parentLeaf (pooledPrepared request frequency) (pooledAtlas request frequency)
    (pooledPredicates request frequency) (pooledNormalization request frequency) j.val

theorem pooledLeaf_live (j : pooledKeys request frequency) :
    (pooledLeaf request frequency j).Live :=
  ActualFirstSource.SecondStages.liveLeaves_spec (pooledPrepared request frequency) (pooledAtlas request frequency)
    (pooledPredicates request frequency) (pooledNormalization request frequency) j

/-- The tag is read from the actual dependent pool summand, retaining
the physical prime inside the leaf key for every valuation branch. -/
def pooledTag (j : pooledKeys request frequency) : AmplificationTag :=
  match j.val.2.2.2.2 with
  | .inl (.inl _) => .main
  | .inl (.inr (.inl _)) => .error .one
  | .inl (.inr (.inr (.inl _))) => .error .six
  | .inl (.inr (.inr (.inr _))) => .error .seven
  | .inr (.inl _) => .main
  | .inr (.inr (.inl _)) => .error .one
  | .inr (.inr (.inr (.inl _))) => .error .six
  | .inr (.inr (.inr (.inr _))) => .error .seven

def directFirstTerminals : RawTerminalPair :=
  ActualDirectFirstSource.firstRawTerminals (firstSource request frequency) (hDiff := TargetArithmetic.different c)

def directSecondTerminals : RawTerminalPair :=
  ActualDirectFirstSource.SecondStages.secondRawTerminals (directPrepared request frequency) (normalization request frequency)

def pooledFirstTerminals : RawTerminalPair :=
  ActualFirstSource.firstRawTerminals (pooledSource request frequency) (hDiff := TargetArithmetic.different c)

def pooledSecondTerminals : RawTerminalPair :=
  ActualFirstSource.SecondStages.secondRawTerminals (pooledPrepared request frequency) (pooledNormalization request frequency)

theorem directTerminals_nonneg :
    (0 ≤ (directFirstTerminals request frequency).1 ∧
      0 ≤ (directFirstTerminals request frequency).2) ∧
    (0 ≤ (directSecondTerminals request frequency).1 ∧
      0 ≤ (directSecondTerminals request frequency).2) := by
  sorry

theorem pooledTerminals_nonneg :
    (0 ≤ (pooledFirstTerminals request frequency).1 ∧
      0 ≤ (pooledFirstTerminals request frequency).2) ∧
    (0 ≤ (pooledSecondTerminals request frequency).1 ∧
      0 ≤ (pooledSecondTerminals request frequency).2) := by
  sorry

end SelectedSource
end HeckeSkeleton.Moments.EngineStepV2
