import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LeafNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedLeaves

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual source reaches one finite family of literal leaves

The source is the exact prepared Mellin model.  The complete moving
mask, Cartesian coefficient, two original Fourier kernels and four
amplifier valuations are retained.  The first and second common support
and their divisor allocations are independent parts of each finite
label.  The original single pool is chosen before any branch.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global EngineInduction EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

def selectedModel (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) : Node K c.family.omega (targetCharacter K c) :=
  (selectedCall request).model frequency

def selectedInput (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) : OriginalInput c (selectedModel request frequency) request.base :=
  request.originalInput (selectedCall request) frequency

theorem request_base_pos (request : Request c frame Cp Hp hCp hminimum hHp) :
    0 < request.base := by
  exact zero_lt_one.trans (SelectedSource.base_gt_one request)

/-- Empty original source rows retain no physical leaf or terminal. -/
def emptyExpansion (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    HybridExpansion c (selectedModel request frequency) request.base
      (selectedInput request frequency) where
  branches := 0
  pool := ∅
  tag b := Fin.elim0 b
  leaf b := Fin.elim0 b
  firstZero := 0
  secondZero := 0
  tail := 0
  firstZero_nonneg := le_rfl
  secondZero_nonneg := le_rfl
  tail_nonneg := le_rfl

/-- The direct entrance reindexes its literal live physical keys once.
The two exact raw terminal pairs remain those of the same source. -/
def directExpansion (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    HybridExpansion c (selectedModel request frequency) request.base
      (selectedInput request frequency) where
  branches := (SelectedSource.directKeys request frequency).card
  pool := ∅
  tag _ := .direct
  leaf b := SelectedSource.directLeaf request frequency
    ((SelectedSource.directKeys request frequency).equivFin.symm b)
  firstZero := (SelectedSource.directFirstTerminals request frequency).1
  secondZero := (SelectedSource.directSecondTerminals request frequency).1
  tail := (SelectedSource.directFirstTerminals request frequency).2 +
    (SelectedSource.directSecondTerminals request frequency).2
  firstZero_nonneg := (SelectedSource.directTerminals_nonneg request frequency).1.1
  secondZero_nonneg := (SelectedSource.directTerminals_nonneg request frequency).2.1
  tail_nonneg := add_nonneg
    (SelectedSource.directTerminals_nonneg request frequency).1.2
    (SelectedSource.directTerminals_nonneg request frequency).2.2

/-- Every pool label is a genuine main or valuation 1/6/7 source.
The sole original pool, actual prime and both divisors are retained. -/
def pooledExpansion (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    HybridExpansion c (selectedModel request frequency) request.base
      (selectedInput request frequency) where
  branches := (SelectedSource.pooledKeys request frequency).card
  pool := (SelectedSource.pool request).primes.image (fun p => p.val)
  tag b := SelectedSource.pooledTag request frequency
    ((SelectedSource.pooledKeys request frequency).equivFin.symm b)
  leaf b := SelectedSource.pooledLeaf request frequency
    ((SelectedSource.pooledKeys request frequency).equivFin.symm b)
  firstZero := (SelectedSource.pooledFirstTerminals request frequency).1
  secondZero := (SelectedSource.pooledSecondTerminals request frequency).1
  tail := (SelectedSource.pooledFirstTerminals request frequency).2 +
    (SelectedSource.pooledSecondTerminals request frequency).2
  firstZero_nonneg := (SelectedSource.pooledTerminals_nonneg request frequency).1.1
  secondZero_nonneg := (SelectedSource.pooledTerminals_nonneg request frequency).2.1
  tail_nonneg := add_nonneg
    (SelectedSource.pooledTerminals_nonneg request frequency).1.2
    (SelectedSource.pooledTerminals_nonneg request frequency).2.2

/-- Actual data are constructed before the source inequality. The
zero-slot case never invokes the prime-pool selection. -/
def selectedExpansion (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    HybridExpansion c (selectedModel request frequency) request.base
      (selectedInput request frequency) :=
  if pairedRows (selectedModel request frequency).data
      (selectedModel request frequency).parameters request.base = ∅ then
    emptyExpansion request frequency
  else if (selectedModel request frequency).data.geometry.slotCount = 0 then
    directExpansion request frequency
  else pooledExpansion request frequency

/-- Empty original row carriers remain empty throughout the construction. -/
theorem selectedExpansion_empty (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ)
    (hrows : pairedRows (selectedModel request frequency).data
      (selectedModel request frequency).parameters request.base = ∅) :
    (selectedExpansion request frequency).branches = 0 ∧
      (selectedExpansion request frequency).total = 0 := by
  sorry

/-- A zero-slot source takes the direct branch and constructs no prime pool. -/
theorem selectedExpansion_zero_slots (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ)
    (hzero : (selectedModel request frequency).data.geometry.slotCount = 0) :
    (selectedExpansion request frequency).pool = ∅ ∧
      ∀ b, (selectedExpansion request frequency).tag b = AmplificationTag.direct := by
  sorry

/-- The two complete transforms prove the inequality on the original
finite source before any leaf or child energy estimate is inserted. -/
theorem selectedExpansion_parent (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    (selectedModel request frequency).energy request.base 0 ≤
      (selectedExpansion request frequency).total := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2

