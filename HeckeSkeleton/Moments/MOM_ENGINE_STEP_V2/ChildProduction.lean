import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedNormalizedFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedPackets

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The same literal leaves produce the smaller admissible children

Each original live key is dispatched to its actual covered packet and
the single shared profile/capacity constructor. The two side energies
use the same original nested Fourier measure. The empty-row entrance
has an empty dependent family; the zero-slot entrance uses the actual
direct source and does not select an amplifier pool.
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

namespace SelectedSource

theorem directPacket_valid (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ)
    (hzero : (selectedModel request frequency).data.geometry.slotCount = 0)
    (j : directKeys request frequency) : (directPacket request frequency j).Valid := by
  sorry

theorem pooledPacket_valid (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ)
    (hzero : (selectedModel request frequency).data.geometry.slotCount ≠ 0)
    (j : pooledKeys request frequency) : (pooledPacket request frequency j).Valid := by
  sorry

end SelectedSource

def emptyNormalization (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    NormalizedExpansion (emptyExpansion request frequency)
      (recipeInductionSigma c) (admissibleOfInvariant request.primitive) where
  childCount b := Fin.elim0 b
  family b := Fin.elim0 b
  measures b := Fin.elim0 b
  ordinary_bound b := Fin.elim0 b

def directNormalization (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) (hrows : (SelectedProfileData.rows request frequency).Nonempty)
    (hzero : (selectedModel request frequency).data.geometry.slotCount = 0) :
    NormalizedExpansion (directExpansion request frequency)
      (recipeInductionSigma c) (admissibleOfInvariant request.primitive) :=
  let key := (SelectedSource.directKeys request frequency).equivFin.symm
  let packet b := SelectedSource.directPacket request frequency (key b)
  let valid b := SelectedSource.directPacket_valid request frequency hzero (key b)
  { childCount := fun b => (packet b).childCount hrows (valid b)
    family := fun b => (packet b).children hrows (valid b)
    measures := fun b => (packet b).measures hrows (valid b)
    ordinary_bound := fun b => (packet b).ordinary_bound hrows (valid b) }

def pooledNormalization (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) (hrows : (SelectedProfileData.rows request frequency).Nonempty)
    (hzero : (selectedModel request frequency).data.geometry.slotCount ≠ 0) :
    NormalizedExpansion (pooledExpansion request frequency)
      (recipeInductionSigma c) (admissibleOfInvariant request.primitive) :=
  let key := (SelectedSource.pooledKeys request frequency).equivFin.symm
  let packet b := SelectedSource.pooledPacket request frequency (key b)
  let valid b := SelectedSource.pooledPacket_valid request frequency hzero (key b)
  { childCount := fun b => (packet b).childCount hrows (valid b)
    family := fun b => (packet b).children hrows (valid b)
    measures := fun b => (packet b).measures hrows (valid b)
    ordinary_bound := fun b => (packet b).ordinary_bound hrows (valid b) }

/-- This dependent dispatch follows exactly the source's branch test
and its finite enumeration. It constructs all public data directly. -/
def selectedNormalization (request : Request c frame Cp Hp hCp hminimum hHp)
    (frequency : ℝ × ℝ) :
    NormalizedExpansion (selectedExpansion request frequency)
      (recipeInductionSigma c) (admissibleOfInvariant request.primitive) := by
  classical
  unfold selectedExpansion
  split_ifs with hrows hzero
  · exact emptyNormalization request frequency
  · exact directNormalization request frequency
      (Finset.nonempty_iff_ne_empty.mpr hrows) hzero
  · exact pooledNormalization request frequency
      (Finset.nonempty_iff_ne_empty.mpr hrows) hzero

/-- Both side invariants refer to the existing children and measures. -/
theorem selectedNormalization_invariant
    (request : Request c frame Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ)
    (side : Bool) (b : (selectedNormalization request frequency).Label)
    (ξ : EngineParameter) :
    admissibleOfInvariant request.primitive
      ((selectedNormalization request frequency).children.data side b ξ)
      ((selectedNormalization request frequency).children.parameters side b) :=
  (selectedNormalization request frequency).children.admissible_data side b ξ

theorem selectedNormalization_parent
    (request : Request c frame Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ) :
    (selectedModel request frequency).normalizedEnergy request.base 0 ≤
      ((selectedExpansion request frequency).normalizedTerminals
        (request_base_pos request).le).total +
          (selectedNormalization request frequency).kernels.pairIntegral :=
  HybridExpansion.normalized_parent_bound (selectedExpansion request frequency)
    (recipeInductionSigma c) (admissibleOfInvariant request.primitive)
    (selectedNormalization request frequency) (request_base_pos request)
    (selectedExpansion_parent request frequency)

end HeckeSkeleton.Moments.EngineStepV2
