import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TargetArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PrimitiveFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourcePool
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PoolAttachment

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false

/-!
# The literal selected source and its original physical metadata

Only the original allowed rows are localized. The complete moving
recipe, mask, coefficients, theta and norm profiles remain those of the
selected Mellin model. The first source is built by its actual arithmetic
atoms and original Fourier transform. Its atlas and normalization are
the same objects subsequently consumed on the two second-stage sides.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep EngineInduction
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

attribute [local instance]
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

local instance selectedPrincipal : IsPrincipalIdealRing (TargetArithmetic.arithmetic c).R :=
  TargetArithmetic.principalRing c
local instance selectedComplex : IsTotallyComplex K := TargetArithmetic.totallyComplex c
local instance selectedNormOneSpace : MeasurableSpace (sLocalNormOneGroup K (places K c)) :=
  borel _
local instance selectedNormOneBorel : BorelSpace (sLocalNormOneGroup K (places K c)) := ⟨rfl⟩
local instance selectedInfinityUnitSpace : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ :=
  borel _
local instance selectedInfinityUnitBorel : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
local instance selectedLocalUnitSpace (v : places K c) : MeasurableSpace (v.val.adicCompletion K)ˣ :=
  borel _
local instance selectedLocalUnitBorel (v : places K c) : BorelSpace (v.val.adicCompletion K)ˣ := ⟨rfl⟩

namespace SelectedSource

variable (request : Request c frame Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ)

abbrev model := (selectedCall request).model frequency

def budget := (request.preparedSourceData (selectedCall request) frequency).localized

def recipe := (budget request frequency).source.recipe

def normProfiles := localizedNormProfileRecipe
  ((request.preparedNormProfiles (selectedCall request)).at frequency :
    NormProfileRecipe (fun _ : PUnit.{1} => (model request frequency).data))
  (model request frequency).parameters request.base

def parameters : RealParameters :=
  (CompleteMovingRowRecipe.fullSupportParameters (Q := (recipe request frequency))) (model request frequency).parameters request.base

def raw :=
  (((recipe request frequency).arithmeticAtoms PUnit.unit).constantAtoms
    ((normProfiles request frequency).at PUnit.unit :
      NormProfileRecipe (fun _ : PUnit.{1} => _))
    (parameters request frequency) request.base 0).raw
      (request.base ^ (model request frequency).comparison₁)
      (request.base ^ (model request frequency).comparison₂)

theorem base_gt_one : 1 < request.base := by
  have h₂ : (2 : ℝ) ≤ selectedBaseThreshold c frame := le_max_left _ _
  exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    (h₂.trans (selectedBase_large request))

theorem fullJointBudget : (recipe request frequency).FullJointBudget request.base
    ((model request frequency).parameters.m + (model request frequency).parameters.q) :=
  (request.preparedSourceData (selectedCall request) frequency).localizedFullJointBudget

theorem probe_root :
    (probeData K c).arithmetic.root6 = (TargetArithmetic.arithmetic c).zeta12 ^ 2 := by
  rfl

theorem probe_embedding :
    (probeData K c).arithmetic.embedding = TargetArithmetic.embedding c := by
  rfl

/-- The actual first Poisson source. Its input is the same original
recipe after the proved finite-row restriction, at time zero. -/
def firstSource :=
  (CompleteMovingRowRecipe.literalPrimitiveFirstSource (Q := (recipe request frequency)) (μv := (TargetArithmetic.localMeasures (K := K))) (ν := (TargetArithmetic.finiteMeasure (K := K))))
    (TargetArithmetic.context c) (probe_root (c := c)) (probe_embedding (c := c))
    (normProfiles request frequency) PUnit.unit (model request frequency).parameters
    request.base 0 (request.base ^ (model request frequency).comparison₁)
    (request.base ^ (model request frequency).comparison₂)
    (base_gt_one request) (fullJointBudget request frequency)
    (model request frequency).centered
    ((selectedBox c frame).firstCutoff request.base)
    ((selectedBox c frame).firstCutoff_ge_one (base_gt_one request).le)
    (selectedBox c frame).delta (selectedBox c frame).tilt_pos
    (selectedBox c frame).tilt_le_half

def atlas : SourceCartesianAtlas (firstSource request frequency).columns
    (firstSource request frequency).ideal :=
  (raw request frequency).originalAtlas

/-- The first allowances retain the actual first common radical and
the actual selected complementary divisor, including both norm lengths. -/
def normalization : (firstSource request frequency).Normalization :=
  (CompleteMovingRowRecipe.literalPrimitiveFirstNormalization (Q := (recipe request frequency)) (μv := (TargetArithmetic.localMeasures (K := K))) (ν := (TargetArithmetic.finiteMeasure (K := K))))
    (TargetArithmetic.context c) (probe_root (c := c)) (probe_embedding (c := c))
    (normProfiles request frequency) PUnit.unit (model request frequency).parameters
    request.base 0 (request.base ^ (model request frequency).comparison₁)
    (request.base ^ (model request frequency).comparison₂)
    (base_gt_one request) (fullJointBudget request frequency)
    (model request frequency).centered
    ((selectedBox c frame).firstCutoff request.base)
    ((selectedBox c frame).firstCutoff_ge_one (base_gt_one request).le)
    (selectedBox c frame).delta (selectedBox c frame).tilt_pos
    (selectedBox c frame).tilt_le_half

theorem pool_large :
    CanonicalPrimitiveEnginePool.threshold (TargetArithmetic.arithmetic c)
      (selectedBox c frame) ≤ request.base :=
  (selectedBaseThreshold_windows c frame (selectedBase_large request)).2.1

/-- The original single pool is chosen once, before either first side
or any second common label, divisor, phase or capacity deletion. -/
def poolSelection := CanonicalPrimitiveEnginePool.selected
  (TargetArithmetic.arithmetic c) (selectedBox c frame) request.base (pool_large request)

def pool := (poolSelection request).pool

theorem firstColumns_bound : ∀ i ∈ (firstSource request frequency).columns,
    (Ideal.absNorm ((firstSource request frequency).ideal i).val : ℝ) ≤
      request.base ^ (selectedBox c frame).columnBound := by
  sorry

theorem firstRows_bound
    (DE : (firstSource request frequency).CommonLabel)
    (D : (((firstSource request frequency).block DE).mask
      (firstSource request frequency).mask).powerset) :
    (∀ h ∈ ((firstSource request frequency).pieces DE D).leftData.rows,
      (TargetArithmetic.arithmetic c).exteriorNorm (originalFrequencyIdeal h) ≤
        request.base ^ (selectedBox c frame).rowBound) ∧
    (∀ h ∈ ((firstSource request frequency).pieces DE D).rightData.rows,
      (TargetArithmetic.arithmetic c).exteriorNorm (originalFrequencyIdeal h) ≤
        request.base ^ (selectedBox c frame).rowBound) := by
  sorry

/-- Installing the one pool changes only the amplifier data. The
original first source, actual atoms, Fourier chart and atlas are reused. -/
def pooledSource :=
  (ActualDirectFirstSource.withOriginalPool (s := (firstSource request frequency))) (pool request) 1 1
    one_ne_zero one_ne_zero (selectedBox c frame).rowBound (selectedBox c frame).rowBound
    0 0 (selectedBox c frame).columnBound
    (selectedBox c frame).rowBound_nonneg (selectedBox c frame).rowBound_nonneg
    (selectedBox c frame).columnBound_nonneg
    (fun DE D => (firstRows_bound request frequency DE D).1)
    (fun DE D => (firstRows_bound request frequency DE D).2)
    (by simp only [map_one, Nat.cast_one, Real.rpow_zero])
    (by simp only [map_one, Nat.cast_one, Real.rpow_zero])
    (firstColumns_bound request frequency)
    (by simpa only [zero_add] using (poolSelection request).density_pos)
    (by simpa only [zero_add] using (poolSelection request).density_pos)

def pooledAtlas : SourceCartesianAtlas (pooledSource request frequency).columns
    (pooledSource request frequency).ideal := atlas request frequency

def pooledNormalization : (pooledSource request frequency).Normalization :=
  (ActualFirstSource.canonicalNormalization (s := (pooledSource request frequency))) (base_gt_one request)
    (fun DE D => (parameters request frequency).n₁ + (parameters request frequency).n₂ +
      (parameters request frequency).z + (parameters request frequency).q +
      idealLogLength request.base (firstActiveRadical DE.val.1 DE.val.2) +
      idealLogLength request.base
        (firstPhysicalDivisorIdeal (A := TargetArithmetic.arithmetic c) D.val).val)

end SelectedSource
end HeckeSkeleton.Moments.EngineStepV2
