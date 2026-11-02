import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawTerminalData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonTupleFibers
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedCommonMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolTerminalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.TailBudget

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fixed scalar coefficients of the original physical terminals

The expressions are the numerical products in the original first and
second source estimates. In particular the second coefficient retains
the first Fourier mass, complete common-support mass, divisor harmonic
mass, mask multiplicity, the actual pool factor and its fibre cap. The
only selections are applications of already proved base estimates.
These definitions do not assume a bound on a moving source.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep EngineStep.CommonSupportMass
open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

namespace PhysicalConstants

open CanonicalPrimitiveEngineChoices

local instance physicalConstantPhaseFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

/-- The complete extracted occurrence tuple, before the original
prime is removed. -/
def tupleConstant (k : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) : ℝ :=
  (support_tuple_multiplicity_subpower (K := K) k B ε hB hε).choose

theorem tupleConstant_pos (k : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < tupleConstant (K := K) k B ε hB hε :=
  (support_tuple_multiplicity_subpower (K := K) k B ε hB hε).choose_spec.1

/-- The two original mask divisors use the same one-tuple bound at
half the available exponent. -/
def maskConstant (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) : ℝ :=
  tupleConstant (K := K) 1 B (ε / 2) hB (div_pos hε (by norm_num)) ^ 2

theorem maskConstant_nonneg (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    0 ≤ maskConstant (K := K) B ε hB hε := sq_nonneg _

def rowSeminorm (c : TargetContext K) (s : Finset (ℕ × ℕ)) : ℝ := by
  letI : MeasurableSpace (sLocalNormOneGroup K
      ((TargetArithmetic.arithmetic c).Sf : Set (HeightOneSpectrum (𝓞 K)))) := borel _
  letI : BorelSpace (sLocalNormOneGroup K
      ((TargetArithmetic.arithmetic c).Sf : Set (HeightOneSpectrum (𝓞 K)))) := ⟨rfl⟩
  exact s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (CanonicalRowBall.archTest K (TargetArithmetic.arithmetic c).Sf 1)

theorem rowSeminorm_nonneg (c : TargetContext K) (s : Finset (ℕ × ℕ)) :
    0 ≤ rowSeminorm c s := apply_nonneg _ _

def firstZeroCoefficient (c : TargetContext K) (b : Box) : ℝ :=
  (rawTerminalData c b).firstZero *
    maskConstant (K := K) b.columnBound ((b.ε / 8) / 4) b.columnBound_nonneg
      (div_pos (div_pos b.ε_pos (by norm_num)) (by norm_num)) *
    (4 * rowSeminorm c (rawTerminalData c b).firstZeroOrders)

def firstTailCoefficient (c : TargetContext K) (b : Box) : ℝ :=
  ((rawTerminalData c b).firstTail *
    (2 * firstTailFieldConstant K * idealCountConstant K ^ (2 * (b.cap + 2)))) *
    (4 * rowSeminorm c (rawTerminalData c b).firstTailOrders)

def firstCoefficient (c : TargetContext K) (b : Box) : ℝ :=
  1 + firstZeroCoefficient c b + firstTailCoefficient c b

theorem firstCoefficient_pos (c : TargetContext K) (b : Box) :
    0 < firstCoefficient c b := by
  sorry

/-- The original terminal sum gives half its exponent to tuple
fibres and splits the other half between three arithmetic counts. -/
def arithmeticLoss (b : Box) : ℝ := ((b.ε / 8) / 2) / 3

theorem arithmeticLoss_pos (b : Box) : 0 < arithmeticLoss b :=
  div_pos (div_pos (div_pos b.ε_pos (by norm_num)) (by norm_num)) (by norm_num)

def commonConstant (b : Box) : ℝ :=
  (actual_first_common_mass (K := K) b.columnBound (arithmeticLoss b)
    b.columnBound_nonneg (arithmeticLoss_pos b)).choose

def divisorConstant (b : Box) : ℝ :=
  (ideal_inverse_norm_subpower (K := K) b.columnBound (arithmeticLoss b)
    b.columnBound_nonneg (arithmeticLoss_pos b)).choose

def arithmeticConstant (b : Box) : ℝ :=
  commonConstant (K := K) b * divisorConstant (K := K) b *
    maskConstant (K := K) b.columnBound (arithmeticLoss b)
      b.columnBound_nonneg (arithmeticLoss_pos b) *
    (Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle) : ℝ)

def sumConstant (c : TargetContext K) (b : Box) (pooled : Bool) : ℝ :=
  let count := tupleConstant (K := K) (2 * (b.cap + 2))
    (2 * b.columnBound) ((b.ε / 8) / 2)
    (mul_nonneg (by norm_num) b.columnBound_nonneg)
    (div_pos (div_pos b.ε_pos (by norm_num)) (by norm_num))
  (rawTerminalData c b).fourierConstant *
    (if pooled then count * ((15 ^ (2 * (b.cap + 2)) : ℕ) : ℝ) else count) *
    arithmeticConstant (K := K) b

/-- Exactly the kernel seminorm that appears in the original first
Fourier estimate, before any branch or frequency is selected. -/
def kernelBound (c : TargetContext K) (b : Box) : ℝ :=
  (rawTerminalData c b).fourierOrders.sup (schwartzSeminormFamily ℝ ℝ ℂ)
    (rawTerminalData c b).kernel

def poolFiberCap (b : Box) : ℕ :=
  max 1 ⌈(b.rowBound + 6 * (b.step / 3)) / ((b.step / 3) / 2)⌉₊

def secondOrders (c : TargetContext K) (b : Box) (tail : Bool) : Finset (ℕ × ℕ) :=
  if tail then (rawTerminalData c b).secondTailOrders
  else (rawTerminalData c b).secondZeroOrders

def secondConstant (c : TargetContext K) (b : Box) (tail : Bool) : ℝ :=
  if tail then (rawTerminalData c b).secondTail else (rawTerminalData c b).secondZero

def secondMultiplier (c : TargetContext K) (b : Box) (pooled tail : Bool) : ℝ :=
  if pooled then
    poolTerminalConstant K (b.step / 3) b.rowBound * (poolFiberCap b : ℝ) *
      secondConstant c b tail * orbitalFieldFactor K * kernelBound c b
  else secondConstant c b tail * orbitalFieldFactor K * kernelBound c b

/-- Four actual coefficients: direct/pool crossed with zero/tail.
The unit-amplitude Gram profile contributes `4 * rowSeminorm`. -/
def secondCoefficient (c : TargetContext K) (b : Box) (pooled tail : Bool) : ℝ :=
  secondMultiplier c b pooled tail *
    (4 * rowSeminorm c (secondOrders c b tail)) * sumConstant c b pooled

def secondTotal (c : TargetContext K) (b : Box) : ℝ :=
  1 + secondCoefficient c b false false + secondCoefficient c b false true +
    secondCoefficient c b true false + secondCoefficient c b true true

theorem secondTotal_pos (c : TargetContext K) (b : Box) :
    0 < secondTotal c b := by
  sorry

end PhysicalConstants

def firstScalar (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  PhysicalConstants.firstCoefficient c (selectedBox c frame)

def secondScalar (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  PhysicalConstants.secondTotal c (selectedBox c frame)

theorem firstScalar_pos (c : TargetContext K) (frame : SourceFrame) :
    0 < firstScalar c frame := PhysicalConstants.firstCoefficient_pos c _

theorem secondScalar_pos (c : TargetContext K) (frame : SourceFrame) :
    0 < secondScalar c frame := PhysicalConstants.secondTotal_pos c _

end HeckeSkeleton.Moments.EngineStepV2
