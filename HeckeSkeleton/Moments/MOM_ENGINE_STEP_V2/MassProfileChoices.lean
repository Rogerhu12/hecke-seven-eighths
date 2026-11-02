import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.MassIndexChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawTerminalData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityProfileMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSeparateAtomMass

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false

/-!
# Explicit complete kernel-mass coefficient

The scalar below expands the witnesses in the original mass argument.
Only the already proved nested Fourier theorem and single-profile radius
theorem select data. The shape and Fourier factors are the literal
profile formulas at unit raw amplitude; the complete amplitude degree
is kept separately. Both original Fourier seminorms, the unit index,
physical fibres, independent passive labels and harmonic sum are paid.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep CommonSupportMass
open HeckeSkeleton.Moments.EngineInduction
open scoped Classical NumberField SchwartzMap

variable {K : Type} [Field K] [NumberField K]

namespace MassProfileChoices

variable (c : TargetContext K) (frame : SourceFrame) (rank : ℕ)

local notation "b" => selectedBox c frame
local notation "orders" => childOrdersAtRank c frame rank
local notation "J" => orders.sup Prod.snd

private def fourierExistence :=
  normalized_capacity_nested_kernel_uniform_mass
    (F := K) (A := TargetArithmetic.arithmetic c) (σ := TargetArithmetic.embedding c)
    (ω := c.family.omega) (ψ := targetCharacter K c) (U := ℝ) (E := ℝ)
    b.cap J J J J

def firstOrders : Finset (ℕ × ℕ) := (fourierExistence c frame rank).choose
def secondOrders : Finset (ℕ × ℕ) := (fourierExistence c frame rank).choose_spec.choose
def fourierConstant : ℝ := (fourierExistence c frame rank).choose_spec.choose_spec.choose

theorem fourierConstant_pos : 0 < fourierConstant c frame rank :=
  (fourierExistence c frame rank).choose_spec.choose_spec.choose_spec.1

def firstKernel : ℝ :=
  (firstOrders c frame rank).sup (schwartzSeminormFamily ℝ ℝ ℂ)
    (rawTerminalData c b).kernel

def secondKernel : ℝ :=
  (secondOrders c frame rank).sup (schwartzSeminormFamily ℝ ℝ ℂ)
    (rawTerminalData c b).kernel

def shapeCoefficient : ℝ :=
  CanonicalLogProfiles.shapeCoefficient (Set.Icc b.lo b.hi) isCompact_Icc
    (CanonicalLogProfiles.positiveAnnulus b.lo b.hi b.lo_pos)
    (CanonicalLiteralProfileScalars.exponent b.tilt b.tilt)
    (CanonicalLogProfiles.sourceOrders orders)

def phaseCoefficient (sign : ℝ) : ℝ :=
  CanonicalLiteralFourierWindows.coefficient (Set.Icc b.lo b.hi) isCompact_Icc
    (CanonicalLogProfiles.positiveAnnulus b.lo b.hi b.lo_pos) sign orders

def fixedCoefficient (sign : ℝ) : ℝ :=
  (1 + 2 * CanonicalLogProfiles.clippingCoefficient b.hi orders) *
    (1 + (1 + shapeCoefficient c frame rank * (1 + Real.sqrt b.hi)) *
      (1 + phaseCoefficient c frame rank sign))

def profileCoefficient : ℝ :=
  (1 + max (fixedCoefficient c frame rank 1) (fixedCoefficient c frame rank (-1))) ^
    massRadiusPower c * (max 1 b.hi) ^ b.cap

def unitIndex : ℝ :=
  ((sixthPowerSUnitSubgroup K
    ((TargetArithmetic.arithmetic c).Sf : Set (HeightOneSpectrum (𝓞 K))))).index

/-- These are exactly the scalar operations in the uniform-coefficient
witness: the fixed arithmetic factors precede the two radius powers. -/
def coefficient : ℝ :=
  (1 + unitIndex c * orbitalFieldFactor K ^ 2 *
    firstKernel c frame rank * secondKernel c frame rank) *
      (fourierConstant c frame rank * (2 * analyticRadiusConstant c frame) ^
        massRadiusPower c * profileCoefficient c frame rank)

theorem coefficient_pos : 0 < coefficient c frame rank := by
  sorry

def direct : ℝ :=
  coefficient c frame rank *
    (MassIndexChoices.directPassive c frame * MassIndexChoices.directPhysical c frame) *
      MassIndexChoices.directHarmonic c frame

def pooled : ℝ :=
  coefficient c frame rank * (MassIndexChoices.pooledFibreCap c frame : ℝ) *
    (MassIndexChoices.pooledPassive c frame * MassIndexChoices.pooledPhysical c frame) *
      MassIndexChoices.pooledHarmonic c frame

theorem direct_pos : 0 < direct c frame rank := by
  sorry

theorem pooled_pos : 0 < pooled c frame rank := by
  sorry

end MassProfileChoices

def massScalar (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) : ℝ :=
  1 + MassProfileChoices.direct c frame rank + MassProfileChoices.pooled c frame rank

theorem massScalar_pos (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) :
    0 < massScalar c frame rank := by
  have hd := MassProfileChoices.direct_pos c frame rank
  have hp := MassProfileChoices.pooled_pos c frame rank
  unfold massScalar
  linarith

/-- Two complete radius lists and three separate slot budgets. -/
def massProfileDegree (cap : ℕ) : ℕ := (cap + 2) + (cap + 2) + 8 * cap

theorem massProfileDegree_eq (cap : ℕ) : massProfileDegree cap = 10 * cap + 4 := by
  unfold massProfileDegree
  omega

end HeckeSkeleton.Moments.EngineStepV2
