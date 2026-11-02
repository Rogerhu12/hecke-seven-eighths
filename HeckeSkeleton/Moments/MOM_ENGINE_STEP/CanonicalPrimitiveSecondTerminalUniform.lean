import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveSecondTerminalConstants
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveDirectTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitivePooledTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDualOriginalExponent

set_option linter.unusedSectionVars false

/-!
# One fixed coefficient for the four original second terminals

The four complete source sums and the original first Fourier kernel are
fixed before the moving profiles and scale. The pooled coefficients keep
their original pool constant and fibre cap. Only the common original
profile amplitude varies, and its degree is the full `2 * (cap + 2)`.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

universe u

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckePort.Moments CanonicalPrimitiveEngineChoices

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (b : Box)
variable (F : CanonicalPrimitiveSecondTerminalConstants.Fixed.{u}
  (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  μv hDiff C (rowBallFiniteFamily K A.Sf 1) b)

/-- This is the same first kernel seminorm in both complete budgets. -/
def kernelBound : ℝ :=
  (firstTerminalFourierControl (W := ℝ)).seminorms.sup
    (schwartzSeminormFamily ℝ ℝ ℂ)
    (ActualGaussStage.canonicalRowBallKernel
      (A := A) (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν b.tilt b.tilt_pos b.tilt_le_half)

theorem kernelBound_nonneg : 0 ≤ kernelBound (A := A) μv ν b := by
  sorry

/-- The row exponent used by the actual pooled source and its fibre cap. -/
def rowExponent : ℝ := CompleteMovingRowRecipe.literalPrimitivePoolRowExponent
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (loss := b.loss) (cutoffExponent := b.loss)

theorem rowExponent_nonneg : 0 ≤ rowExponent b := by
  sorry

/-- The exact four constants already selected by the original source sums. -/
def sumConstant (pooled tail : Bool) : ℝ :=
  match pooled, tail with
  | false, false => CanonicalPrimitiveDirectTerminalBudget.zeroSumConstant
      μv C hDiff b.cap b.columnBound (b.ε / 8) b.columnBound_nonneg
        (div_pos b.ε_pos (by norm_num))
  | false, true => CanonicalPrimitiveDirectTerminalBudget.tailSumConstant
      μv C hDiff b.cap b.columnBound (b.ε / 8) b.columnBound_nonneg
        (div_pos b.ε_pos (by norm_num))
  | true, false => CanonicalPrimitivePooledTerminalBudget.zeroSumConstant
      μv C hDiff b.cap b.columnBound (b.ε / 8) b.columnBound_nonneg
        (div_pos b.ε_pos (by norm_num))
  | true, true => CanonicalPrimitivePooledTerminalBudget.tailSumConstant
      μv C hDiff b.cap b.columnBound (b.ε / 8) b.columnBound_nonneg
        (div_pos b.ε_pos (by norm_num))

theorem sumConstant_pos (pooled tail : Bool) :
    0 < sumConstant μv C hDiff b pooled tail := by
  sorry

def terminalOrders (tail : Bool) : Finset (ℕ × ℕ) :=
  if tail then F.sTail else F.sZero

def terminalConstant (tail : Bool) : ℝ := if tail then F.Cerror else F.Czero

theorem terminalConstant_nonneg (tail : Bool) :
    0 ≤ terminalConstant μv C hDiff b F tail := by
  sorry

/-- All factors preceding the individual profile constant, in their
original order. The amplified density has already been paid by its budget. -/
def multiplier (pooled tail : Bool) : ℝ :=
  if pooled then
    poolTerminalConstant K (b.step / 3) (rowExponent b) *
      (CanonicalPrimitivePooledTerminalWindows.fiberCap (rowExponent b) b.step : ℝ) *
      terminalConstant μv C hDiff b F tail * orbitalFieldFactor K *
      kernelBound (A := A) μv ν b
  else
    terminalConstant μv C hDiff b F tail * orbitalFieldFactor K *
      kernelBound (A := A) μv ν b

theorem multiplier_nonneg (pooled tail : Bool) :
    0 ≤ multiplier μv ν C hDiff b F pooled tail := by
  sorry

/-- Its four values are literally the four complete budget coefficients. -/
def coefficient (pooled tail : Bool) (amplitude : ℝ) : ℝ :=
  multiplier μv ν C hDiff b F pooled tail *
    CanonicalPrimitiveDirectTerminalWindows.profileConstant (A := A) b.cap amplitude
      (terminalOrders μv C hDiff b F tail) * sumConstant μv C hDiff b pooled tail

theorem coefficient_nonneg (pooled tail : Bool) (amplitude : ℝ) :
    0 ≤ coefficient μv ν C hDiff b F pooled tail amplitude := by
  sorry

/-- A positive source-independent majorant of all four unit amplitudes. -/
def Csecond : ℝ :=
  1 + coefficient μv ν C hDiff b F false false 1 +
    coefficient μv ν C hDiff b F false true 1 +
    coefficient μv ν C hDiff b F true false 1 +
    coefficient μv ν C hDiff b F true true 1

theorem Csecond_pos : 0 < Csecond μv ν C hDiff b F := by
  sorry

theorem coefficient_one_le (pooled tail : Bool) :
    coefficient μv ν C hDiff b F pooled tail 1 ≤ Csecond μv ν C hDiff b F := by
  sorry

/-- Every original plain and prime occurrence is paid in the same degree. -/
theorem coefficient_le (pooled tail : Bool) (amplitude control : ℝ)
    (hamplitude : 0 ≤ amplitude) (hcontrol : 1 ≤ control)
    (hprofile : amplitude ≤ control) :
    coefficient μv ν C hDiff b F pooled tail amplitude ≤
      Csecond μv ν C hDiff b F * control ^ (2 * (b.cap + 2)) := by
  sorry

/-- The direct zero loss with both physical losses and both fixed tilts. -/
theorem directZero_exponent_le (padding : ℝ) (hpadding : padding ≤ b.paddingMax) :
    CanonicalPrimitiveDirectTerminalWindows.zeroLoss padding b.step b.loss b.loss
        b.lengthBound b.columnBound b.tilt b.tilt + b.ε / 8 ≤
      b.paddingMax + 3 * b.step + b.ε := by
  sorry

/-- The pooled zero loss keeps the extra, actually paid density exponent. -/
theorem pooledZero_exponent_le (padding : ℝ) (hpadding : padding ≤ b.paddingMax) :
    CanonicalPrimitivePooledTerminalWindows.zeroLoss padding b.step b.loss b.loss
        b.lengthBound b.columnBound b.tilt b.tilt b.loss + b.ε / 8 ≤
      b.paddingMax + 3 * b.step + b.ε := by
  sorry

theorem tail_exponent_le : b.loss + b.ε / 8 ≤ b.paddingMax + 3 * b.step + b.ε := by
  sorry

/-- The exact exponent in each of the four complete budget bounds. -/
def exponent (pooled tail : Bool) (padding : ℝ) : ℝ :=
  if tail then b.loss + b.ε / 8 else
    if pooled then
      CanonicalPrimitivePooledTerminalWindows.zeroLoss padding b.step b.loss b.loss
        b.lengthBound b.columnBound b.tilt b.tilt b.loss + b.ε / 8
    else
      CanonicalPrimitiveDirectTerminalWindows.zeroLoss padding b.step b.loss b.loss
        b.lengthBound b.columnBound b.tilt b.tilt + b.ε / 8

theorem exponent_le (pooled tail : Bool) (padding : ℝ) (hpadding : padding ≤ b.paddingMax) :
    exponent b pooled tail padding ≤ b.paddingMax + 3 * b.step + b.ε := by
  sorry

/-- The existing actual budget may be followed directly by this numerical
comparison; no source, terminal, measure or divisor is changed. -/
theorem bound (pooled tail : Bool) (amplitude control Z padding : ℝ)
    (hamplitude : 0 ≤ amplitude) (hcontrol : 1 ≤ control)
    (hprofile : amplitude ≤ control) (hZ : 1 ≤ Z) (hpadding : padding ≤ b.paddingMax) :
    coefficient μv ν C hDiff b F pooled tail amplitude * Z ^ exponent b pooled tail padding ≤
      Csecond μv ν C hDiff b F * control ^ (2 * (b.cap + 2)) *
        Z ^ (b.paddingMax + 3 * b.step + b.ε) := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform.Csecond_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform.coefficient_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform.directZero_exponent_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform.pooledZero_exponent_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform.tail_exponent_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform.bound
