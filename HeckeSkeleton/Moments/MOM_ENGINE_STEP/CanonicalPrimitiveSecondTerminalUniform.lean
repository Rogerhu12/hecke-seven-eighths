import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveSecondTerminalConstants
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveDirectTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitivePooledTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDualOriginalExponent

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

theorem kernelBound_nonneg : 0 ≤ kernelBound (A := A) μv ν b := apply_nonneg _ _

/-- The row exponent used by the actual pooled source and its fibre cap. -/
def rowExponent : ℝ := CompleteMovingRowRecipe.literalPrimitivePoolRowExponent
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (loss := b.loss) (cutoffExponent := b.loss)

theorem rowExponent_nonneg : 0 ≤ rowExponent b := by
  have hlength := b.lengthBound_nonneg
  have hcolumn := b.columnBound_nonneg
  have hloss := b.loss_pos.le
  dsimp only [rowExponent, CompleteMovingRowRecipe.literalPrimitivePoolRowExponent]
  positivity

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
  cases pooled <;> cases tail
  · exact CanonicalPrimitiveDirectTerminalBudget.zeroSumConstant_pos
      μv C hDiff b.cap b.columnBound (b.ε / 8) b.columnBound_nonneg
        (div_pos b.ε_pos (by norm_num))
  · exact CanonicalPrimitiveDirectTerminalBudget.tailSumConstant_pos
      μv C hDiff b.cap b.columnBound (b.ε / 8) b.columnBound_nonneg
        (div_pos b.ε_pos (by norm_num))
  · exact CanonicalPrimitivePooledTerminalBudget.zeroSumConstant_pos
      μv C hDiff b.cap b.columnBound (b.ε / 8) b.columnBound_nonneg
        (div_pos b.ε_pos (by norm_num))
  · exact CanonicalPrimitivePooledTerminalBudget.tailSumConstant_pos
      μv C hDiff b.cap b.columnBound (b.ε / 8) b.columnBound_nonneg
        (div_pos b.ε_pos (by norm_num))

def terminalOrders (tail : Bool) : Finset (ℕ × ℕ) :=
  if tail then F.sTail else F.sZero

def terminalConstant (tail : Bool) : ℝ := if tail then F.Cerror else F.Czero

theorem terminalConstant_nonneg (tail : Bool) :
    0 ≤ terminalConstant μv C hDiff b F tail := by
  cases tail
  · exact F.Czero_pos.le
  · exact F.Cerror_nonneg

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
  have hterminal := terminalConstant_nonneg μv C hDiff b F tail
  have hfield := orbitalFieldFactor_nonneg K
  have hkernel := kernelBound_nonneg (A := A) μv ν b
  have hpool := (poolTerminalConstant_pos (K := K) (b.step / 3) (rowExponent b)
    (div_pos b.step_pos (by norm_num)) (rowExponent_nonneg b)).le
  cases pooled <;> simp only [multiplier, Bool.false_eq_true, if_false, if_true] <;>
    positivity

/-- Its four values are literally the four complete budget coefficients. -/
def coefficient (pooled tail : Bool) (amplitude : ℝ) : ℝ :=
  multiplier μv ν C hDiff b F pooled tail *
    CanonicalPrimitiveDirectTerminalWindows.profileConstant (A := A) b.cap amplitude
      (terminalOrders μv C hDiff b F tail) * sumConstant μv C hDiff b pooled tail

theorem coefficient_nonneg (pooled tail : Bool) (amplitude : ℝ) :
    0 ≤ coefficient μv ν C hDiff b F pooled tail amplitude :=
  mul_nonneg (mul_nonneg (multiplier_nonneg μv ν C hDiff b F pooled tail)
    (CanonicalPrimitiveDirectTerminalWindows.profileConstant_nonneg (A := A) _ _ _))
      (sumConstant_pos μv C hDiff b pooled tail).le

/-- A positive source-independent majorant of all four unit amplitudes. -/
def Csecond : ℝ :=
  1 + coefficient μv ν C hDiff b F false false 1 +
    coefficient μv ν C hDiff b F false true 1 +
    coefficient μv ν C hDiff b F true false 1 +
    coefficient μv ν C hDiff b F true true 1

theorem Csecond_pos : 0 < Csecond μv ν C hDiff b F := by
  have h₁ := coefficient_nonneg μv ν C hDiff b F false false 1
  have h₂ := coefficient_nonneg μv ν C hDiff b F false true 1
  have h₃ := coefficient_nonneg μv ν C hDiff b F true false 1
  have h₄ := coefficient_nonneg μv ν C hDiff b F true true 1
  dsimp only [Csecond]
  linarith

theorem coefficient_one_le (pooled tail : Bool) :
    coefficient μv ν C hDiff b F pooled tail 1 ≤ Csecond μv ν C hDiff b F := by
  have h₁ := coefficient_nonneg μv ν C hDiff b F false false 1
  have h₂ := coefficient_nonneg μv ν C hDiff b F false true 1
  have h₃ := coefficient_nonneg μv ν C hDiff b F true false 1
  have h₄ := coefficient_nonneg μv ν C hDiff b F true true 1
  cases pooled <;> cases tail <;> dsimp only [Csecond] <;> linarith

/-- Every original plain and prime occurrence is paid in the same degree. -/
theorem coefficient_le (pooled tail : Bool) (amplitude control : ℝ)
    (hamplitude : 0 ≤ amplitude) (hcontrol : 1 ≤ control)
    (hprofile : amplitude ≤ control) :
    coefficient μv ν C hDiff b F pooled tail amplitude ≤
      Csecond μv ν C hDiff b F * control ^ (2 * (b.cap + 2)) := by
  let s := terminalOrders μv C hDiff b F tail
  have hp := first_dual_original_profile_constant_le b.cap 1 amplitude control
    (CanonicalRowBall.terminalSeminorm A s) hamplitude hcontrol
    (CanonicalRowBall.terminalSeminorm_nonneg s) (by simpa only [pow_one] using hprofile)
  have hprofile' : CanonicalPrimitiveDirectTerminalWindows.profileConstant (A := A)
      b.cap amplitude s ≤
      CanonicalPrimitiveDirectTerminalWindows.profileConstant (A := A) b.cap 1 s *
        control ^ (2 * (b.cap + 2)) := by
    simpa only [CanonicalPrimitiveDirectTerminalWindows.profileConstant,
      CanonicalRowBall.terminalSeminorm, firstDualOriginalProfileDegree, Nat.mul_one,
      one_pow, mul_one, show (2 : ℝ) ^ 2 = 4 by norm_num] using hp
  calc
    coefficient μv ν C hDiff b F pooled tail amplitude ≤
        coefficient μv ν C hDiff b F pooled tail 1 * control ^ (2 * (b.cap + 2)) := by
      unfold coefficient
      calc
        _ ≤ multiplier μv ν C hDiff b F pooled tail *
            (CanonicalPrimitiveDirectTerminalWindows.profileConstant (A := A) b.cap 1 s *
              control ^ (2 * (b.cap + 2))) * sumConstant μv C hDiff b pooled tail :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprofile'
              (multiplier_nonneg μv ν C hDiff b F pooled tail))
            (sumConstant_pos μv C hDiff b pooled tail).le
        _ = _ := by dsimp only [s]; ring
    _ ≤ Csecond μv ν C hDiff b F * control ^ (2 * (b.cap + 2)) :=
      mul_le_mul_of_nonneg_right (coefficient_one_le μv ν C hDiff b F pooled tail)
        (pow_nonneg (zero_le_one.trans hcontrol) _)

/-- The direct zero loss with both physical losses and both fixed tilts. -/
theorem directZero_exponent_le (padding : ℝ) (hpadding : padding ≤ b.paddingMax) :
    CanonicalPrimitiveDirectTerminalWindows.zeroLoss padding b.step b.loss b.loss
        b.lengthBound b.columnBound b.tilt b.tilt + b.ε / 8 ≤
      b.paddingMax + 3 * b.step + b.ε := by
  have hsmall := b.secondZero_loss
  have hstep := b.step_pos
  have hloss := b.loss_pos
  have hε := b.ε_pos
  dsimp only [Box.normBound] at hsmall
  unfold CanonicalPrimitiveDirectTerminalWindows.zeroLoss
  linarith

/-- The pooled zero loss keeps the extra, actually paid density exponent. -/
theorem pooledZero_exponent_le (padding : ℝ) (hpadding : padding ≤ b.paddingMax) :
    CanonicalPrimitivePooledTerminalWindows.zeroLoss padding b.step b.loss b.loss
        b.lengthBound b.columnBound b.tilt b.tilt b.loss + b.ε / 8 ≤
      b.paddingMax + 3 * b.step + b.ε := by
  have hsmall := b.secondZero_loss
  have hstep := b.step_pos
  have hε := b.ε_pos
  dsimp only [Box.normBound] at hsmall
  unfold CanonicalPrimitivePooledTerminalWindows.zeroLoss
  linarith

theorem tail_exponent_le : b.loss + b.ε / 8 ≤ b.paddingMax + 3 * b.step + b.ε := by
  have hloss := b.loss_le_ε
  have hpadding := b.padding_nonneg
  have hstep := b.step_pos
  have hε := b.ε_pos
  linarith

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
  cases tail
  · cases pooled
    · exact directZero_exponent_le b padding hpadding
    · exact pooledZero_exponent_le b padding hpadding
  · exact tail_exponent_le b

/-- The existing actual budget may be followed directly by this numerical
comparison; no source, terminal, measure or divisor is changed. -/
theorem bound (pooled tail : Bool) (amplitude control Z padding : ℝ)
    (hamplitude : 0 ≤ amplitude) (hcontrol : 1 ≤ control)
    (hprofile : amplitude ≤ control) (hZ : 1 ≤ Z) (hpadding : padding ≤ b.paddingMax) :
    coefficient μv ν C hDiff b F pooled tail amplitude * Z ^ exponent b pooled tail padding ≤
      Csecond μv ν C hDiff b F * control ^ (2 * (b.cap + 2)) *
        Z ^ (b.paddingMax + 3 * b.step + b.ε) := by
  exact mul_le_mul (coefficient_le μv ν C hDiff b F pooled tail amplitude control
    hamplitude hcontrol hprofile)
    (Real.rpow_le_rpow_of_exponent_le hZ (exponent_le b pooled tail padding hpadding))
    (Real.rpow_nonneg (zero_le_one.trans hZ) _)
    (mul_nonneg (Csecond_pos μv ν C hDiff b F).le
      (pow_nonneg (zero_le_one.trans hcontrol) _))

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform.Csecond_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform.coefficient_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform.directZero_exponent_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform.pooledZero_exponent_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform.tail_exponent_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalUniform.bound
