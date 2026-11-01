import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalSourceBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectExceptionalKernels
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPooledExceptionalKernels
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalUniformIndexBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalOriginalIntegral

/-!
# Fixed choices for the complete original exceptional term

The two raw volume estimates, the actual Fourier kernels and the original
arithmetic mass theorems select all constants before a moving source.
The complete first deletion is paid by its fixed support box, including
the actual pool prime. These choices contain no source, child, terminal
bound or completed family estimate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalChoices

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open CanonicalPrimitiveEngineChoices

/-- The full original first deletion has a separate fixed width charge. -/
def sourceWidth (b : Box) : ℝ := max b.widthMax (b.columnBound + 2 * (b.step / 3))

theorem sourceWidth_nonneg (b : Box) : 0 ≤ sourceWidth b :=
  b.width_nonneg.trans (le_max_left _ _)

theorem parentWidth_le (b : Box) : b.widthMax ≤ sourceWidth b := le_max_left _ _

theorem firstSupportWidth_le (b : Box) :
    b.columnBound + 2 * (b.step / 3) ≤ sourceWidth b := le_max_right _ _

def volumeLoss (b : Box) : ℝ := b.ε / 64

theorem volumeLoss_pos (b : Box) : 0 < volumeLoss b := div_pos b.ε_pos (by norm_num)

def indexLoss (b : Box) : ℝ := b.ε / 64

theorem indexLoss_pos (b : Box) : 0 < indexLoss b := div_pos b.ε_pos (by norm_num)

def maskExponent (b : Box) : ℝ :=
  CanonicalLiteralExceptionalPhysicalBox.maskExponent (sourceWidth b) b.loss b.loss

theorem maskExponent_nonneg (b : Box) : 0 ≤ maskExponent b :=
  CanonicalLiteralExceptionalPhysicalBox.maskExponent_nonneg
    (sourceWidth_nonneg b) b.loss_pos.le b.loss_pos.le

/-- The two first scalar factors add exactly two powers per original slot. -/
def degree (b : Box) : ℕ := 2 * b.cap +
  (CanonicalLiteralExceptionalSourceBudget.profileDegree b.cap +
    CanonicalLiteralExceptionalAtomBudget.commonDegree b.cap)

theorem degree_eq (b : Box) : degree b = 14 * b.cap + 10 := by
  unfold degree CanonicalLiteralExceptionalAtomBudget.commonDegree
  rw [CanonicalLiteralExceptionalSourceBudget.profileDegree_eq]
  omega

/-- This enlarged arithmetic box retains all original 1/6/7 pool columns. -/
def indexBox (b : Box) : ℝ := b.columnBound + 7 * (b.step / 3)

theorem indexBox_nonneg (b : Box) : 0 ≤ indexBox b := by
  have hc := b.columnBound_nonneg
  have hs := b.step_pos
  unfold indexBox
  positivity

def firstTiltError (b : Box) : ℝ := 4 * b.normBound * (b.tilt + b.tilt)

/-- The three index losses and the one original pool loss fit after the
actual source and first scalar estimates have been applied. -/
theorem terminal_exponent_le (b : Box) (padding : ℝ) (hpadding : padding ≤ b.paddingMax) :
    (padding + 3 * b.step + b.ε / 2 + firstTiltError b) +
        indexLoss b + indexLoss b + indexLoss b + b.loss ≤
      b.paddingMax + 3 * b.step + b.ε := by
  have ht := CanonicalEngineSmallParameters.tilt_linear_budget b.normBound_nonneg b.ε_pos
  have ht0 := b.tilt_pos.le
  have hb := b.normBound_nonneg
  have hl := b.loss_le_ε
  have he := b.ε_pos
  change (6 * b.normBound + 4) * b.tilt ≤ b.ε / 32 at ht
  unfold firstTiltError indexLoss
  nlinarith [mul_nonneg hb ht0]

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
variable (b : Box) {ψ : HeckeCharacter K} {theta : Finset (HeckeCharacter K)}
variable (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive ψ theta
  (Set.Icc b.lo b.hi))

local notation "Γ₀" => sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "hΓ₀" => actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "FibreCode" => PUnit.{1} × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local instance exceptionalChoicesSixthUnitFintype :
    Fintype (SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := Fintype.ofFinite _
local notation "kernel" => ActualGaussStage.canonicalRowBallKernel
  (A := A) (Γ := Γ₀) μv ν b.tilt b.tilt_pos b.tilt_le_half

def orders : Finset (ℕ × ℕ) :=
  CanonicalLiteralExceptionalUnifiedChoice.orders
    (A := A) (σ := σ) (η := η) (hS := hS) primitive
      (volumeLoss b) (maskExponent b) (volumeLoss_pos b) (maskExponent_nonneg b)

def heightOrder : ℕ :=
  CanonicalLiteralExceptionalUnifiedChoice.heightOrder
    (A := A) (σ := σ) (η := η) (hS := hS) primitive
      (volumeLoss b) (maskExponent b) (volumeLoss_pos b) (maskExponent_nonneg b)

local notation "J" => heightOrder (A := A) (σ := σ) (η := η) (hS := hS) b primitive

/-- Both first scalar factors are paid together with their original profile. -/
def firstCoefficient : ℝ := orbitalFieldFactor K * b.hi ^ b.cap

theorem firstCoefficient_nonneg : 0 ≤ firstCoefficient (K := K) b :=
  mul_nonneg (orbitalFieldFactor_nonneg K) (pow_nonneg (zero_le_one.trans b.hi_ge_one) _)

def sourceCoefficient : ℝ :=
  b.hi ^ b.cap * orbitalFieldFactor K * ((Γ₀).index : ℝ) *
    CanonicalLiteralExceptionalSourceBudget.coefficient
      (A := A) (σ := σ) (η := η) (hS := hS) primitive
        (volumeLoss b) (sourceWidth b) b.loss b.loss
          (volumeLoss_pos b) (sourceWidth_nonneg b) b.loss_pos.le b.loss_pos.le
          b.tilt b.tilt b.hi b.cap

theorem sourceCoefficient_nonneg :
    0 ≤ sourceCoefficient (A := A) (σ := σ) (η := η) (hS := hS) b primitive := by
  have h := (CanonicalLiteralExceptionalSourceBudget.coefficient_pos
    (A := A) (σ := σ) (η := η) (hS := hS) primitive
      (volumeLoss b) (sourceWidth b) b.loss b.loss
        (volumeLoss_pos b) (sourceWidth_nonneg b) b.loss_pos.le b.loss_pos.le
        b.tilt b.tilt b.hi b.cap b.hi_ge_one).le
  have hh := zero_le_one.trans b.hi_ge_one
  have hf := orbitalFieldFactor_nonneg K
  unfold sourceCoefficient
  positivity

def integralCoefficient : ℝ :=
  (theta.card : ℝ) ^ 2 * firstCoefficient (K := K) b *
    sourceCoefficient (A := A) (σ := σ) (η := η) (hS := hS) b primitive *
      (1 + 2 * Real.pi) ^ J *
        CanonicalExceptionalPaidIntegral.fourierFactor J J kernel kernel

theorem integralCoefficient_nonneg :
    0 ≤ integralCoefficient (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive := by
  have h₁ := firstCoefficient_nonneg (K := K) b
  have h₂ := sourceCoefficient_nonneg (A := A) (σ := σ) (η := η) (hS := hS) b primitive
  have h₃ := CanonicalExceptionalPaidIntegral.fourierFactor_nonneg J J kernel kernel
  unfold integralCoefficient
  positivity

/-- A fixed cap dominates the original signed second-row fibre. -/
def fiberCap : ℝ := (CanonicalLiteralPrimitivePooledScalar.fiberCap b.rowBound b.step : ℝ)

theorem fiberCap_one : 1 ≤ fiberCap b := by
  change (1 : ℝ) ≤ (max 1 (⌈(b.rowBound + 6 * (b.step / 3)) /
    ((b.step / 3) / 2)⌉₊) : ℕ)
  exact_mod_cast (le_max_left 1 (⌈(b.rowBound + 6 * (b.step / 3)) / ((b.step / 3) / 2)⌉₊))

def leafCoefficient : ℝ := fiberCap b *
  integralCoefficient (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive

theorem leafCoefficient_nonneg :
    0 ≤ leafCoefficient (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive :=
  mul_nonneg (zero_le_one.trans (fiberCap_one b))
    (integralCoefficient_nonneg (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive)

local notation "leafC" => leafCoefficient (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive
local notation "hleafC" => leafCoefficient_nonneg (A := A) (σ := σ) (η := η) (hS := hS) μv ν b primitive
local notation "directExistence" => CanonicalExceptionalUniformIndexBudget.direct
  (A := A) (C := C) (U := ℝ) (E := ℝ) (Θ := FibreCode)
  (hΓ := hΓ₀) (μv := μv) (hDiff := hDiff) (finiteTest := rowBallFiniteFamily K A.Sf 1)
  b.cap 0 0 (degree b) b.columnBound (indexLoss b) (indexLoss b) (indexLoss b) leafC
  b.columnBound_nonneg (indexLoss_pos b) (indexLoss_pos b) (indexLoss_pos b) hleafC
local notation "pooledExistence" => CanonicalExceptionalUniformIndexBudget.amplified
  (A := A) (C := C) (U := ℝ) (E := ℝ) (Θ := FibreCode)
  (hΓ := hΓ₀) (μv := μv) (hDiff := hDiff) (finiteTest := rowBallFiniteFamily K A.Sf 1)
  b.cap 0 0 (degree b) (indexBox b) (indexLoss b) (indexLoss b) (indexLoss b)
  (b.step / 3) b.loss b.rowBound b.columnBound leafC
  (indexBox_nonneg b) (indexLoss_pos b) (indexLoss_pos b) (indexLoss_pos b)
  (div_pos b.step_pos (by norm_num)) b.loss_pos b.pool_separation.2
  b.rowBound_nonneg b.columnBound_nonneg hleafC

/-- The direct arithmetic constant precedes every moving original source. -/
def directConstant : ℝ := Classical.choose directExistence

theorem directConstant_pos : 0 < directConstant μv ν C hDiff b primitive :=
  (Classical.choose_spec directExistence).1

/-- Internal uniform estimate, to be consumed with the proved actual leaf estimates. -/
def direct_bound := (Classical.choose_spec directExistence).2

/-- The same pool arithmetic theorem chooses both numbers before the pool exists. -/
def pooledConstant : ℝ := Classical.choose pooledExistence

def pooledThreshold : ℝ := Classical.choose (Classical.choose_spec pooledExistence)

theorem pooledConstant_pos : 0 < pooledConstant μv ν C hDiff b primitive :=
  (Classical.choose_spec (Classical.choose_spec pooledExistence)).1

theorem pooledThreshold_gt_one : 1 < pooledThreshold μv ν C hDiff b primitive :=
  (Classical.choose_spec (Classical.choose_spec pooledExistence)).2.1

/-- Internal uniform estimate on the same amplified arithmetic carrier. -/
def pooled_bound := (Classical.choose_spec (Classical.choose_spec pooledExistence)).2.2

def constant : ℝ := 1 + directConstant μv ν C hDiff b primitive +
  pooledConstant μv ν C hDiff b primitive

theorem constant_pos : 0 < constant μv ν C hDiff b primitive := by
  have hd := directConstant_pos μv ν C hDiff b primitive
  have hp := pooledConstant_pos μv ν C hDiff b primitive
  unfold constant
  linarith

def threshold : ℝ := max b.fullThreshold
  (max (max 2 (Ideal.absNorm A.cS : ℝ)) (pooledThreshold μv ν C hDiff b primitive))

theorem threshold_windows (Z : ℝ) (hlarge : threshold μv ν C hDiff b primitive ≤ Z) :
    b.fullThreshold ≤ Z ∧ max 2 (Ideal.absNorm A.cS : ℝ) ≤ Z ∧
      pooledThreshold μv ν C hDiff b primitive ≤ Z := by
  exact ⟨(le_max_left _ _).trans hlarge,
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hlarge,
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hlarge⟩

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalChoices

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalChoices.degree_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalChoices.terminal_exponent_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalChoices.constant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalChoices.direct_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveExceptionalChoices.pooled_bound
