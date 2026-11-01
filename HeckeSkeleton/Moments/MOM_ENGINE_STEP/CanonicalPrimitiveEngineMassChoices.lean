import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineControl
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectGlobalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledGlobalMass

/-!
# The fixed contour and mass constants of the primitive engine

The slot cap, original mesh, annulus, finite seminorm orders and raw
analytic height constant determine every choice below. Both Fourier kernels
use the original fixed row-ball test and the same selected logarithmic tilt.
No scale, profile, source, allocation or normalized child enters these
choices. The final estimates compare only the explicit numerical right
sides of the proved direct and pooled whole-source mass bounds.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open CanonicalPrimitiveEngineChoices

/-- This is the reserved loss already used to select the original tilt. -/
def massLoss (b : Box) : ℝ := b.ε / 16

theorem massLoss_pos (b : Box) : 0 < massLoss b := div_pos b.ε_pos (by norm_num)

/-- The complete two radius powers and all three slot charges are kept. -/
def degree (b : Box) : ℕ :=
  CanonicalLiteralPassiveMassCoefficient.degree b.cap 1 0 0 0 0

theorem degree_eq (b : Box) : degree b = 10 * b.cap + 4 := by
  rw [degree, CanonicalLiteralPassiveMassCoefficient.degree_eq_explicit]
  omega

theorem tilt_eq_actual (b : Box) :
    b.tilt = CanonicalLiteralCombinedMassCoefficient.mellinTilt
      (max b.lengthBound b.columnBound) (massLoss b) := rfl

theorem rawWidth_eq (b : Box) :
    b.widthMax + b.columnBound + (2 * b.loss + b.loss) = b.rawNormBound := by
  unfold Box.rawNormBound
  ring

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
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

variable (b : Box) (mesh : ℝ) (orders : Finset (ℕ × ℕ)) (heightC : ℝ)

local notation "unitIndex" =>
  ((sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).index : ℝ)
local notation "firstKernel" =>
  (CanonicalLiteralKernelConstants.firstOrders K A σ ω ψ b.cap (orders.sup Prod.snd)).sup
    (schwartzSeminormFamily ℝ ℝ ℂ)
    (ActualGaussStage.canonicalRowBallKernel
      (A := A) (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν b.tilt b.tilt_pos b.tilt_le_half)
local notation "secondKernel" =>
  (CanonicalLiteralKernelConstants.secondOrders K A σ ω ψ b.cap (orders.sup Prod.snd)).sup
    (schwartzSeminormFamily ℝ ℝ ℂ)
    (ActualGaussStage.canonicalRowBallKernel
      (A := A) (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν b.tilt b.tilt_pos b.tilt_le_half)

/-- The actual full-kappa contour, selected before all source data. -/
def contour : ℝ :=
  CanonicalLiteralPrimitiveMassConstants.contour K A σ ω ψ b.cap 1 0
    b.hi b.lo b.hi b.lo_pos b.hi_ge_one (zero_le_one.trans b.hi_ge_one)
    b.normBound (massLoss b) b.normBound_nonneg (massLoss_pos b)
    orders mesh heightC b.rawNormBound b.rawNormBound_nonneg
    unitIndex firstKernel secondKernel (by positivity) (by positivity) (by positivity)

local notation "chosenContour" => contour
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC

theorem contour_pos : 0 < chosenContour :=
  CanonicalLiteralPrimitiveMassConstants.contour_pos K A σ ω ψ b.cap 1 0
    b.hi b.lo b.hi b.lo_pos b.hi_ge_one (zero_le_one.trans b.hi_ge_one)
    b.normBound (massLoss b) b.normBound_nonneg (massLoss_pos b)
    orders mesh heightC b.rawNormBound b.rawNormBound_nonneg
    unitIndex firstKernel secondKernel (by positivity) (by positivity) (by positivity)

theorem contour_le_quarter : chosenContour ≤ 1 / 4 :=
  CanonicalLiteralPrimitiveMassConstants.contour_le K A σ ω ψ b.cap 1 0
    b.hi b.lo b.hi b.lo_pos b.hi_ge_one (zero_le_one.trans b.hi_ge_one)
    b.normBound (massLoss b) b.normBound_nonneg (massLoss_pos b)
    orders mesh heightC b.rawNormBound b.rawNormBound_nonneg
    unitIndex firstKernel secondKernel (by positivity) (by positivity) (by positivity)

/-- The common raw width is the exact width used in both actual mass
constructors. Rewriting it does not select a different contour. -/
theorem contour_eq_actual : chosenContour =
    CanonicalLiteralPrimitiveMassConstants.contour K A σ ω ψ b.cap 1 0
      b.hi b.lo b.hi b.lo_pos b.hi_ge_one (zero_le_one.trans b.hi_ge_one)
      (max b.lengthBound b.columnBound) (massLoss b)
      (le_max_of_le_left b.lengthBound_nonneg) (massLoss_pos b)
      orders mesh heightC (b.widthMax + b.columnBound + (2 * b.loss + b.loss))
      (by have h₁ := b.width_nonneg
          have h₂ := b.columnBound_nonneg
          have h₃ := b.loss_pos.le
          positivity)
      unitIndex firstKernel secondKernel (by positivity) (by positivity) (by positivity) := by
  simpa only [rawWidth_eq b] using (rfl : chosenContour = chosenContour)

/-- The proved complete direct source uses exactly this fixed constant. -/
def directConstant : ℝ :=
  CompleteMovingRowRecipe.literalPrimitiveDirectMassConstant
  (K := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (μv := μv) (ν := ν)
  (cap := b.cap) (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (loss := b.loss) (cutoffExponent := b.loss) (hloss := b.loss_pos.le)
  (hcutoffExponent := b.loss_pos.le)
  (mesh := mesh) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (profileDegree := 1) (heightDegree := 0)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (widthMax := b.widthMax) (massLoss := massLoss b) (heightConstant := heightC)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (hwidthMax := b.width_nonneg) (hmassLoss := massLoss_pos b)

/-- The pooled constant retains the original orbit, passive-label and
amplified harmonic constants, including its single pool density loss. -/
def pooledConstant : ℝ :=
  CompleteMovingRowRecipe.literalPrimitivePooledMassConstant
  (K := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (μv := μv) (ν := ν)
  (cap := b.cap) (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (loss := b.loss) (cutoffExponent := b.loss) (hloss := b.loss_pos.le)
  (hcutoffExponent := b.loss_pos.le) (step := b.step) (hstep := b.step_pos)
  (mesh := mesh) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (profileDegree := 1) (heightDegree := 0)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (widthMax := b.widthMax) (massLoss := massLoss b) (heightConstant := heightC)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (hwidthMax := b.width_nonneg) (hmassLoss := massLoss_pos b)
  (eps := b.loss) (heps := b.loss_pos) (hepsSmall := b.pool_separation.2)

local notation "directC" => directConstant
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
local notation "pooledC" => pooledConstant
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC

theorem directConstant_pos : 0 < directC :=
  CompleteMovingRowRecipe.literalPrimitiveDirectMassConstant_pos
  (K := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (μv := μv) (ν := ν)
  (cap := b.cap) (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (loss := b.loss) (cutoffExponent := b.loss) (hloss := b.loss_pos.le)
  (hcutoffExponent := b.loss_pos.le)
  (mesh := mesh) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (profileDegree := 1) (heightDegree := 0)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (widthMax := b.widthMax) (massLoss := massLoss b) (heightConstant := heightC)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (hwidthMax := b.width_nonneg) (hmassLoss := massLoss_pos b)

theorem pooledConstant_pos : 0 < pooledC :=
  CompleteMovingRowRecipe.literalPrimitivePooledMassConstant_pos
  (K := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (μv := μv) (ν := ν)
  (cap := b.cap) (δ₁ := b.tilt) (hδ₁ := b.tilt_pos) (hδ₁half := b.tilt_le_half)
  (δ₂ := b.tilt) (hδ₂ := b.tilt_pos) (hδ₂half := b.tilt_le_half)
  (loss := b.loss) (cutoffExponent := b.loss) (hloss := b.loss_pos.le)
  (hcutoffExponent := b.loss_pos.le) (step := b.step) (hstep := b.step_pos)
  (mesh := mesh) (lo := b.lo) (hi := b.hi) (hlo := b.lo_pos) (hhi := b.hi_ge_one)
  (orders := orders) (profileDegree := 1) (heightDegree := 0)
  (lengthBound := b.lengthBound) (columnBound := b.columnBound)
  (widthMax := b.widthMax) (massLoss := massLoss b) (heightConstant := heightC)
  (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
  (hwidthMax := b.width_nonneg) (hmassLoss := massLoss_pos b)
  (eps := b.loss) (heps := b.loss_pos) (hepsSmall := b.pool_separation.2)

/-- A single fixed positive constant works for either original source. -/
def constant : ℝ := 1 + directC + pooledC

local notation "massC" => constant
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC

theorem constant_pos : 0 < massC := by
  have hd := directConstant_pos (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
  have hp := pooledConstant_pos (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
  dsimp only [constant]
  linarith

theorem directConstant_le : directC ≤ massC := by
  have hp := pooledConstant_pos (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
  dsimp only [constant]
  linarith

theorem pooledConstant_le : pooledC ≤ massC := by
  have hd := directConstant_pos (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC
  dsimp only [constant]
  linarith

/-- The threshold is likewise the existing amplified harmonic choice,
before the actual pool is constructed. -/
def pooledThreshold : ℝ :=
  CompleteMovingRowRecipe.literalPrimitivePooledMassThreshold
    (K := K) (A := A) (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
    (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
    (step := b.step) (hstep := b.step_pos)
    (lengthBound := b.lengthBound) (columnBound := b.columnBound)
    (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
    (massLoss := massLoss b) (hmassLoss := massLoss_pos b) (eps := b.loss)
    (heps := b.loss_pos) (hepsSmall := b.pool_separation.2)

theorem pooledThreshold_gt_one : 1 < pooledThreshold (A := A) b :=
  CompleteMovingRowRecipe.literalPrimitivePooledMassThreshold_one_lt
    (K := K) (A := A) (cap := b.cap) (loss := b.loss) (cutoffExponent := b.loss)
    (hloss := b.loss_pos.le) (hcutoffExponent := b.loss_pos.le)
    (step := b.step) (hstep := b.step_pos)
    (lengthBound := b.lengthBound) (columnBound := b.columnBound)
    (hlengthBound := b.lengthBound_nonneg) (hcolumnBound := b.columnBound_nonneg)
    (massLoss := massLoss b) (hmassLoss := massLoss_pos b) (eps := b.loss)
    (heps := b.loss_pos) (hepsSmall := b.pool_separation.2)

/-- The original mesh is paid once, independently of the analytic loss. -/
theorem direct_exponent_le :
    9 * massLoss b / 4 + 5 * b.error / 3 + mesh ≤ b.ε + mesh := by
  have h := b.direct_mass_loss
  have hloss := b.loss_pos.le
  change 9 * (b.ε / 16) / 4 + 5 * b.error / 3 + mesh ≤ b.ε + mesh
  linarith [b.ε_pos]

theorem pooled_exponent_le :
    9 * massLoss b / 4 + b.loss + 5 * b.error / 3 + mesh ≤ b.ε + mesh := by
  have h := b.pooled_mass_loss
  have hloss := b.loss_pos.le
  change 9 * (b.ε / 16) / 4 + b.loss + 5 * b.error / 3 + mesh ≤ b.ε + mesh
  linarith [b.ε_pos]

/-- This is only a numerical comparison of the direct theorem's
explicit right side; it assumes no family mass estimate. -/
theorem direct_bound (control Z : ℝ) (hcontrol : 1 ≤ control) (hZ : 1 ≤ Z) :
    directC * control ^ degree b * Z ^ (9 * massLoss b / 4 + 5 * b.error / 3 + mesh) ≤
      massC * control ^ degree b * Z ^ (b.ε + mesh) :=
  CanonicalPrimitiveEngineControl.monomial_mono
    (constant_pos (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC).le
    (directConstant_le (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC)
    hcontrol hZ le_rfl (direct_exponent_le b mesh)

/-- The pool contributes its one extra `loss` and no additional
unpaid exponent. Its original fixed constant is the one bounded above. -/
theorem pooled_bound (control Z : ℝ) (hcontrol : 1 ≤ control) (hZ : 1 ≤ Z) :
    pooledC * control ^ degree b *
        Z ^ (9 * massLoss b / 4 + b.loss + 5 * b.error / 3 + mesh) ≤
      massC * control ^ degree b * Z ^ (b.ε + mesh) :=
  CanonicalPrimitiveEngineControl.monomial_mono
    (constant_pos (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC).le
    (pooledConstant_le (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC)
    hcontrol hZ le_rfl (pooled_exponent_le b mesh)

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.degree_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.contour_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.contour_le_quarter
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.contour_eq_actual
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.constant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.pooledThreshold_gt_one
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.direct_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineMassChoices.pooled_bound
