import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSourceCoordinates

/-!
# A fixed box for the actual complete exceptional mask

The original enlargement cancels the retained first scale and the first
moving-support terms. The complete sixth root is paid together with the
actual unit-pattern ideal inside the original second gcd. Consequently
the physical child width, including that complete root, is bounded by
the original parent width and the two literal column/cutoff losses.

This bound is uniform in both common ideals, every actual pattern and
the retained first row. It selects a fixed mask exponent before any
moving source or Fourier parameter, without assuming a final mask bound.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPhysicalBox

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {a : RealParameters} {Z step : ℝ}

/-- The original maximum defining the enlargement supplies the whole
first cancellation, including its original padding. -/
theorem frequency_support_le_parent
    (G : OriginalNominalGeometry (K := K) a Z step) (hstep : 0 ≤ step) :
    G.frequencyCenter + G.supportCenter ≤ a.m + a.q - step := by
  have hg := G.enlargement_bound hstep
  dsimp only [NominalChildGeometry.enlargementJ, NominalChildGeometry.shiftedCommon,
    NominalChildGeometry.firstFrequency, OriginalNominalGeometry.skeleton] at hg
  dsimp only [OriginalNominalGeometry.frequencyCenter, OriginalNominalGeometry.supportCenter,
    OriginalNominalGeometry.skeleton]
  linarith

variable {A : SArithmeticData K} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- This is precisely the complete physical exponent from the actual
appended-pattern frequency and mask window. -/
def physicalWidth (G : OriginalNominalGeometry (K := K) a Z step)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (columnLoss cutoffExponent : ℝ) : ℝ :=
  secondCommonChildWidth Z
    (G.skeleton.A - G.skeleton.c - G.skeleton.w + columnLoss)
    (a.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo G.skeleton.Krow G.skeleton.g
    (primePowerProduct p m).val (primePowerProduct p n).val
    (secondPatternUnitIdeal p m n pattern).val (secondPatternNonunitIdeal p pattern).val +
      idealLogLength Z (secondSixthRootIdeal p m n).val + cutoffExponent

theorem physicalWidth_le_parent
    (G : OriginalNominalGeometry (K := K) a Z step)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (pattern : ι → Bool)
    (columnLoss cutoffExponent : ℝ) (hZ : 1 < Z) (hstep : 0 ≤ step) :
    physicalWidth G p m n pattern columnLoss cutoffExponent ≤
      a.m + a.q - step + 2 * columnLoss + cutoffExponent := by
  have hfirst := frequency_support_le_parent G hstep
  have hunit := secondPatternUnitIdeal_root_log_slack Z hZ p m n hm hn pattern
  dsimp only [OriginalNominalGeometry.frequencyCenter, OriginalNominalGeometry.supportCenter]
    at hfirst
  change 2 * (G.skeleton.A - G.skeleton.c - G.skeleton.w) -
    G.skeleton.Krow - G.skeleton.g +
      (a.q + G.skeleton.R + G.skeleton.E + G.skeleton.wo) ≤ a.m + a.q - step at hfirst
  dsimp only [physicalWidth, secondCommonChildWidth]
  linarith

/-- One additional exponent pays the fixed initial bad-prime modulus
after its fixed threshold. Every argument is selected before the source. -/
def maskExponent (widthMax columnLoss cutoffExponent : ℝ) : ℝ :=
  widthMax + 2 * columnLoss + cutoffExponent + 1

theorem maskExponent_nonneg {widthMax columnLoss cutoffExponent : ℝ}
    (hwidth : 0 ≤ widthMax) (hcolumn : 0 ≤ columnLoss) (hcutoff : 0 ≤ cutoffExponent) :
    0 ≤ maskExponent widthMax columnLoss cutoffExponent := by
  unfold maskExponent
  linarith

theorem physicalWidth_add_one_le
    (G : OriginalNominalGeometry (K := K) a Z step)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (pattern : ι → Bool)
    (widthMax columnLoss cutoffExponent : ℝ) (hZ : 1 < Z) (hstep : 0 ≤ step)
    (hwidth : a.m + a.q ≤ widthMax) :
    physicalWidth G p m n pattern columnLoss cutoffExponent + 1 ≤
      maskExponent widthMax columnLoss cutoffExponent := by
  have h := physicalWidth_le_parent G p m n hm hn pattern columnLoss cutoffExponent hZ hstep
  unfold maskExponent
  linarith

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPhysicalBox

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPhysicalBox.physicalWidth_le_parent
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPhysicalBox.physicalWidth_add_one_le
