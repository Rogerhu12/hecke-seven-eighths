import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSharpSecondZeroLedger
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualGaussStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

/-!
# Original normalization powers for the actual second terminals

The first normalization contains the full physical-mask and active
radical lengths. Its shift is adjusted by exactly the same amount as
the allowance. Thus the sharp second-zero cancellation applies to the
normalization already used by the actual child family.

The physical radius and fixed tail degree below are computed from
original scale and length windows. No terminal estimate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

/-- The shift for the literal normalization used by the children. -/
def firstProfileShiftForTotal (total δ : ℝ) : ℝ :=
  total - a.q - idealLogLength Z G.ideals.complementary.val -
    idealLogLength Z (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) +
      δ * (idealLogLength Z G.ideals.complementary.val +
        idealLogLength Z (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) - a.m)

theorem firstProfileShiftForTotal_eq (total δ : ℝ) :
    G.firstProfileShiftForTotal total δ =
      G.firstProfileShift δ + total - (a.n₁ + a.n₂ + a.z) := by
  unfold firstProfileShiftForTotal firstProfileShift
  ring

/-- The original first row weight keeps exactly its old exponent. -/
theorem firstProfileShiftForTotal_exponent (total δ : ℝ) :
    (a.m + a.q) - total + G.firstProfileShiftForTotal total δ =
      a.m - idealLogLength Z G.ideals.complementary.val -
        idealLogLength Z (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) +
          δ * (idealLogLength Z G.ideals.complementary.val +
            idealLogLength Z (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) - a.m) := by
  unfold firstProfileShiftForTotal
  ring

/-- Changing the displayed normalization moves both sides of the
same allowance identity; it does not change the source or its budget. -/
theorem sharp_zero_allowance_ledger_for_total
    (hZ : 1 < Z) (hstep : 0 ≤ step)
    (total loss δ ε productExponent lengthBound padding : ℝ)
    (hm : 0 ≤ a.m) (hloss : loss ≤ 1) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
    (hmask : idealLogLength Z G.ideals.complementary.val ≤ lengthBound)
    (hactive : idealLogLength Z
      (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) ≤ lengthBound)
    (hproduct : productExponent ≤ 2 * (lengthBound + 1))
    (hcore : a.n₁ + a.n₂ + a.z ≤ a.m + a.q + padding) :
    G.sharpZeroExponent loss δ + productExponent * ε ≤
      (total - idealLogLength Z G.ideals.first.val + G.boundary) +
        (padding + 5 * step / 3 + G.supportError + 2 * loss +
          (4 * lengthBound + 2) * δ + 2 * (lengthBound + 1) * ε) -
            G.firstProfileShiftForTotal total δ := by
  have h := G.sharp_zero_allowance_ledger hZ hstep loss δ ε productExponent
    lengthBound padding hm hloss hδ hε htotal hmask hactive hproduct hcore
  rw [G.firstProfileShiftForTotal_eq]
  linarith

theorem tail_allowance_ledger_for_total
    (total δ lengthBound loss saving : ℝ)
    (hm : 0 ≤ a.m) (hq : 0 ≤ a.q) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hmaskNonneg : 0 ≤ idealLogLength Z G.ideals.complementary.val)
    (hactiveNonneg : 0 ≤ idealLogLength Z
      (firstActiveRadical G.ideals.first.val G.ideals.opposite.val))
    (hfirst : idealLogLength Z G.ideals.first.val ≤ lengthBound)
    (hmask : idealLogLength Z G.ideals.complementary.val ≤ lengthBound)
    (hactive : idealLogLength Z
      (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) ≤ lengthBound)
    (hloss : 0 ≤ loss) (hsaving : 2 * lengthBound ≤ saving) :
    -saving ≤ (total - idealLogLength Z G.ideals.first.val + G.boundary) +
      loss - G.firstProfileShiftForTotal total δ := by
  have h := G.tail_allowance_ledger δ lengthBound loss saving hm hq hδ hδhalf
    hmaskNonneg hactiveNonneg hfirst hmask hactive hloss hsaving
  rw [G.firstProfileShiftForTotal_eq]
  linarith

/-- This is the actual inverse radius of the second row-ball stage,
including a retained endpoint whose logarithmic length may be negative. -/
theorem canonical_inverse_radius (hZ : 1 < Z) :
    (CanonicalRowBall.gaussRadius G.retainedScale Z G.enlargement
      G.retainedScale_pos (zero_lt_one.trans hZ)).val⁻¹ =
        Z ^ (G.retainedLength + G.enlargement) := by
  have hr : Z ^ G.retainedLength = G.retainedScale := by
    simpa only [retainedLength, Real.logb] using
      Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' G.retainedScale_pos
  rw [CanonicalRowBall.gaussRadius_val, inv_inv,
    Real.rpow_add (zero_lt_one.trans hZ), hr]

/-- The fixed original length box bounds the exact second inverse
radius. The bound does not depend on a second common label. -/
theorem inverse_radius_exponent_le
    (hZ : 1 < Z) (hstep : 0 ≤ step) (lengthBound : ℝ)
    (hm : 0 ≤ a.m) (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
    (hmask : idealLogLength Z G.ideals.complementary.val ≤ lengthBound)
    (hactive : idealLogLength Z
      (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) ≤ lengthBound) :
    G.retainedLength + G.enlargement ≤
      4 * lengthBound + G.supportError + 2 * step := by
  have h := G.retained_plus_enlargement_le_original hZ
  have hc := idealLogLength_nonneg Z hZ G.ideals.first.val
    (nonZeroDivisors.coe_ne_zero _)
  have hp : G.tag.padding step ≤ 2 * step := by
    cases G.tag <;> simp only [OriginalNominalTag.padding] <;> linarith
  unfold OriginalNominalIdeals.firstFrequency at h
  linarith

end OriginalNominalGeometry

namespace CanonicalOriginalTerminalPowers

/-- This bound is fixed before any source or Fourier variable. -/
def tailDegree (k : ℕ) (totalBound coarseBound frozenBound radiusBound : ℝ) : ℝ :=
  2 * coarseBound * ((k + 1 : ℕ) : ℝ) + totalBound + 2 * frozenBound + 4 +
    max (2 * coarseBound) radiusBound

/-- The full Cartesian tail pays a coarse product bound and the
original inverse column norm. Only raw numerical lengths enter. -/
theorem secondTailExponent_le_tailDegree
    (k : ℕ) (total coarse frozen common loss δ inverseRadius
      totalBound coarseBound frozenBound radiusBound : ℝ)
    (htotalNonneg : 0 ≤ total) (htotal : total ≤ totalBound)
    (hcoarse : coarse ≤ coarseBound) (hfrozen : frozen ≤ frozenBound)
    (hcommon : 0 ≤ common) (hloss : loss ≤ 1)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hradius : inverseRadius ≤ radiusBound) :
    secondTailExponent k (2 * coarse)
      (((total + loss - common) - total) + 2 * (total + loss - common) * δ -
        2 * (total - loss - frozen)) 0 inverseRadius ≤
      tailDegree k totalBound coarseBound frozenBound radiusBound := by
  have hbound : 0 ≤ totalBound := htotalNonneg.trans htotal
  have htilt : 2 * (total + loss - common) * δ ≤ totalBound + 1 := by
    have h := mul_le_mul_of_nonneg_right
      (show 2 * (total + loss - common) ≤ 2 * (totalBound + 1) by linarith) hδ
    nlinarith
  have hprofile : ((total + loss - common) - total) +
      2 * (total + loss - common) * δ - 2 * (total - loss - frozen) ≤
        totalBound + 2 * frozenBound + 4 := by linarith
  have hprod : 2 * coarse * ((k + 1 : ℕ) : ℝ) ≤
      2 * coarseBound * ((k + 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hmax : max (2 * coarse) inverseRadius ≤ max (2 * coarseBound) radiusBound :=
    max_le_max (by linarith) hradius
  unfold secondTailExponent tailDegree
  linarith

/-- The all-zero coefficient branch uses this same nonnegative
product exponent; no activity assumption is needed for the box bound. -/
theorem zeroProductExponent_le
    (total frozen loss lengthBound : ℝ) (hbound : 0 ≤ lengthBound)
    (htotal : total ≤ lengthBound) (hfrozen : 0 ≤ frozen) (hloss : loss ≤ 1) :
    2 * max 0 (total + loss - frozen) ≤ 2 * (lengthBound + 1) := by
  have hmax : max 0 (total + loss - frozen) ≤ lengthBound + 1 :=
    max_le (by linarith) (by linarith)
  linarith

end CanonicalOriginalTerminalPowers

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.sharp_zero_allowance_ledger_for_total
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.tail_allowance_ledger_for_total
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.canonical_inverse_radius
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.inverse_radius_exponent_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalTerminalPowers.secondTailExponent_le_tailDegree
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalTerminalPowers.zeroProductExponent_le
