import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCapacityLengths
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthRootSupportBudget

set_option linter.unusedSectionVars false

/-!
# The raw literal width from the original second common ideal

The full sixth root divides each actual second common ideal. Its
logarithmic cost is paid by that original norm window, independently
of the physical cutoff. The nominal enlargement already gives the
original width drop before this explicit root cost is added.
-/

noncomputable section
open scoped Classical NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complete minimum multiplicities are retained in the root.
No squarefree reduction or lower bound on a physical row is used. -/
theorem literalSixthRootLength_le_common (Z : ℝ) (hZ : 1 < Z)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    idealLogLength Z (secondSixthRootIdeal p m n).val ≤
        idealLogLength Z (primePowerProduct p m).val ∧
      idealLogLength Z (secondSixthRootIdeal p m n).val ≤
        idealLogLength Z (primePowerProduct p n).val := by
  sorry

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

/-- The original tag's enlargement and its actual unit divisor imply
the nominal width drop directly, before either capacity choice. -/
theorem literalNominalWidth_le_parent (hZ : 1 < Z) (hstep : 0 ≤ step) :
    G.skeleton.nominalWidth ≤ a.m + a.q - step := by
  sorry

private theorem literalRawWidth_le_of_root (hZ : 1 < Z) (hstep : 0 ≤ step)
    (cutoff rootLength secondBox : ℝ) (hroot : rootLength ≤ secondBox) :
    G.literalRowParameter cutoff + G.literalSupportParameter rootLength ≤
      a.m + a.q - step + secondBox + cutoff := by
  sorry

/-- A genuine second common ideal supplies the entire root cost.
The input is its original norm window, rather than a raw-width bound. -/
theorem literalRawWidth_le_second_box (hZ : 1 < Z) (hstep : 0 ≤ step)
    (cutoff secondBox : ℝ) (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (hsecond : (primePowerProduct p m).val = G.ideals.second.val)
    (hN : (Ideal.absNorm G.ideals.second.val : ℝ) ≤ Z ^ secondBox) :
    G.literalRowParameter cutoff +
        G.literalSupportParameter (idealLogLength Z (secondSixthRootIdeal p m n).val) ≤
      a.m + a.q + secondBox + cutoff := by
  sorry

/-- The reversed source uses the same root and its own actual second
ideal. The left and right common ideals need not be equal. -/
theorem literalRawWidth_le_second_box_right (hZ : 1 < Z) (hstep : 0 ≤ step)
    (cutoff secondBox : ℝ) (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (hsecond : (primePowerProduct p n).val = G.ideals.second.val)
    (hN : (Ideal.absNorm G.ideals.second.val : ℝ) ≤ Z ^ secondBox) :
    G.literalRowParameter cutoff +
        G.literalSupportParameter (idealLogLength Z (secondSixthRootIdeal p m n).val) ≤
      a.m + a.q + secondBox + cutoff := by
  sorry

end OriginalNominalGeometry
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.literalSixthRootLength_le_common
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.literalNominalWidth_le_parent
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.literalRawWidth_le_second_box
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.literalRawWidth_le_second_box_right
