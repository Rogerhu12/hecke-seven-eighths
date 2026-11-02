import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstRowGeometry

set_option linter.unusedSectionVars false

/-!
# The sharp second-zero exponent on every original source tag

The original first profile contains a positive degree which must be
combined with the actual second numerator. After that cancellation the
only principal excess is the padded parent core and the enlargement.
The main tag pays its original pool length once. Direct and valuation
error tags pay no fictitious density. The resulting bound is uniform
in all three tag kinds and all slot counts.
-/

noncomputable section
open scoped Classical NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

namespace OriginalNominalTag

/-- Every actual error removes at least its moving radical length. -/
theorem movingLength_le_twice_removedLength
    (tag : OriginalNominalTag K) (Z : ℝ) (hZ : 1 < Z) :
    tag.movingLength Z ≤ 2 * tag.removedLength Z := by
  sorry

/-- The main enlargement is `2*step`, and its one pool length is
`step/3`. The other actual tags have enlargement padding `step`. -/
theorem padding_sub_poolLength_le
    (tag : OriginalNominalTag K) (step : ℝ) (hstep : 0 ≤ step) :
    tag.padding step - tag.poolLength step ≤ 5 * step / 3 := by
  sorry

end OriginalNominalTag

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

/-- The actual retained endpoint and its positive enlargement have a
uniform bound even when the un-enlarged nominal frequency is negative. -/
theorem retained_plus_enlargement_le_original
    (hZ : 1 < Z) :
    G.retainedLength + G.enlargement ≤
      G.ideals.firstFrequency a Z + idealLogLength Z G.ideals.opposite.val +
        G.supportError + G.tag.padding step := by
  sorry

/-- The original first row profile relative to its original allowance.
The large positive total degree is deliberately retained here. -/
def firstProfileShift (δ : ℝ) : ℝ :=
  (a.n₁ + a.n₂ + a.z) - a.q - idealLogLength Z G.ideals.complementary.val -
    idealLogLength Z (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) +
      δ * (idealLogLength Z G.ideals.complementary.val +
        idealLogLength Z (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) - a.m)

/-- This is the exponent produced by the sharp actual numerator,
one uncancelled inverse norm, the exact square count, and row radius.
The main pool charge is separated before summing its original tags. -/
def sharpZeroExponent (loss δ : ℝ) : ℝ :=
  -(a.n₁ + a.n₂ + a.z) +
    2 * ((a.n₁ + a.n₂ + a.z) + loss - idealLogLength Z G.ideals.first.val) * δ +
      (G.retainedLength + G.enlargement) + 2 * loss - G.tag.poolLength step

/-- Combine the two actual degrees before estimating the result.
Only original length bounds and small numerical powers enter. -/
theorem sharp_zero_allowance_ledger
    (hZ : 1 < Z) (hstep : 0 ≤ step)
    (loss δ ε productExponent lengthBound padding : ℝ)
    (hm : 0 ≤ a.m) (hloss : loss ≤ 1) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
    (hmask : idealLogLength Z G.ideals.complementary.val ≤ lengthBound)
    (hactive : idealLogLength Z
      (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) ≤ lengthBound)
    (hproduct : productExponent ≤ 2 * (lengthBound + 1))
    (hcore : a.n₁ + a.n₂ + a.z ≤ a.m + a.q + padding) :
    G.sharpZeroExponent loss δ + productExponent * ε ≤
      ((a.n₁ + a.n₂ + a.z) - idealLogLength Z G.ideals.first.val + G.boundary) +
        (padding + 5 * step / 3 + G.supportError + 2 * loss +
          (4 * lengthBound + 2) * δ + 2 * (lengthBound + 1) * ε) -
            G.firstProfileShift δ := by
  sorry

/-- The coarse tail has already placed its original numerator power
in the fixed cutoff degree. A fixed saving pays the first allowance
without introducing any extra power of a moving common ideal. -/
theorem tail_allowance_ledger
    (δ lengthBound loss saving : ℝ)
    (hm : 0 ≤ a.m) (hq : 0 ≤ a.q) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hmaskNonneg : 0 ≤ idealLogLength Z G.ideals.complementary.val)
    (hactiveNonneg : 0 ≤ idealLogLength Z
      (firstActiveRadical G.ideals.first.val G.ideals.opposite.val))
    (hfirst : idealLogLength Z G.ideals.first.val ≤ lengthBound)
    (hmask : idealLogLength Z G.ideals.complementary.val ≤ lengthBound)
    (hactive : idealLogLength Z
      (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) ≤ lengthBound)
    (hloss : 0 ≤ loss) (hsaving : 2 * lengthBound ≤ saving) :
    -saving ≤
      ((a.n₁ + a.n₂ + a.z) - idealLogLength Z G.ideals.first.val + G.boundary) +
        loss - G.firstProfileShift δ := by
  sorry

end OriginalNominalGeometry
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalTag.padding_sub_poolLength_le
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.retained_plus_enlargement_le_original
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.sharp_zero_allowance_ledger
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.tail_allowance_ledger
