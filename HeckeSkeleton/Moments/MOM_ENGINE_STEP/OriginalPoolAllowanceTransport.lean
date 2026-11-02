import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalAmplifiedCarrier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonMass

set_option linter.unusedSectionVars false

/-!
# The original pool pays its actual moving-support exponent

A main label retains its original pool length. An error label retains
the moving multiplicity of its actual prime, which is one at valuations
1 and 7 and zero at valuation 6. These powers already occur in the
proved amplified arithmetic index; they must not be charged again to
the small remaining exponent.

All equalities use the same original density, prime tag and harmonic
label. No estimate or second pool average is introduced.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

theorem rpow_amplifier_moving_length (hZ : 1 < Z)
    (p : ExteriorPrime A) (n : ℕ) :
    Z ^ ((amplifierMovingExponent n : ℝ) * idealLogLength Z p.val.asIdeal) =
      Q p ^ amplifierMovingExponent n := by
  sorry

namespace AmplifiedCommonIndex

variable (P : PowerScaleExteriorPool A bad Z ell eps) (M B : ℝ)
variable (main : TwoDivisorCommonBranch (K := K))
variable (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))

/-- The scalar already attached to the original main or error source,
before its moving-support power is included. -/
def originalTagWeight : AmplifiedCommonIndex P main error → ℝ
  | .inl _ => (4 / P.rowDensity M B) * ((M + 6 * ell) / (ell / 2))
  | .inr j => (4 / P.rowDensity M B) *
      FirstGaussPoolData.localErrorWeight j.2.1.val j.1.val

/-- The literal length paid by this original tag. -/
def movingLength : AmplifiedCommonIndex P main error → ℝ
  | .inl _ => ell
  | .inr j =>
      (amplifierMovingExponent j.1.val : ℝ) * idealLogLength Z j.2.1.val.val.asIdeal

/-- Both genuine common supports and the independent second divisor
remain inside the same original harmonic weight. -/
def harmonicWeight : AmplifiedCommonIndex P main error → ℝ
  | .inl j => main.indexWeight j
  | .inr j => (error j.1.val j.2.1.val).indexWeight j.2.2

theorem originalTagWeight_nonneg (hell : 0 < ell) (hM : 0 ≤ M)
    (hdensity : 0 ≤ P.rowDensity M B) (i : AmplifiedCommonIndex P main error) :
    0 ≤ originalTagWeight P M B main error i := by
  sorry

theorem harmonicWeight_nonneg (i : AmplifiedCommonIndex P main error) :
    0 ≤ harmonicWeight P main error i := by
  sorry

/-- The main pool power and error moving norm are precisely the powers
already present in amplifiedIndexWeight. -/
theorem originalTagWeight_mul_rpow (hZ : 1 < Z)
    (i : AmplifiedCommonIndex P main error) :
    originalTagWeight P M B main error i *
        Z ^ movingLength P main error i * harmonicWeight P main error i =
      amplifiedIndexWeight P M B main error i := by
  sorry

/-- Only the small original error remains outside the actual index. -/
theorem originalTagWeight_mul_remaining (hZ : 1 < Z) (δ : ℝ)
    (i : AmplifiedCommonIndex P main error) :
    originalTagWeight P M B main error i *
        Z ^ (δ + movingLength P main error i) * harmonicWeight P main error i =
      Z ^ δ * amplifiedIndexWeight P M B main error i := by
  sorry

/-- A bound on the original per-label scalar can now be read by the
uniform amplified-index mass theorem with no additional prime count. -/
theorem pointwise_of_original_tag
    (hZ : 1 < Z) (hell : 0 < ell) (hM : 0 ≤ M)
    (hdensity : 0 ≤ P.rowDensity M B)
    (i : AmplifiedCommonIndex P main error)
    (actual C control remaining δ : ℝ) (hC : 0 ≤ C) (hcontrol : 0 ≤ control)
    (hremaining : remaining ≤ δ + movingLength P main error i)
    (hraw : actual ≤ C * control * originalTagWeight P M B main error i *
      Z ^ remaining * harmonicWeight P main error i) :
    actual ≤ C * control * Z ^ δ * amplifiedIndexWeight P M B main error i := by
  sorry

end AmplifiedCommonIndex
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.rpow_amplifier_moving_length
#print axioms HeckeSkeleton.Moments.EngineStep.AmplifiedCommonIndex.originalTagWeight_mul_remaining
#print axioms HeckeSkeleton.Moments.EngineStep.AmplifiedCommonIndex.pointwise_of_original_tag

