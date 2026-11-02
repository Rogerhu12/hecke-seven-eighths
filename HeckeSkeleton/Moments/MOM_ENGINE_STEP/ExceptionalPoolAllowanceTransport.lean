import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalPoolAllowanceTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifiedExceptionalMass

set_option linter.unusedSectionVars false

/-!
# The exceptional source keeps the same original pool allowance

The main length and actual valuation 1/6/7 moving-prime length are
already part of the amplified exceptional index.  These exact
identities absorb them once, before its proved finite harmonic sum.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree CommonSupportMass LocalFiniteSums

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

namespace AmplifiedCommonIndex

variable (P : PowerScaleExteriorPool A bad Z ell eps) (M B : ℝ)
variable (main : TwoDivisorCommonBranch (K := K))
variable (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))

def dyadWeight (lower : ℝ) : AmplifiedCommonIndex P main error → ℝ
  | .inl j => main.exceptionalDyadWeight Z lower j
  | .inr j => (error j.1.val j.2.1.val).exceptionalDyadWeight Z lower j.2.2

theorem dyadWeight_nonneg (hZ : 0 ≤ Z) (lower : ℝ)
    (i : AmplifiedCommonIndex P main error) : 0 ≤ dyadWeight P main error lower i := by
  sorry

theorem originalTagWeight_mul_dyad (hZ : 1 < Z) (lower : ℝ)
    (i : AmplifiedCommonIndex P main error) :
    originalTagWeight P M B main error i *
        Z ^ movingLength P main error i * dyadWeight P main error lower i =
      amplifiedExceptionalDyadWeight P M B main error lower i := by
  sorry

theorem originalTagWeight_mul_remaining_dyad (hZ : 1 < Z) (lower δ : ℝ)
    (i : AmplifiedCommonIndex P main error) :
    originalTagWeight P M B main error i *
        Z ^ (δ + movingLength P main error i) * dyadWeight P main error lower i =
      Z ^ δ * amplifiedExceptionalDyadWeight P M B main error lower i := by
  sorry

/-- Internal numerical transport after the original atom estimate.
The only retained exponent is its true small numerical remainder. -/
theorem exceptional_pointwise_of_original_tag
    (hZ : 1 < Z) (hell : 0 < ell) (hM : 0 ≤ M)
    (hdensity : 0 ≤ P.rowDensity M B)
    (i : AmplifiedCommonIndex P main error)
    (actual C control remaining δ lower : ℝ) (hC : 0 ≤ C) (hcontrol : 0 ≤ control)
    (hremaining : remaining ≤ δ + movingLength P main error i)
    (hraw : actual ≤ C * control * originalTagWeight P M B main error i *
      Z ^ remaining * dyadWeight P main error lower i) :
    actual ≤ C * control * Z ^ δ *
      amplifiedExceptionalDyadWeight P M B main error lower i := by
  sorry

end AmplifiedCommonIndex
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.AmplifiedCommonIndex.originalTagWeight_mul_remaining_dyad
#print axioms HeckeSkeleton.Moments.EngineStep.AmplifiedCommonIndex.exceptional_pointwise_of_original_tag
