import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralMassProfilePower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralKernelConstants

set_option linter.unusedSectionVars false

/-!
# Uniform payment of the literal mass coefficient

The same actual kernel theorem leaves an explicit coefficient in front
of its arithmetic sum. This file pays that coefficient: both complete
pre-removal profile counts, the original first scalar pair, all second
common and frozen atoms, and the two original Fourier seminorms.

The contour, constant and natural profile degree are selected before
the scale, source, label and original control values. Only individual
original profile and single-character height windows are inputs. No
kernel mass or terminal estimate is assumed here.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralUniformMassCoefficient

open NumberField DedekindZetaZeroFree HeckeGeneral.Characters
open CanonicalLiteralFirstScalarCost

variable (K : Type) [Field K] [NumberField K]
variable (A : SArithmeticData K) (σ : K →+* ℂ) (ω ψ : HeckeCharacter K)

/-- The height exponent pays the original single-prime factor on both
complete pre-removal profile lists. All other degrees are the exact
separate original-profile charges. -/
def degree (cap d dRow dFirstKernel dSecondKernel heightDegree : ℕ) : ℕ :=
  heightDegree * ((cap + 2) + (cap + 2)) +
    CanonicalLiteralMassProfilePower.degree cap d dRow dFirstKernel dSecondKernel

/-- A single original control may dominate both `1 + T` and the
individual original profile values. The chosen contour and constant
do not depend on any of those moving values. -/
theorem exists_uniform_coefficient
    (cap d dRow dFirstKernel dSecondKernel heightDegree : ℕ)
    (annulus lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (hannulus : 0 ≤ annulus) (δ₁ δ₂ : ℝ) (orders : Finset (ℕ × ℕ))
    (ε mesh heightConstant widthBound : ℝ) (hε : 0 < ε) (hwidth : 0 ≤ widthBound) :
    ∃ δ Cmass : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ 0 < Cmass ∧
      ∀ Z T width height control originalBound row firstKernel secondKernel : ℝ,
        1 ≤ Z → 0 ≤ T → width ≤ widthBound →
        height ≤ heightConstant * (1 + Real.log Z) * (1 + T) ^ heightDegree →
        1 + T ≤ control →
        0 ≤ originalBound → originalBound ≤ control ^ d →
        0 ≤ row → row ≤ control ^ dRow →
        0 ≤ firstKernel → firstKernel ≤ control ^ dFirstKernel →
        0 ≤ secondKernel → secondKernel ≤ control ^ dSecondKernel →
        CanonicalLiteralKernelConstants.constant K A σ ω ψ cap (orders.sup Prod.snd) *
          (2 * CanonicalFullKappaPrime.radiusFactor K Z δ mesh
            (CanonicalHeckePrimeAnalytic.degreeBound K) height
            (CompleteMovingRowRecipe.primeMaskLogBound A Z width)) ^
              ((cap + 2) + (cap + 2)) *
          ((1 + CanonicalLiteralActiveRadius.twoSignsCoefficient
              originalBound lo hi hlo δ₁ δ₂ orders) ^ ((cap + 2) + (cap + 2)) *
            (atomBudget annulus originalBound ^ cap *
              CanonicalLiteralMassProfilePower.slotBudget originalBound ^ (2 * cap))) *
          row * firstKernel * secondKernel ≤
            Cmass * control ^ degree cap d dRow dFirstKernel dSecondKernel heightDegree *
              Z ^ ε := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralUniformMassCoefficient

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralUniformMassCoefficient.exists_uniform_coefficient
